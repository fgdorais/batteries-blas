/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Term
public import BLAS.Ops

/-!
# The `blas!` notation

The root module `BLAS` doesn't import this one, because it makes `blas!` a keyword and `ᵀ` a
postfix operator (as Mathlib does for its matrices).

`blas! y := e` updates `y` by a single routine, chosen from the form of `e` and the kinds of its
operands. In a `do` block it reassigns the mutable variable `y`, and as a term, `blas!(y := e)` is
the new value of `y`. `blas! y += e` is `blas! y := e + y`.

| Update                       | Expansion                     | Routine                    |
|------------------------------|-------------------------------|----------------------------|
| `y := α • A * x + β • y`     | `MulAdd.run α A x β y`        | `gemv`, `gemvT` or `gemm`  |
| `y := α • x + y`             | `Axpy.run α x y`              | `axpy`                     |
| `x := α • x`                 | `Scal.run α x`                | `scal`                     |
| `y := x`                     | `Copy.run x y`                | `copy`                     |
| `x := T⁻¹ * x`               | `Solve.run T x`               | `trsv`, or `trsm` (`α = 1`) |
| `B := α • T⁻¹ * B`           | `ScaledSolve.run α T B`       | `trsm`                     |
| `B := α • B * T⁻¹`           | `SolveRight.run α B T`        | `trsmRight`                |

The routine of `MulAdd` follows from the kinds of `A` and `x`: a matrix and a vector is `gemv`, a
transpose `Aᵀ` and a vector `gemvT`, and two matrices `gemm`. A missing `α` is `1`, a missing
`β • y` is `β = 0`, which sets `y` to `0` without reading it, as in the reference BLAS, and a bare
`y` is `β = 1`. The summands may come in any order, and `α • (A * x)` is `α • A * x`.

An update that no single routine computes is an error at compile time, never a combination of
routines: `α • x + β • y` (no `axpby` in the reference BLAS), `A * B * x`, `y := α • x` (a copy
and a scaling), or `Aᵀ * B` (no instance of `MulAdd`, since the library has no transposed
`gemm`). So the expansion is always one call, with the speed and the specification of its routine.
-/

namespace BLAS.Notation

open Lean

/-- `Aᵀ` is the transpose of `A`, with no copy. -/
scoped postfix:max "ᵀ" => BLAS.Transpose.mk

/-- `A[:, j]` is column `j` of the matrix `A`, as a vector, with no copy. -/
scoped syntax:max term noWs "[" ":" ", " term "]" : term

/-- `A[i, :]` is row `i` of the matrix `A`, as a vector, with no copy. -/
scoped syntax:max term noWs "[" term ", " ":" "]" : term

macro_rules
  | `($A[:, $j]) => `(($A).col $j (by get_elem_tactic))
  | `($A[$i, :]) => `(($A).row $i (by get_elem_tactic))

/-- A summand of the right side of a `blas!` update, with its optional scalar. -/
private inductive Summand where
  /-- `α • a * x`. -/
  | prod (c : Option Term) (a x : Term)
  /-- `α • x`. -/
  | plain (c : Option Term) (x : Term)
  deriving Inhabited

/-- The operators that `blas!` doesn't take in an operand, rather than reading them as a term. -/
private meta def opKinds : List SyntaxNodeKind :=
  [``«term_-_», ``«term-_», ``«term_/_», ``«term_^_», ``«term_+_», ``«term_*_», ``«term_•_»]

/-- Removes the parentheses around a term. -/
private meta partial def unparen : Term → Term
  | `(($t)) => unparen t
  | t => t

/-- The summands of `e`, from the left. -/
private meta partial def summands (e : Term) : Array Term :=
  match unparen e with
  | `($a + $b) => summands a ++ summands b
  | t => #[t]

/-- Checks that `t` is an operand, not an arithmetic expression that `blas!` doesn't handle. -/
private meta def operand (t : Term) : MacroM Term := do
  let t := unparen t
  if opKinds.contains t.raw.getKind then
    Macro.throwErrorAt t "blas!: no single BLAS routine computes this operand; \
      write it with a separate update first"
  return t

/-- Classifies a summand of the right side of a `blas!` update. -/
private meta partial def classify (t : Term) : MacroM Summand := do
  match unparen t with
  | `($c • $u) =>
    match ← classify u with
    | .prod none a x => return .prod (some c) a x
    | .plain none x => return .plain (some c) x
    | _ => Macro.throwErrorAt t "blas!: a summand has at most one scalar"
  | `($a * $b) =>
    match ← classify a, ← classify b with
    | .plain c a, .plain none x => return .prod c (← operand a) (← operand x)
    | .plain _ _, .plain (some _) _ =>
      Macro.throwErrorAt t "blas!: write the scalar first, as in `α • A * x`"
    | _, _ => Macro.throwErrorAt t "blas!: no single BLAS routine computes a product of three \
        factors"
  | u => return .plain none (← operand u)

/-- Whether `t` is the target `y` of the update. -/
private meta def isTarget (y : Ident) (t : Term) : Bool :=
  t.raw.isIdent && t.raw.getId == y.getId

/-- The routine call of the update `y := e`. -/
private meta def expand (y : Ident) (e : Term) : MacroM Term := do
  let mut target : Option (Option Term) := none
  let mut others : Array Summand := #[]
  for t in summands e do
    let s ← classify t
    match s with
    | .plain c x =>
      if isTarget y x then
        if target.isSome then
          Macro.throwErrorAt t s!"blas!: `{y.getId}` occurs twice; combine its scalars"
        target := some c
      else others := others.push s
    | .prod .. => others := others.push s
  let fail {α} : MacroM α := Macro.throwErrorAt e
    s!"blas!: no single BLAS routine computes this update of `{y.getId}`"
  match others, target with
  -- `y := α • A * x + β • y`, or the solves.
  | #[.prod c a x], tgt =>
    match unparen a, unparen x with
    | `($t⁻¹), x =>
      unless isTarget y x && tgt.isNone do fail
      match c with
      | none => `(BLAS.Solve.run $t $y)
      | some c => `(BLAS.ScaledSolve.run $c $t $y)
    | b, `($t⁻¹) =>
      unless isTarget y b && tgt.isNone do fail
      `(BLAS.SolveRight.run $(c.getD (← `(1))) $y $t)
    | a, x =>
      let α ← c.getDM `(1)
      let β ← match tgt with
        | none => `(0)
        | some none => `(1)
        | some (some β) => pure β
      `(BLAS.MulAdd.run $α $a $x $β $y)
  -- `y := α • x + y`.
  | #[.plain c x], some none => `(BLAS.Axpy.run $(← c.getDM `(1)) $x $y)
  -- `y := x`.
  | #[.plain none x], none => `(BLAS.Copy.run $x $y)
  -- `x := α • x`.
  | #[], some (some c) => `(BLAS.Scal.run $c $y)
  | _, _ => fail

/-- `blas!(y := e)` is the new value of `y` after the update `y := e` by a single routine. -/
scoped syntax (name := blasTerm) "blas!(" ident " := " term ")" : term

/-- `blas!(y += e)` is `blas!(y := e + y)`. -/
scoped syntax (name := blasAddTerm) "blas!(" ident " += " term ")" : term

/-- `blas! y := e` updates the mutable variable `y` by a single routine. -/
scoped syntax (name := blasDo) "blas! " ident " := " term : doElem

/-- `blas! y += e` is `blas! y := e + y`. -/
scoped syntax (name := blasAddDo) "blas! " ident " += " term : doElem

macro_rules
  | `(blas!($y := $e)) => expand y e
  | `(blas!($y += $e)) => do expand y (← `($e + $y))

macro_rules
  | `(doElem| blas! $y:ident := $e) => `(doElem| $y:ident := blas!($y := $e))
  | `(doElem| blas! $y:ident += $e) => `(doElem| $y:ident := blas!($y += $e))

end BLAS.Notation
