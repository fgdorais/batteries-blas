/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Term
public import BLAS.Ops

/-!
# The `blas%` notation

The root module `BLAS` doesn't import this one, because it makes `blas%` a keyword. Outside of
`blas%` it adds nothing else: the right side of an update is in its own syntax category, so `ᵀ` and
`A[:, j]` mean something only there, and `•` and `*` have the precedence of the formula.

`blas% y := e` updates `y` by a single routine, chosen from the form of `e` and the kinds of its
operands. In a `do` block it reassigns the mutable variable `y`, and as a term, `blas%(y := e)` is
the new value of `y`. `blas% y += e` is `blas% y := y + e`, and `blas% y -= e` is
`blas% y := y - e`.

| Update                       | Expansion                     | Routine                    |
|------------------------------|-------------------------------|----------------------------|
| `y := α • A * x + β • y`     | `MulAdd.run α A x β y`        | `gemv`, `gemvT`, `gemm`, … |
| `y := α • x + y`             | `Axpy.run α x y`              | `axpy`                     |
| `y := α • x + β • y`         | `Axpby.run α x β y`           | `axpby`                    |
| `y := α • x`                 | `Axpby.run α x 0 y`           | `axpby`                    |
| `x := α • x`                 | `Scal.run α x`                | `scal`                     |
| `y := x`                     | `Copy.run x y`                | `copy`                     |
| `x := T⁻¹ * x`               | `Solve.run T x`               | `trsv`, or `trsm` (`α = 1`) |
| `B := α • T⁻¹ * B`           | `ScaledSolve.run α T B`       | `trsm`                     |
| `B := α • B * T⁻¹`           | `SolveRight.run α B T`        | `trsmRight`                |

The routine of `MulAdd` follows from the kinds of `A` and `x`: a matrix and a vector is `gemv`, a
transpose `Aᵀ` and a vector `gemvT`, two matrices `gemm`, and transposes `gemmTN` (`Aᵀ * B`),
`gemmNT` (`A * Bᵀ`) and `gemmTT` (`Aᵀ * Bᵀ`). A missing `α` is `1`, a missing
`β • y` is `β = 0`, which sets `y` to `0` without reading it, as in the reference BLAS, and a bare
`y` is `β = 1`. The summands may come in any order, and a subtracted summand `- α • …` has the
scalar `-α` (`-1` if it has none). Floating-point negation is exact, and `a - b` is `a + (-b)`, so
`y := A * x - y` is `gemv 1 A x (-1) y` and `y -= α • x` is `axpy (-α) x y`, to the bit.

## Grammar

The right side is a sum of summands `s • f * g`, which may be subtracted, as in `- f + g - h`,
with an optional scalar `s` and one or two factors `f` and `g`. The `•` ends the scalar, so the
scalar is a product or quotient of terms, as in `2 * a • A * x` or `-α / 2 • x`, with no
parentheses: only a scalar sum or difference needs them, `(a - b) • x`, as `+` and `-` separate the
summands. A scalar term and a factor are Lean terms above the
precedence of `*`, such as `α`, `-α`, `f a`, `x.dot y` or `A.lower⁻¹`. A factor can also be a
transpose `Aᵀ`, a column `A[:, j]` or a row `A[i, :]` of a matrix `A`, as vectors with no copy.

An update that no single routine computes is an error at compile time, never a combination of
routines: `A * B * x` (two products), `y := A * x + z` with `z` not the target, or a product of
operands of sizes that don't match (no instance of `MulAdd`). So the expansion is always one call,
with the speed and the specification of its routine.
-/

namespace BLAS.Notation

open Lean

/-- A factor of a summand of a `blas%` update: a matrix, a vector, or a view of one. -/
declare_syntax_cat blasFactor

/-- A factor is a term above the precedence of `*`, such as `A`, `A.lower⁻¹` or `f x`. -/
syntax term:75 : blasFactor

/-- `Aᵀ` is the transpose of `A`, with no copy. -/
syntax (name := blasTranspose) term:max noWs "ᵀ" : blasFactor

/-- `A[:, j]` is column `j` of the matrix `A`, as a vector, with no copy. -/
syntax ident noWs "[" ":" ", " term "]" : blasFactor

/-- `A[i, :]` is row `i` of the matrix `A`, as a vector, with no copy. -/
syntax ident noWs "[" term ", " ":" "]" : blasFactor

/-- A scalar of a summand of a `blas%` update. -/
declare_syntax_cat blasScalar

/-- A scalar is a product or quotient of terms above the precedence of `*`. -/
syntax term:75 ((" * " <|> " / ") term:75)* : blasScalar

/-- A summand of a `blas%` update. -/
declare_syntax_cat blasSummand

/-- A summand `s • f * g`, with an optional scalar `s` and one or more factors. -/
syntax (atomic(blasScalar " • "))? blasFactor (" * " blasFactor)* : blasSummand

/-- The right side of a `blas%` update. -/
declare_syntax_cat blasSum

/-- The right side of a `blas%` update is a sum and difference of summands. -/
syntax ("-")? blasSummand ((" + " <|> " - ") blasSummand)* : blasSum

/-- A summand of the right side of a `blas%` update, with its optional scalar. -/
private inductive Summand where
  /-- `α • a * x`. -/
  | prod (c : Option Term) (a x : Term)
  /-- `α • x`. -/
  | plain (c : Option Term) (x : Term)
  deriving Inhabited

/-- The arithmetic that a parenthesized factor can't be, as no single routine computes it. -/
private meta def opKinds : List SyntaxNodeKind :=
  [``«term_-_», ``«term_/_», ``«term_+_», ``«term_*_», ``«term_•_»]

/-- Removes the parentheses around a term. -/
private meta partial def unparen : Term → Term
  | `(($t)) => unparen t
  | t => t

/-- The term of a scalar. -/
private meta def scalar (s : TSyntax `blasScalar) : MacroM Term := do
  let mut acc : Term := ⟨s.raw[0]⟩
  for p in s.raw[1].getArgs do
    let a : Term := ⟨p[1]⟩
    acc ← if (p[0].find? (·.isToken "/")).isSome then `($acc / $a) else `($acc * $a)
  return acc

/-- The term of a factor. -/
private meta def factor (f : TSyntax `blasFactor) : MacroM Term := do
  if f.raw.isOfKind ``blasTranspose then return ← `(BLAS.Transpose.mk $(⟨f.raw[0]⟩))
  match f with
  | `(blasFactor| $A:ident[:, $j]) => `(($A).col $j (by get_elem_tactic))
  | `(blasFactor| $A:ident[$i, :]) => `(($A).row $i (by get_elem_tactic))
  | `(blasFactor| $t:term) =>
    let t := unparen t
    if opKinds.contains t.raw.getKind then
      Macro.throwErrorAt t "blas%: no single BLAS routine computes this factor; \
        write it with a separate update first"
    return t
  | _ => Macro.throwUnsupported

/--
Classifies a summand of the right side of a `blas%` update, negated if `neg`: its scalar `α`
becomes `-α`, and a missing one `-1`. Negation is exact, so `y - α • x` is `y + (-α) • x` to the
bit.
-/
private meta def classify (s : TSyntax `blasSummand) (neg : Bool) : MacroM Summand := do
  match s with
  | `(blasSummand| $[$c:blasScalar •]? $f:blasFactor $[* $gs:blasFactor]*) =>
    let c ← c.mapM scalar
    let c ← if neg then some <$> (match c with | some c => `(-$c) | none => `(-1)) else pure c
    match gs with
    | #[] => return .plain c (← factor f)
    | #[g] => return .prod c (← factor f) (← factor g)
    | _ => Macro.throwErrorAt s "blas%: no single BLAS routine computes a product of three \
        factors"
  | _ => Macro.throwUnsupported

/-- Whether `t` is the target `y` of the update. -/
private meta def isTarget (y : Ident) (t : Term) : Bool :=
  t.raw.isIdent && t.raw.getId == y.getId

/-- The summands of the right side of a `blas%` update, with whether each one is subtracted. -/
private meta def summands (e : TSyntax `blasSum) : Array (Bool × TSyntax `blasSummand) := Id.run do
  let mut out := #[(!e.raw[0].isNone, ⟨e.raw[1]⟩)]
  for p in e.raw[2].getArgs do
    out := out.push ((p[0].find? (·.isToken "-")).isSome, ⟨p[1]⟩)
  return out

/--
The routine call of the update `y := e`, and of `y += e` if `add`, or `y -= e` if also `sub`.
-/
private meta def expand (y : Ident) (e : TSyntax `blasSum) (add sub : Bool) : MacroM Term := do
  let mut target : Option (Option Term) := if add then some none else none
  let mut others : Array Summand := #[]
  for (neg, t) in summands e do
    let s ← classify t (neg != sub)
    match s with
    | .plain c x =>
      if isTarget y x then
        if target.isSome then
          Macro.throwErrorAt t s!"blas%: `{y.getId}` occurs twice; combine its scalars"
        target := some c
      else others := others.push s
    | .prod .. => others := others.push s
  let fail {α} : MacroM α := Macro.throwErrorAt e
    s!"blas%: no single BLAS routine computes this update of `{y.getId}`"
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
  -- `y := α • x + β • y`.
  | #[.plain c x], some (some β) => `(BLAS.Axpby.run $(← c.getDM `(1)) $x $β $y)
  -- `y := α • x`, which sets `y` to `α * x` without reading it.
  | #[.plain (some c) x], none => `(BLAS.Axpby.run $c $x 0 $y)
  -- `y := x`.
  | #[.plain none x], none => `(BLAS.Copy.run $x $y)
  -- `x := α • x`.
  | #[], some (some c) => `(BLAS.Scal.run $c $y)
  | _, _ => fail

/-- `blas%(y := e)` is the new value of `y` after the update `y := e` by a single routine. -/
scoped syntax (name := blasTerm) "blas%(" ident " := " blasSum ")" : term

/-- `blas%(y += e)` is `blas%(y := e + y)`. -/
scoped syntax (name := blasAddTerm) "blas%(" ident " += " blasSum ")" : term

/-- `blas% y := e` updates the mutable variable `y` by a single routine. -/
scoped syntax (name := blasDo) "blas% " ident " := " blasSum : doElem

/-- `blas% y += e` is `blas% y := e + y`. -/
scoped syntax (name := blasAddDo) "blas% " ident " += " blasSum : doElem

/-- `blas%(y -= e)` is `blas%(y := y - e)`. -/
scoped syntax (name := blasSubTerm) "blas%(" ident " -= " blasSum ")" : term

/-- `blas% y -= e` is `blas% y := y - e`. -/
scoped syntax (name := blasSubDo) "blas% " ident " -= " blasSum : doElem

macro_rules
  | `(blas%($y := $e)) => expand y e false false
  | `(blas%($y += $e)) => expand y e true false
  | `(blas%($y -= $e)) => expand y e true true

macro_rules
  | `(doElem| blas% $y:ident := $e) => `(doElem| $y:ident := blas%($y := $e))
  | `(doElem| blas% $y:ident += $e) => `(doElem| $y:ident := blas%($y += $e))
  | `(doElem| blas% $y:ident -= $e) => `(doElem| $y:ident := blas%($y -= $e))

end BLAS.Notation
