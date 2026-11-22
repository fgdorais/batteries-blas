/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import BLASTest.Util
meta import BLAS
meta import BLASTest.Util

/-!
Tests for `gemv`, `gemvT`, `ger`, `trsv`, `trsvT`, `trmv`, `trmvT`, `symv`, `syr` and `syr2` on
`Float`.
-/

open BLAS.Float64

/--
The value of the elements outside the vectors and matrices of the tests, which no test computes.
-/
def mark : Float := 1e9 + 0.5

/-- An `m × n` matrix of small integers computed from the indices and the seed `s`. -/
def mat (m n : Nat) (s : Nat := 0) : Mat m n :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5

/-- A vector of small integers computed from the indices and the seed `s`. -/
def vec (n : Nat) (s : Nat := 0) : Vec n :=
  .ofFn fun i => ((i.val * 5 + s) % 9).toFloat - 4

/-- `mat m n s` at the offset `off` with the leading dimension `ld`, in an array of `mark`s. -/
def matLd (m n off ld : Nat) (s : Nat := 0) : Mat m n :=
  let a := ScalarArray.Float64Array.ofFn (n := off + ld * n) fun p =>
    let q := p.val - off
    if off ≤ p.val ∧ q % ld < m then ((q % ld * 7 + q / ld * 13 + s) % 11).toFloat - 5 else mark
  (Mat.ofLd? a off ld).getD (mat m n s)

/-- `vec n s` at the offset `off` with the stride `inc`, in an array of `mark`s. -/
def vecInc (n off inc : Nat) (s : Nat := 0) : Vec n :=
  let a := ScalarArray.Float64Array.ofFn (n := off + inc * n) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 then
      (((p.val - off) / inc * 5 + s) % 9).toFloat - 4
    else mark
  (Vec.ofStride? a off inc).getD (vec n s)

/-- The number of `mark`s in an array: the elements outside a vector or matrix of the tests. -/
def marks (a : ScalarArray.Float64Array) : Nat := a.toList.countP (· == mark)

/--
The address of the array of `x`, with `x`. It is not inlined, so the address is taken before `x`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-- `withAddr` for a matrix. -/
@[noinline] def withAddrMat (A : Mat m n) : USize × Mat m n := (BLASTest.addr A.data, A)

/-! ## `gemv` and `gemvT` -/

-- `[[1, 2], [3, 4]] * [1, 1] = [3, 7]`, and its transpose `[4, 6]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [1, 1]
  (Mat.gemv 1 A x 0 y).toList == [3, 7] && (Mat.gemv 2 A x 1 y).toList == [7, 15] &&
    (Mat.gemvT 1 A x 0 y).toList == [4, 6] && (Mat.gemvT 2 A x (-1) y).toList == [7, 11]

/-- The spec of `gemv`, on lists. -/
def gemvList (α : Float) (A : Mat m n) (x : Vec n) (β : Float) (y : Vec m) : List Float :=
  List.ofFn fun i : Fin m =>
    let v := if β == 0 then 0 else β * y[i.val]
    if n = 0 then y[i.val] else if α == 0 then v
    else (List.finRange n).foldl (fun s j => s + α * x[j.val] * A[(i.val, j.val)]) v

/-- The spec of `gemvT`, on lists. -/
def gemvTList (α : Float) (A : Mat m n) (x : Vec m) (β : Float) (y : Vec n) : List Float :=
  List.ofFn fun j : Fin n =>
    let v := if β == 0 then 0 else β * y[j.val]
    if m = 0 then y[j.val] else if α == 0 then v
    else v + α * (List.finRange m).foldl (fun s i => s + A[(i.val, j.val)] * x[i.val]) 0

/--
Whether `gemv` and `gemvT` match their specs, on packed operands and on operands with offsets,
strides and leading dimensions, and leave the rest of `y`'s array unchanged.
-/
def gemvMatches (m n : Nat) (α β : Float) : Bool :=
  let A := mat m n 1
  let A' := matLd m n 3 (m + 2) 1
  let ok₁ := (Mat.gemv α A (vec n 2) β (vec m 3)).toList == gemvList α A (vec n 2) β (vec m 3)
  let y := vecInc m 2 3 3
  let z := Mat.gemv α A' (vecInc n 1 2 2) β y
  let ok₂ := z.toList == gemvList α A (vec n 2) β (vec m 3) && marks z.data == marks y.data
  let ok₃ := (Mat.gemvT α A (vec m 2) β (vec n 3)).toList == gemvTList α A (vec m 2) β (vec n 3)
  let y := vecInc n 1 4 3
  let z := Mat.gemvT α A' (vecInc m 0 3 2) β y
  let ok₄ := z.toList == gemvTList α A (vec m 2) β (vec n 3) && marks z.data == marks y.data
  ok₁ && ok₂ && ok₃ && ok₄

#guard gemvMatches 5 4 1.5 0.5
#guard gemvMatches 1 1 2 3
#guard gemvMatches 17 9 (-0.25) 2
#guard gemvMatches 300 70 0.75 (-1)
#guard gemvMatches 0 3 1 1
#guard gemvMatches 3 0 1 2

#guard gemvMatches 5 4 0 0.5
#guard gemvMatches 5 4 1.5 0
#guard gemvMatches 5 4 0 0
#guard gemvMatches 0 3 1 0
#guard gemvMatches 3 0 1 0

-- As in the reference BLAS, `β = 0` sets `y` to `0` without reading it, so a `NaN` in `y` goes.
#guard (Mat.gemv 1 (mat 1 1) (vec 1) 0 (.ofList [0 / 0])).toList == [(mat 1 1)[(0, 0)] * (vec 1)[0]]
#guard (Mat.gemvT 1 (mat 1 1) (vec 1) 0 (.ofList [0 / 0])).toList ==
  [(mat 1 1)[(0, 0)] * (vec 1)[0]]

-- `α = 0` only scales `y`, without reading `A` or `x`.
#guard (Mat.gemv (m := 1) (n := 1) 0 (.ofFn fun _ _ => 0 / 0) (.ofList [1 / 0]) 2
  (.ofList [3])).toList == [6]
#guard (Mat.gemvT (m := 1) (n := 1) 0 (.ofFn fun _ _ => 0 / 0) (.ofList [1 / 0]) 2
  (.ofList [3])).toList == [6]

-- An empty sum returns `y`, unscaled.
#guard (Mat.gemv (m := 2) (n := 0) 1 (.ofFn fun _ _ => 0) (.ofList []) 2
  (.ofList [1, 0 / 0])).toList.head? == some 1
#guard (Mat.gemvT (m := 0) (n := 2) 1 (.ofFn fun _ _ => 0) (.ofList []) 2
  (.ofList [1, 3])).toList == [1, 3]

/-- Whether `gemv` and `gemvT` update an unshared `y` in place. -/
def gemvInPlace (m : Nat) : Bool :=
  let (p, y) := withAddr (vecInc m 1 2)
  let (q, y') := withAddr (vecInc m 1 2 5)
  BLASTest.addr (Mat.gemv 1 (mat m m 1) (vec m 2) 1 y).data == p &&
    BLASTest.addr (Mat.gemvT 1 (mat m m 1) (vec m 2) 1 y').data == q

#guard gemvInPlace 8

/-! ## `ger` -/

-- `[1, 2] * [3, 4]ᵀ`, in column-major order.
#guard (Mat.ger (m := 2) (n := 2) 1 (.ofList [1, 2]) (.ofList [3, 4])
  (.ofFn fun _ _ => 0)).toList == [3, 6, 4, 8]
#guard (Mat.ger (m := 2) (n := 2) 2 (.ofList [1, 2]) (.ofList [3, 4])
  (.ofFn fun _ _ => 1)).toList == [7, 13, 9, 17]

/-- The spec of `ger`, on lists. -/
def gerList (α : Float) (x : Vec m) (y : Vec n) (A : Mat m n) : List Float :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m =>
    if α == 0 || y[j.val] == 0 then A[(i.val, j.val)]
    else A[(i.val, j.val)] + x[i.val] * (α * y[j.val])).flatten

/-- Whether `ger` matches its spec, and leaves the rest of `A`'s array unchanged. -/
def gerMatches (m n : Nat) (α : Float) : Bool :=
  let ok₁ := (Mat.ger α (vec m 2) (vec n 3) (mat m n 1)).toList ==
    gerList α (vec m 2) (vec n 3) (mat m n 1)
  let A := matLd m n 4 (m + 3) 1
  let B := Mat.ger α (vecInc m 1 2 2) (vecInc n 0 3 3) A
  ok₁ && B.toList == gerList α (vec m 2) (vec n 3) (mat m n 1) && marks B.data == marks A.data

#guard gerMatches 5 4 1.5
#guard gerMatches 1 1 2
#guard gerMatches 300 70 (-0.75)
#guard gerMatches 0 3 1
#guard gerMatches 3 0 1
#guard gerMatches 5 4 0

-- As in the reference BLAS, `α = 0` returns `A`, and a column with `y[j] = 0` is skipped, so an
-- infinity in `x` doesn't reach it.
#guard (Mat.ger (m := 2) (n := 2) 0 (.ofList [1 / 0, 1]) (.ofList [1, 1])
  (.ofFn fun _ _ => 1)).toList == [1, 1, 1, 1]
#guard (Mat.ger (m := 2) (n := 2) 1 (.ofList [1 / 0, 1]) (.ofList [0, 1])
  (.ofFn fun _ _ => 1)).toList == [1, 1, 1 / 0, 2]

/-- Whether `ger` updates an unshared `A` in place. -/
def gerInPlace (m : Nat) : Bool :=
  let (p, A) := withAddrMat (matLd m m 2 (m + 1))
  BLASTest.addr (Mat.ger 1 (vec m 2) (vec m 3) A).data == p

#guard gerInPlace 8

/-! ## `trsv` -/

-- `[[2, 0], [1, 1]] * y = [4, 3]` gives `y = [2, 1]`; `[[2, 1], [0, 1]] * y = [5, 1]` gives
-- `[2, 1]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 1, 1], by decide⟩
  (Mat.trsv .lower .nonUnit A (.ofList [4, 3])).toList == [2, 1] &&
    (Mat.trsv .upper .nonUnit A (.ofList [5, 1])).toList == [2, 1] &&
    (Mat.trsv .lower .unit A (.ofList [4, 3])).toList == [4, -1] &&
    (Mat.trsv .upper .unit A (.ofList [5, 1])).toList == [4, 1]

/-- A matrix with the elements of `mat n n s`, and `n + 4 + i` on the diagonal. -/
def triMat (n : Nat) (s : Nat := 0) (other : Float := 0) (uplo : Uplo := .lower) : Mat n n :=
  .ofFn fun i j =>
    if i.val = j.val then (n + 4 + i.val).toFloat
    else if (uplo = .lower ∧ j.val < i.val) ∨ (uplo = .upper ∧ i.val < j.val) then
      ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5
    else other

/-- The loops of the reference BLAS for `trsv`, on an `Array`. -/
def trsvRef (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : List Float := Id.run do
  let mut y := x.toList.toArray
  let cols := match uplo with
    | .lower => List.range n
    | .upper => (List.range n).reverse
  for j in cols do
    let t := d.apply y[j]! (A[(j, j)]?.getD 0)
    y := y.set! j t
    let rows := match uplo with
      | .lower => (List.range n).filter (j < ·)
      | .upper => List.range j
    for i in rows do
      y := y.set! i (y[i]! - t * (A[(i, j)]?.getD 0))
  return y.toList

/--
Whether `trsv` matches the reference loops, on packed operands and on operands with offsets, strides
and leading dimensions, doesn't read the other triangle (nor the diagonal when it is unit), and
leaves the rest of `x`'s array unchanged.
-/
def trsvMatches (n : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let A := triMat n 1 0 uplo
  let ok₁ := (Mat.trsv uplo d A (vec n 2)).toList == trsvRef uplo d A (vec n 2)
  let nan : Float := 0 / 0
  let B := triMat n 1 nan uplo
  let B : Mat n n := match d with
    | .nonUnit => B
    | .unit => .ofFn fun i j => if i.val = j.val then nan else B[(i.val, j.val)]
  let B' := (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then B[(i.val, j.val)]'⟨h, j.isLt⟩ else mark).data 0 (n + 3)).getD B
  let x := vecInc n 2 3 2
  let y := Mat.trsv uplo d B' x
  ok₁ && y.toList == trsvRef uplo d A (vec n 2) && marks y.data == marks x.data

#guard [Uplo.lower, .upper].all fun u => [Diag.unit, .nonUnit].all fun d =>
  trsvMatches 5 u d && trsvMatches 1 u d && trsvMatches 0 u d && trsvMatches 40 u d &&
    trsvMatches 300 u d

/-- The residual `A * y - x` of a solve, by `gemv`: zero up to rounding. -/
def trsvResidual (n : Nat) (uplo : Uplo) : Float :=
  let A := triMat n 1 0 uplo
  let y := Mat.trsv uplo .nonUnit A (vec n 2)
  let r := Mat.gemv 1 A y (-1) (vec n 2)
  r.toList.foldl (fun s v => max s v.abs) 0

#guard trsvResidual 50 .lower < 1e-12 && trsvResidual 50 .upper < 1e-12

/-- Whether `trsv` updates an unshared `x` in place. -/
def trsvInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (vecInc n 1 2)
  let (q, x') := withAddr (vecInc n 1 2 5)
  BLASTest.addr (Mat.trsv .lower .nonUnit (triMat n) x).data == p &&
    BLASTest.addr (Mat.trsv .upper .unit (triMat n 0 0 .upper) x').data == q

#guard trsvInPlace 8

/-! ## `trsvT` -/

-- `[[2, 0], [1, 1]]ᵀ * y = [5, 1]` gives `y = [2, 1]`; `[[2, 1], [0, 1]]ᵀ * y = [4, 3]` gives
-- `[2, 1]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 1, 1], by decide⟩
  (Mat.trsvT .lower .nonUnit A (.ofList [5, 1])).toList == [2, 1] &&
    (Mat.trsvT .upper .nonUnit A (.ofList [4, 3])).toList == [2, 1] &&
    (Mat.trsvT .lower .unit A (.ofList [5, 1])).toList == [4, 1] &&
    (Mat.trsvT .upper .unit A (.ofList [4, 3])).toList == [4, -1]

/-- The loops of the reference BLAS for `trsv` with `TRANS = 'T'`, on an `Array`. -/
def trsvTRef (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : List Float := Id.run do
  let mut y := x.toList.toArray
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let cols := match uplo with
    | .upper => List.range n
    | .lower => (List.range n).reverse
  for j in cols do
    let mut t := y[j]!
    let rows := match uplo with
      | .upper => List.range j
      | .lower => ((List.range n).filter (j < ·)).reverse
    for i in rows do
      t := t - a i j * y[i]!
    if d == .nonUnit then t := t / a j j
    y := y.set! j t
  return y.toList

/--
Whether `trsvT` matches the reference loops, on packed operands and on operands with offsets,
strides and leading dimensions, doesn't read the other triangle (nor the diagonal when it is unit),
and leaves the rest of `x`'s array unchanged.
-/
def trsvTMatches (n : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let A := triMat n 1 0 uplo
  let ok₁ := (Mat.trsvT uplo d A (vec n 2)).toList == trsvTRef uplo d A (vec n 2)
  let nan : Float := 0 / 0
  let B := triMat n 1 nan uplo
  let B : Mat n n := match d with
    | .nonUnit => B
    | .unit => .ofFn fun i j => if i.val = j.val then nan else B[(i.val, j.val)]
  let B' := (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then B[(i.val, j.val)]'⟨h, j.isLt⟩ else mark).data 0 (n + 3)).getD B
  let x := vecInc n 2 3 2
  let y := Mat.trsvT uplo d B' x
  ok₁ && y.toList == trsvTRef uplo d A (vec n 2) && marks y.data == marks x.data

#guard [Uplo.lower, .upper].all fun u => [Diag.unit, .nonUnit].all fun d =>
  trsvTMatches 5 u d && trsvTMatches 1 u d && trsvTMatches 0 u d && trsvTMatches 40 u d &&
    trsvTMatches 300 u d

/-- The residual `Aᵀ * y - x` of a solve, by `gemvT`: zero up to rounding. -/
def trsvTResidual (n : Nat) (uplo : Uplo) : Float :=
  let A := triMat n 1 0 uplo
  let y := Mat.trsvT uplo .nonUnit A (vec n 2)
  let r := Mat.gemvT 1 A y (-1) (vec n 2)
  r.toList.foldl (fun s v => max s v.abs) 0

#guard trsvTResidual 50 .lower < 1e-12 && trsvTResidual 50 .upper < 1e-12

/-- Whether `trsvT` updates an unshared `x` in place. -/
def trsvTInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (vecInc n 1 2)
  let (q, x') := withAddr (vecInc n 1 2 5)
  BLASTest.addr (Mat.trsvT .lower .nonUnit (triMat n) x).data == p &&
    BLASTest.addr (Mat.trsvT .upper .unit (triMat n 0 0 .upper) x').data == q

#guard trsvTInPlace 8

/-! ## `trmv` and `trmvT` -/

/-- The elements of `A` divided by `3`, so that the order of the sums changes their roundings. -/
def thirdsMat (A : Mat n n) : Mat n n := .ofFn fun i j => A[(i.val, j.val)] / 3

-- `A = [[2, 1], [1, 1]]`, read by triangle: `[[2, 0], [1, 1]] * [1, 2] = [2, 3]`,
-- `[[2, 1], [0, 1]] * [1, 2] = [4, 2]`, and the transposes give `[4, 2]` and `[2, 3]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 1, 1], by decide⟩
  let x : Vec 2 := .ofList [1, 2]
  (Mat.trmv .lower .nonUnit A x).toList == [2, 3] &&
    (Mat.trmv .upper .nonUnit A x).toList == [4, 2] &&
    (Mat.trmv .lower .unit A x).toList == [1, 3] &&
    (Mat.trmv .upper .unit A x).toList == [3, 2] &&
    (Mat.trmvT .lower .nonUnit A x).toList == [4, 2] &&
    (Mat.trmvT .upper .nonUnit A x).toList == [2, 3] &&
    (Mat.trmvT .lower .unit A x).toList == [3, 2] &&
    (Mat.trmvT .upper .unit A x).toList == [1, 3]

/-- The loops of the reference BLAS for `trmv`, on an `Array`. -/
def trmvRef (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : List Float := Id.run do
  let mut y := x.toList.toArray
  let a (i j : Nat) := A[(i, j)]?.getD 0
  match uplo with
  | .upper =>
    for j in List.range n do
      let t := y[j]!
      for i in List.range j do
        y := y.set! i (y[i]! + t * a i j)
      if d == .nonUnit then y := y.set! j (y[j]! * a j j)
  | .lower =>
    for j in (List.range n).reverse do
      let t := y[j]!
      for i in ((List.range n).filter (j < ·)).reverse do
        y := y.set! i (y[i]! + t * a i j)
      if d == .nonUnit then y := y.set! j (y[j]! * a j j)
  return y.toList

/-- The loops of the reference BLAS for `trmv` with `TRANS = 'T'`, on an `Array`. -/
def trmvTRef (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : List Float := Id.run do
  let mut y := x.toList.toArray
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let cols := match uplo with
    | .upper => (List.range n).reverse
    | .lower => List.range n
  for j in cols do
    let mut t := y[j]!
    if d == .nonUnit then t := t * a j j
    let rows := match uplo with
      | .upper => (List.range j).reverse
      | .lower => (List.range n).filter (j < ·)
    for i in rows do
      t := t + a i j * y[i]!
    y := y.set! j t
  return y.toList

/--
Whether `trmv` (or `trmvT` if `t`) matches the reference loops, on packed operands and on operands
with offsets, strides and leading dimensions, doesn't read the other triangle (nor the diagonal
when it is unit), and leaves the rest of `x`'s array unchanged.
-/
def trmvMatches (t : Bool) (n : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let f := if t then Mat.trmvT uplo d else Mat.trmv uplo d
  let ref := if t then trmvTRef uplo d else trmvRef uplo d
  let A := thirdsMat (triMat n 1 0 uplo)
  let ok₁ := (f A (vec n 2)).toList == ref A (vec n 2)
  let nan : Float := 0 / 0
  let B := thirdsMat (triMat n 1 nan uplo)
  let B : Mat n n := match d with
    | .nonUnit => B
    | .unit => .ofFn fun i j => if i.val = j.val then nan else B[(i.val, j.val)]
  let B' := (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then B[(i.val, j.val)]'⟨h, j.isLt⟩ else mark).data 0 (n + 3)).getD B
  let x := vecInc n 2 3 2
  let y := f B' x
  ok₁ && y.toList == ref A (vec n 2) && marks y.data == marks x.data

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d =>
    trmvMatches t 5 u d && trmvMatches t 1 u d && trmvMatches t 0 u d &&
      trmvMatches t 40 u d && trmvMatches t 300 u d

/-- `trsv` undoes `trmv`, and `trsvT` undoes `trmvT`, up to rounding. -/
def trmvResidual (n : Nat) (uplo : Uplo) : Float :=
  let A := triMat n 1 0 uplo
  let y := Mat.trsv uplo .nonUnit A (Mat.trmv uplo .nonUnit A (vec n 2))
  let z := Mat.trsvT uplo .nonUnit A (Mat.trmvT uplo .nonUnit A (vec n 2))
  let e := (y.toList.zip (vec n 2).toList) ++ (z.toList.zip (vec n 2).toList)
  e.foldl (fun s (u, v) => max s (u - v).abs) 0

#guard trmvResidual 50 .lower < 1e-9 && trmvResidual 50 .upper < 1e-9

/-- Whether `trmv` and `trmvT` update an unshared `x` in place. -/
def trmvInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (vecInc n 1 2)
  let (q, x') := withAddr (vecInc n 1 2 5)
  BLASTest.addr (Mat.trmv .lower .nonUnit (triMat n) x).data == p &&
    BLASTest.addr (Mat.trmvT .upper .unit (triMat n 0 0 .upper) x').data == q

#guard trmvInPlace 8

/-! ## `symv` -/

-- `A = [[2, 1], [1, 3]]`, stored in either triangle: `A * [1, 2] = [4, 7]`.
#guard
  let nan : Float := 0 / 0
  let U : Mat 2 2 := .ofPMat ⟨.ofList [2, nan, 1, 3], by decide⟩
  let L : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, nan, 3], by decide⟩
  let x : Vec 2 := .ofList [1, 2]
  let y : Vec 2 := .ofList [10, 20]
  (Mat.symv .upper 1 U x 0 y).toList == [4, 7] && (Mat.symv .lower 1 L x 0 y).toList == [4, 7] &&
    (Mat.symv .upper 2 U x 1 y).toList == [18, 34] &&
    (Mat.symv .lower 0 L x 0.5 y).toList == [5, 10]

/-- The loops of the reference BLAS for `symv`, on `Array`s. -/
def symvRef (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float) (y : Vec n) :
    List Float := Id.run do
  let mut b := y.toList.toArray
  let xs := x.toList.toArray
  if n == 0 || (α == 0 && β == 1) then return b.toList
  if β != 1 then
    for i in List.range n do b := b.set! i (if β == 0 then 0 else β * b[i]!)
  if α == 0 then return b.toList
  let a (i j : Nat) := A[(i, j)]?.getD 0
  for j in List.range n do
    let t₁ := α * xs[j]!
    let mut t₂ : Float := 0
    match uplo with
    | .upper =>
      for i in List.range j do
        b := b.set! i (b[i]! + t₁ * a i j)
        t₂ := t₂ + a i j * xs[i]!
      b := b.set! j (b[j]! + t₁ * a j j + α * t₂)
    | .lower =>
      b := b.set! j (b[j]! + t₁ * a j j)
      for i in (List.range n).filter (j < ·) do
        b := b.set! i (b[i]! + t₁ * a i j)
        t₂ := t₂ + a i j * xs[i]!
      b := b.set! j (b[j]! + α * t₂)
  return b.toList

/-- The bits of a list of floats. -/
def floatBits (l : List Float) := l.map Float.toBits

/--
Whether `symv` matches the reference loops bit for bit, on packed operands and on operands with
offsets, strides and leading dimensions, doesn't read the other triangle, and leaves the rest of
`y`'s array unchanged.
-/
def symvMatches (n : Nat) (uplo : Uplo) (α β : Float) : Bool :=
  let A := thirdsMat (triMat n 1 0 uplo)
  let r := symvRef uplo α A (vec n 2) β (vec n 5)
  let ok₁ := floatBits (Mat.symv uplo α A (vec n 2) β (vec n 5)).toList == floatBits r
  let B := thirdsMat (triMat n 1 (0 / 0) uplo)
  let B' := (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then B[(i.val, j.val)]'⟨h, j.isLt⟩ else mark).data 0 (n + 3)).getD B
  let y := vecInc n 1 2 5
  let z := Mat.symv uplo α B' (vecInc n 2 3 2) β y
  ok₁ && floatBits z.toList == floatBits r && marks z.data == marks y.data

#guard [Uplo.lower, .upper].all fun u =>
  symvMatches 5 u 1.5 0.5 && symvMatches 1 u 2 0 && symvMatches 0 u 1 1 &&
    symvMatches 40 u (-0.25) 1 && symvMatches 300 u (1 / 7) (-2) && symvMatches 17 u 0 0.5 &&
    symvMatches 17 u 0 0 && symvMatches 17 u 1 0 && symvMatches 6 u 1.5 0.5 &&
    symvMatches 7 u (-0.25) 1 && symvMatches 11 u (1 / 7) (-2)

/-- `symv` on the two triangles of a symmetric matrix agrees with `gemv`, up to rounding. -/
def symvResidual (n : Nat) : Float :=
  let S : Mat n n := .ofFn fun i j => ((i.val * j.val + i.val + j.val) % 7).toFloat / 3
  let g := Mat.gemv 1.5 S (vec n 2) 0.5 (vec n 5)
  let e := ((Mat.symv .upper 1.5 S (vec n 2) 0.5 (vec n 5)).toList.zip g.toList) ++
    ((Mat.symv .lower 1.5 S (vec n 2) 0.5 (vec n 5)).toList.zip g.toList)
  e.foldl (fun s (u, v) => max s (u - v).abs) 0

#guard symvResidual 50 < 1e-12

/-- Whether `symv` updates an unshared `y` in place. -/
def symvInPlace (n : Nat) : Bool :=
  let (p, y) := withAddr (vecInc n 1 2)
  let (q, y') := withAddr (vecInc n 1 2 5)
  BLASTest.addr (Mat.symv .lower 2 (triMat n) (vec n) 0.5 y).data == p &&
    BLASTest.addr (Mat.symv .upper 2 (triMat n 0 0 .upper) (vec n) 0 y').data == q

#guard symvInPlace 8

/-! ## `syr` and `syr2` -/

/-- The `2 × 2` matrix of `1`s. -/
def ones : Mat 2 2 := .ofFn fun _ _ => 1

-- `[1, 2] * [1, 2]ᵀ` on each triangle, over `1`s: the other triangle is unchanged.
#guard (Mat.syr (n := 2) .upper 1 (.ofList [1, 2]) ones).toList == [2, 1, 3, 5]
#guard (Mat.syr (n := 2) .lower 1 (.ofList [1, 2]) ones).toList == [2, 3, 1, 5]
#guard (Mat.syr2 (n := 2) .upper 1 (.ofList [1, 2]) (.ofList [3, 4]) ones).toList ==
  [7, 1, 11, 17]

/-- The loops of the reference BLAS for `syr2`, or `syr` when `y` is `none`, on `Array`s. -/
def syrRef (uplo : Uplo) (α : Float) (x : Vec n) (y : Option (Vec n)) (A : Mat n n) :
    List Float := Id.run do
  let mut a := A.toList.toArray
  let xs := x.toList.toArray
  if n == 0 || α == 0 then return a.toList
  for j in List.range n do
    let is := match uplo with
      | .upper => List.range (j + 1)
      | .lower => (List.range n).filter (j ≤ ·)
    match y with
    | none =>
      if xs[j]! != 0 then
        let t := α * xs[j]!
        for i in is do a := a.set! (i + n * j) (a[i + n * j]! + xs[i]! * t)
    | some y =>
      let ys := y.toList.toArray
      if xs[j]! != 0 || ys[j]! != 0 then
        let t₁ := α * ys[j]!
        let t₂ := α * xs[j]!
        for i in is do a := a.set! (i + n * j) (a[i + n * j]! + xs[i]! * t₁ + ys[i]! * t₂)
  return a.toList

/-- `vec n s` divided by `3`, so that the order of the sums changes their roundings. -/
def thirdsVec (n : Nat) (s : Nat := 0) : Vec n :=
  let x := vec n s
  .ofFn fun i => x[i.val] / 3

/--
Whether `syr` and `syr2` match the reference loops bit for bit, on packed operands and on operands
with offsets, strides and leading dimensions, leave the other triangle (here `NaN`) unchanged, and
leave the rest of `A`'s array unchanged.
-/
def syrMatches (n : Nat) (uplo : Uplo) (α : Float) : Bool :=
  let A := thirdsMat (triMat n 1 (0 / 0) uplo)
  let x := thirdsVec n 2
  let y := thirdsVec n 5
  let r := syrRef uplo α x none A
  let r2 := syrRef uplo α x (some y) A
  let A' := (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then A[(i.val, j.val)]'⟨h, j.isLt⟩ else mark).data 0 (n + 3)).getD A
  let x' : Vec n := (Vec.ofStride? (ScalarArray.Float64Array.ofFn (n := 1 + 2 * n) fun p =>
    if 1 ≤ p.val ∧ (p.val - 1) % 2 = 0 then x[(p.val - 1) / 2]! else mark) 1 2).getD x
  let y' : Vec n := (Vec.ofStride? (ScalarArray.Float64Array.ofFn (n := 3 * n) fun p =>
    if p.val % 3 = 0 then y[p.val / 3]! else mark) 0 3).getD y
  let B := Mat.syr uplo α x' A'
  let B2 := Mat.syr2 uplo α x' y' A'
  floatBits (Mat.syr uplo α x A).toList == floatBits r &&
    floatBits (Mat.syr2 uplo α x y A).toList == floatBits r2 &&
    floatBits B.toList == floatBits r && floatBits B2.toList == floatBits r2 &&
    marks B.data == marks A'.data && marks B2.data == marks A'.data

#guard (thirdsVec 9 2).toList.contains 0
#guard [Uplo.lower, .upper].all fun u =>
  syrMatches 5 u 1.5 && syrMatches 1 u 2 && syrMatches 0 u 1 && syrMatches 40 u (-0.25) &&
    syrMatches 300 u (1 / 7) && syrMatches 17 u 0

-- A column with `x[j] = 0` (and `y[j] = 0` for `syr2`) is skipped, so an infinity in `x` or `y`
-- doesn't reach it.
#guard
  let inf : Float := 1 / 0
  (Mat.syr (n := 2) .lower 1 (.ofList [0, inf]) ones).toList == [1, 1, 1, inf] &&
    ((Mat.syr2 (n := 2) .lower 1 (.ofList [0, inf]) (.ofList [0, 1]) ones).toList.take 3) ==
      [1, 1, 1]

/-- Whether `syr` and `syr2` update an unshared `A` in place. -/
def syrInPlace (n : Nat) : Bool :=
  let (p, A) := withAddrMat (matLd n n 2 (n + 1))
  let (q, A') := withAddrMat (matLd n n 2 (n + 1) 3)
  BLASTest.addr (Mat.syr .lower 1 (vec n 2) A).data == p &&
    BLASTest.addr (Mat.syr2 .upper 1 (vec n 2) (vec n 3) A').data == q

#guard syrInPlace 8
