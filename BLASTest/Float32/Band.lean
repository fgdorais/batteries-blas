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
Tests for the band routines `gbmv`, `gbmvT`, `sbmv`, `tbmv`, `tbmvT`, `tbsv` and `tbsvT` on
`Float32`, against transcriptions of the loops of the reference BLAS (`dgbmv`, `dsbmv`, `dtbmv` and
`dtbsv`) on the band storage.
-/

open BLAS.Float32

/--
The value of the elements outside the vectors and matrices of the tests, which no test computes.
-/
def mark : Float32 := 1e9 + 0.5

/-- The number of `mark`s in an array: the elements outside a vector or matrix of the tests. -/
def marks (a : ScalarArray.Float32Array) : Nat := a.toList.countP (· == mark)

/-- The bits of a list of floats. -/
def floatBits (l : List Float32) := l.map Float32.toBits

/-- `NaN`, for the elements of the band storage that are not part of the matrix. -/
def nan : Float32 := 0 / 0

/--
A vector of thirds of small integers computed from the indices and the seed `s`, so that the order
of the sums changes their roundings.
-/
def vec (n : Nat) (s : Nat := 0) : Vec n :=
  .ofFn fun i => (((i.val * 5 + s) % 9).toFloat32 - 4) / 3

/-- `vec n s` at the offset `off` with the stride `inc`, in an array of `mark`s. -/
def vecInc (n off inc : Nat) (s : Nat := 0) : Vec n :=
  let a := ScalarArray.Float32Array.ofFn (n := off + inc * n) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 then
      ((((p.val - off) / inc * 5 + s) % 9).toFloat32 - 4) / 3
    else mark
  (Vec.ofStride? a off inc).getD (vec n s)

/--
The `r × n` matrix with the elements `f q j`, packed, and at the offset `2` with the leading
dimension `r + 3`, in an array of `mark`s.
-/
def store (r n : Nat) (f : Nat → Nat → Float32) : Mat r n × Mat r n :=
  let A : Mat r n := .ofFn fun q j => f q.val j.val
  let a := ScalarArray.Float32Array.ofFn (n := 2 + (r + 3) * n) fun p =>
    let q := p.val - 2
    if 2 ≤ p.val ∧ q % (r + 3) < r then f (q % (r + 3)) (q / (r + 3)) else mark
  (A, (Mat.ofLd? a 2 (r + 3)).getD A)

/-- An element `i, j` of the tests' matrices: a third of a small integer. -/
def entry (i j s : Nat) : Float32 := (((i * 7 + j * 13 + s) % 11).toFloat32 - 5) / 3

/--
The band storage of an `m × n` band matrix with `kl` subdiagonals and `ku` superdiagonals: row
`ku + i - j` of column `j` holds the element `i, j`, and the elements that are not part of the
matrix are `NaN`.
-/
def gbStore (m n kl ku : Nat) (s : Nat := 0) : Mat (kl + ku + 1) n × Mat (kl + ku + 1) n :=
  store (kl + ku + 1) n fun q j =>
    if ku ≤ q + j ∧ q + j - ku < m then entry (q + j - ku) j s else nan

/--
The band storage of a triangular (or symmetric) `n × n` band matrix with `k` off-diagonals, by its
triangle `uplo`: the diagonal is `diag j`, and the elements that are not part of the matrix are
`NaN`.
-/
def triStore (n k : Nat) (uplo : Uplo) (diag : Nat → Float32) (s : Nat := 0) :
    Mat (k + 1) n × Mat (k + 1) n :=
  store (k + 1) n fun q j => match uplo with
    | .upper => if q = k then diag j else if k ≤ q + j then entry (q + j - k) j s else nan
    | .lower => if q = 0 then diag j else if q + j < n then entry (q + j) j s else nan

/-- The diagonal of the triangular tests: far from zero, so that the solves are well conditioned. -/
def diagOf (n : Nat) (j : Nat) : Float32 := (n + 4 + j).toFloat32 / 3

/-- The rows `i` of column `j` in the band, other than `j`, for `ku` rows above and `kl` below. -/
def bandRows (m kl ku j : Nat) : List Nat :=
  (List.range m).filter fun i => i + ku ≥ j ∧ i ≤ j + kl ∧ i ≠ j

/-! ## `gbmv` and `gbmvT` -/

-- The tridiagonal `[[1, 2, 0], [3, 4, 5], [0, 6, 7]]`, stored by diagonals: `A * [1, 1, 1]` is
-- `[3, 12, 13]` and `Aᵀ * [1, 1, 1]` is `[4, 12, 12]`.
#guard
  let A : Mat 3 3 := .ofPMat ⟨.ofList [0, 1, 3, 2, 4, 6, 5, 7, 0], by decide⟩
  let x : Vec 3 := .ofList [1, 1, 1]
  (Mat.gbmv 1 1 1 A x 0 x).toList == [3, 12, 13] && (Mat.gbmvT 1 1 1 A x 0 x).toList == [4, 12, 12]

-- The elements of the views are those of the band matrices.
#guard
  let A : Mat 3 3 := .ofPMat ⟨.ofList [0, 1, 3, 2, 4, 6, 5, 7, 0], by decide⟩
  let B := A.band 3 1 1
  (List.range 3).flatMap (fun i => (List.range 3).map fun j => B[(i, j)]!) ==
    [1, 2, 0, 3, 4, 5, 0, 6, 7]

#guard
  let U : Mat 2 3 := .ofPMat ⟨.ofList [0, 2, 1, 3, 1, 4], by decide⟩
  let els {T} [GetElem T (Nat × Nat) Float32 fun _ p => p.1 < 3 ∧ p.2 < 3] (t : T) :=
    (List.range 3).flatMap fun i => (List.range 3).map fun j => t[(i, j)]!
  els U.upperBand == [2, 1, 0, 0, 3, 1, 0, 0, 4] &&
    els U.unitUpperBand == [1, 1, 0, 0, 1, 1, 0, 0, 1] &&
    els U.symUpperBand == [2, 1, 0, 1, 3, 1, 0, 1, 4]

/-- The loops of the reference BLAS for `gbmv`, or `gbmvT` if `t`, on `Array`s. -/
def gbmvRef (t : Bool) (m n kl ku : Nat) (α : Float32) (A : Mat (kl + ku + 1) n) (x : List Float32)
    (β : Float32) (y : List Float32) : List Float32 := Id.run do
  let mut b := y.toArray
  let xs := x.toArray
  let a (i j : Nat) := A[(ku + i - j, j)]?.getD 0
  if m == 0 || n == 0 || (α == 0 && β == 1) then return b.toList
  if β != 1 then
    for i in List.range b.size do b := b.set! i (if β == 0 then 0 else β * b[i]!)
  if α == 0 then return b.toList
  for j in List.range n do
    let rows := (List.range m).filter fun i => i + ku ≥ j ∧ i ≤ j + kl
    if t then
      let mut s : Float32 := 0
      for i in rows do s := s + a i j * xs[i]!
      b := b.set! j (b[j]! + α * s)
    else
      let s := α * xs[j]!
      for i in rows do b := b.set! i (b[i]! + s * a i j)
  return b.toList

/--
Whether `gbmv` and `gbmvT` match the reference loops bit for bit, on packed operands and on
operands with offsets, strides and leading dimensions, don't read the elements of the storage
outside the band (here `NaN`), and leave the rest of `y`'s array unchanged.
-/
def gbmvMatches (m n kl ku : Nat) (α β : Float32) : Bool :=
  let (A, A') := gbStore m n kl ku 1
  let r := gbmvRef false m n kl ku α A (vec n 2).toList β (vec m 5).toList
  let rT := gbmvRef true m n kl ku α A (vec m 2).toList β (vec n 5).toList
  let y := vecInc m 1 2 5
  let z := Mat.gbmv kl ku α A' (vecInc n 2 3 2) β y
  let yT := vecInc n 1 2 5
  let zT := Mat.gbmvT kl ku α A' (vecInc m 2 3 2) β yT
  floatBits (Mat.gbmv kl ku α A (vec n 2) β (vec m 5)).toList == floatBits r &&
    floatBits z.toList == floatBits r && marks z.data == marks y.data &&
    floatBits (Mat.gbmvT kl ku α A (vec m 2) β (vec n 5)).toList == floatBits rT &&
    floatBits zT.toList == floatBits rT && marks zT.data == marks yT.data

#guard [(0, 0), (1, 2), (3, 0), (0, 4), (9, 9)].all fun (kl, ku) =>
  gbmvMatches 5 7 kl ku 1.5 0.5 && gbmvMatches 7 5 kl ku (-0.25) 1 &&
    gbmvMatches 1 1 kl ku 2 0 && gbmvMatches 0 3 kl ku 1 2 && gbmvMatches 3 0 kl ku 1 2 &&
    gbmvMatches 40 40 kl ku (1 / 7) (-2) && gbmvMatches 17 13 kl ku 0 0.5 &&
    gbmvMatches 13 17 kl ku 0 0 && gbmvMatches 13 17 kl ku 1 0

#guard gbmvMatches 300 300 4 3 (1 / 7) (-2)

/-- `gbmv` and `gbmvT` agree with `gemv` and `gemvT` on the full matrix, up to rounding. -/
def gbmvResidual (m n kl ku : Nat) : Float32 :=
  let (A, _) := gbStore m n kl ku 1
  let F : Mat m n := .ofFn fun i j =>
    if i.val + ku ≥ j.val ∧ i.val ≤ j.val + kl then A[(ku + i.val - j.val, j.val)]?.getD 0 else 0
  let e := ((Mat.gbmv kl ku 1.5 A (vec n 2) 0.5 (vec m 5)).toList.zip
      (Mat.gemv 1.5 F (vec n 2) 0.5 (vec m 5)).toList) ++
    ((Mat.gbmvT kl ku 1.5 A (vec m 2) 0.5 (vec n 5)).toList.zip
      (Mat.gemvT 1.5 F (vec m 2) 0.5 (vec n 5)).toList)
  e.foldl (fun s (u, v) => max s (u - v).abs) 0

#guard gbmvResidual 30 20 2 5 < 1e-4 && gbmvResidual 20 30 6 1 < 1e-4

/-! ## `sbmv` -/

-- The symmetric tridiagonal `[[1, 2, 0], [2, 3, 4], [0, 4, 5]]` times `[1, 1, 1]` is `[3, 9, 9]`.
#guard
  let U : Mat 2 3 := .ofPMat ⟨.ofList [0, 1, 2, 3, 4, 5], by decide⟩
  let L : Mat 2 3 := .ofPMat ⟨.ofList [1, 2, 3, 4, 5, 0], by decide⟩
  let x : Vec 3 := .ofList [1, 1, 1]
  (Mat.sbmv .upper 1 U x 0 x).toList == [3, 9, 9] && (Mat.sbmv .lower 1 L x 0 x).toList == [3, 9, 9]

/-- The loops of the reference BLAS for `sbmv`, on `Array`s. -/
def sbmvRef (uplo : Uplo) (n k : Nat) (α : Float32) (A : Mat (k + 1) n) (x : List Float32)
    (β : Float32) (y : List Float32) : List Float32 := Id.run do
  let mut b := y.toArray
  let xs := x.toArray
  if n == 0 || (α == 0 && β == 1) then return b.toList
  if β != 1 then
    for i in List.range n do b := b.set! i (if β == 0 then 0 else β * b[i]!)
  if α == 0 then return b.toList
  for j in List.range n do
    let t₁ := α * xs[j]!
    let mut t₂ : Float32 := 0
    match uplo with
    | .upper =>
      let a (i : Nat) := A[(k + i - j, j)]?.getD 0
      for i in bandRows n 0 k j do
        b := b.set! i (b[i]! + t₁ * a i)
        t₂ := t₂ + a i * xs[i]!
      b := b.set! j (b[j]! + t₁ * a j + α * t₂)
    | .lower =>
      let a (i : Nat) := A[(i - j, j)]?.getD 0
      b := b.set! j (b[j]! + t₁ * a j)
      for i in bandRows n k 0 j do
        b := b.set! i (b[i]! + t₁ * a i)
        t₂ := t₂ + a i * xs[i]!
      b := b.set! j (b[j]! + α * t₂)
  return b.toList

/--
Whether `sbmv` matches the reference loops bit for bit, on packed operands and on operands with
offsets, strides and leading dimensions, doesn't read the elements of the storage outside the band
(here `NaN`), and leaves the rest of `y`'s array unchanged.
-/
def sbmvMatches (n k : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let (A, A') := triStore n k uplo (diagOf n) 1
  let r := sbmvRef uplo n k α A (vec n 2).toList β (vec n 5).toList
  let y := vecInc n 1 2 5
  let z := Mat.sbmv uplo α A' (vecInc n 2 3 2) β y
  floatBits (Mat.sbmv uplo α A (vec n 2) β (vec n 5)).toList == floatBits r &&
    floatBits z.toList == floatBits r && marks z.data == marks y.data

#guard [Uplo.lower, .upper].all fun u => [0, 1, 3, 9].all fun k =>
  sbmvMatches 5 k u 1.5 0.5 && sbmvMatches 1 k u 2 0 && sbmvMatches 0 k u 1 1 &&
    sbmvMatches 40 k u (-0.25) 1 && sbmvMatches 17 k u 0 0.5 && sbmvMatches 17 k u 0 0 &&
    sbmvMatches 17 k u 1 0

#guard sbmvMatches 300 4 .upper (1 / 7) (-2) && sbmvMatches 300 4 .lower (1 / 7) (-2)

/-! ## `tbmv` and `tbmvT` -/

-- The bidiagonal `[[2, 1, 0], [0, 3, 1], [0, 0, 4]]` times `[1, 2, 3]` is `[4, 9, 12]`, and its
-- transpose times `[1, 2, 3]` is `[2, 7, 14]`.
#guard
  let U : Mat 2 3 := .ofPMat ⟨.ofList [0, 2, 1, 3, 1, 4], by decide⟩
  let x : Vec 3 := .ofList [1, 2, 3]
  (Mat.tbmv .upper .nonUnit U x).toList == [4, 9, 12] &&
    (Mat.tbmvT .upper .nonUnit U x).toList == [2, 7, 14] &&
    (Mat.tbmv .upper .unit U x).toList == [3, 5, 3] &&
    (Mat.tbmvT .upper .unit U x).toList == [1, 3, 5]

/-- The loops of the reference BLAS for `tbmv`, or `tbmvT` if `t`, on an `Array`. -/
def tbmvRef (t : Bool) (uplo : Uplo) (d : Diag) (n k : Nat) (A : Mat (k + 1) n) (x : List Float32) :
    List Float32 := Id.run do
  let mut y := x.toArray
  let a (i j : Nat) := match uplo with
    | .upper => A[(k + i - j, j)]?.getD 0
    | .lower => A[(i - j, j)]?.getD 0
  let rows (j : Nat) := match uplo with
    | .upper => bandRows n 0 k j
    | .lower => bandRows n k 0 j
  -- the columns in the order of the loops
  let up := match uplo with | .upper => true | .lower => false
  let cols := if up != t then List.range n else (List.range n).reverse
  for j in cols do
    if t then
      let mut s := y[j]!
      if d == .nonUnit then s := s * a j j
      for i in (if up then (rows j).reverse else rows j) do s := s + a i j * y[i]!
      y := y.set! j s
    else
      let s := y[j]!
      for i in (if up then rows j else (rows j).reverse) do y := y.set! i (y[i]! + s * a i j)
      if d == .nonUnit then y := y.set! j (y[j]! * a j j)
  return y.toList

/--
Whether `tbmv` (or `tbmvT` if `t`) matches the reference loops bit for bit, on packed operands and
on operands with offsets, strides and leading dimensions, doesn't read the elements of the storage
outside the band (here `NaN`), nor the diagonal when it is unit, and leaves the rest of `x`'s array
unchanged.
-/
def tbmvMatches (t : Bool) (n k : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let f := if t then Mat.tbmvT uplo d else Mat.tbmv uplo d
  let (A, A') := triStore n k uplo (fun j => if d == .unit then nan else diagOf n j) 1
  let r := tbmvRef t uplo d n k A (vec n 2).toList
  let x := vecInc n 2 3 2
  let y := f A' x
  floatBits (f A (vec n 2)).toList == floatBits r && floatBits y.toList == floatBits r &&
    marks y.data == marks x.data

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d => [0, 1, 3, 9].all fun k =>
    tbmvMatches t 5 k u d && tbmvMatches t 1 k u d && tbmvMatches t 0 k u d &&
      tbmvMatches t 40 k u d

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d => tbmvMatches t 300 4 u d

/--
The address of the array of `x`, with `x`. It is not inlined, so the address is taken before `x`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-- Whether `tbmv` and `tbmvT` update an unshared `x` in place. -/
def tbmvInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (vecInc n 1 2)
  let (q, x') := withAddr (vecInc n 1 2 5)
  BLASTest.addr (Mat.tbmv .lower .nonUnit (triStore n 2 .lower (diagOf n)).1 x).data == p &&
    BLASTest.addr (Mat.tbmvT .upper .unit (triStore n 2 .upper (diagOf n)).1 x').data == q

#guard tbmvInPlace 8

/-! ## `tbsv` and `tbsvT` -/

-- The bidiagonal `[[2, 1, 0], [0, 3, 1], [0, 0, 4]]` times `[1, 2, 3]` is `[4, 9, 12]`, and its
-- transpose times `[1, 2, 3]` is `[2, 7, 14]`.
#guard
  let U : Mat 2 3 := .ofPMat ⟨.ofList [0, 2, 1, 3, 1, 4], by decide⟩
  (Mat.tbsv .upper .nonUnit U (.ofList [4, 9, 12])).toList == [1, 2, 3] &&
    (Mat.tbsvT .upper .nonUnit U (.ofList [2, 7, 14])).toList == [1, 2, 3] &&
    (Mat.tbsv .upper .unit U (.ofList [3, 5, 3])).toList == [1, 2, 3] &&
    (Mat.tbsvT .upper .unit U (.ofList [1, 3, 5])).toList == [1, 2, 3]

/-- The loops of the reference BLAS for `tbsv`, or `tbsvT` if `t`, on an `Array`. -/
def tbsvRef (t : Bool) (uplo : Uplo) (d : Diag) (n k : Nat) (A : Mat (k + 1) n) (x : List Float32) :
    List Float32 := Id.run do
  let mut y := x.toArray
  let a (i j : Nat) := match uplo with
    | .upper => A[(k + i - j, j)]?.getD 0
    | .lower => A[(i - j, j)]?.getD 0
  let rows (j : Nat) := match uplo with
    | .upper => bandRows n 0 k j
    | .lower => bandRows n k 0 j
  -- the columns in the order of the loops
  let up := match uplo with | .upper => true | .lower => false
  let cols := if up == t then List.range n else (List.range n).reverse
  for j in cols do
    if t then
      let mut s := y[j]!
      for i in (if up then rows j else (rows j).reverse) do s := s - a i j * y[i]!
      if d == .nonUnit then s := s / a j j
      y := y.set! j s
    else
      if d == .nonUnit then y := y.set! j (y[j]! / a j j)
      let s := y[j]!
      for i in (if up then (rows j).reverse else rows j) do y := y.set! i (y[i]! - s * a i j)
  return y.toList

/--
Whether `tbsv` (or `tbsvT` if `t`) matches the reference loops bit for bit, on packed operands and
on operands with offsets, strides and leading dimensions, doesn't read the elements of the storage
outside the band (here `NaN`), nor the diagonal when it is unit, and leaves the rest of `x`'s array
unchanged.
-/
def tbsvMatches (t : Bool) (n k : Nat) (uplo : Uplo) (d : Diag) : Bool :=
  let f := if t then Mat.tbsvT uplo d else Mat.tbsv uplo d
  let (A, A') := triStore n k uplo (fun j => if d == .unit then nan else diagOf n j) 1
  let r := tbsvRef t uplo d n k A (vec n 2).toList
  let x := vecInc n 2 3 2
  let y := f A' x
  floatBits (f A (vec n 2)).toList == floatBits r && floatBits y.toList == floatBits r &&
    marks y.data == marks x.data

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d => [0, 1, 3, 9].all fun k =>
    tbsvMatches t 5 k u d && tbsvMatches t 1 k u d && tbsvMatches t 0 k u d &&
      tbsvMatches t 40 k u d

#guard [false, true].all fun t => [Uplo.lower, .upper].all fun u =>
  [Diag.unit, .nonUnit].all fun d => tbsvMatches t 300 4 u d

/-- `tbsv` undoes `tbmv`, and `tbsvT` undoes `tbmvT`, up to rounding. -/
def tbsvResidual (n k : Nat) (uplo : Uplo) : Float32 :=
  let (A, _) := triStore n k uplo (diagOf n) 1
  let y := Mat.tbsv uplo .nonUnit A (Mat.tbmv uplo .nonUnit A (vec n 2))
  let z := Mat.tbsvT uplo .nonUnit A (Mat.tbmvT uplo .nonUnit A (vec n 2))
  ((y.toList ++ z.toList).zip ((vec n 2).toList ++ (vec n 2).toList)).foldl
    (fun s (u, v) => max s (u - v).abs) 0

#guard tbsvResidual 50 3 .lower < 1e-4 && tbsvResidual 50 3 .upper < 1e-4

-- The reference BLAS master doesn't skip a column whose element of the solution is zero, so an
-- infinity in the band below it gives `NaN` (`0 * ∞`).
#guard
  let inf : Float32 := 1 / 0
  let L : Mat 2 2 := .ofPMat ⟨.ofList [1, inf, 1, 0], by decide⟩
  ((Mat.tbsv .lower .nonUnit L (.ofList [0, 1])).toList.map Float32.isNaN) == [false, true] &&
    ((Mat.tbsvT .lower .nonUnit L (.ofList [1, 0])).toList.map Float32.isNaN) == [true, false]

/-- Whether `tbsv` and `tbsvT` update an unshared `x` in place. -/
def tbsvInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (vecInc n 1 2)
  let (q, x') := withAddr (vecInc n 1 2 5)
  BLASTest.addr (Mat.tbsv .lower .nonUnit (triStore n 2 .lower (diagOf n)).1 x).data == p &&
    BLASTest.addr (Mat.tbsvT .upper .unit (triStore n 2 .upper (diagOf n)).1 x').data == q

#guard tbsvInPlace 8
