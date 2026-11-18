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
Tests for `gemm`, `gemmTN`, `gemmNT`, `gemmTT`, `syrk`, `syrkT`, `trsm`, `trsmRight`, `trsmT`,
`trsmRightT`, `trmm`, `trmmT`, `trmmRight`, `trmmRightT`, `symm`, `symmRight`, `syr2k`, `syr2kT`,
`gemmtr`, `gemmtrTN`, `gemmtrNT` and `gemmtrTT` on `Float32`.
-/

open BLAS.Float32

/-- An `m × n` matrix of small integers computed from the indices and the seed `s`. -/
def mat (m n : Nat) (s : Nat := 0) : Mat m n :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat32 - 5

/-- The elements of `gemmEntry`, column after column. -/
def gemmModelList (α : Float32) (A : Mat m k) (B : Mat k n) (β : Float32) (C : Mat m n) :
    List Float32 :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m =>
    Mat.gemmEntry α A B β C i.val j.val i.isLt j.isLt).flatten

/--
The address of the array of `A`, with `A`. It is not inlined, so the address is taken before `A`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (A : Mat m n) : USize × Mat m n := (BLASTest.addr A.data, A)

/-- Whether `gemm` computes its model exactly, for these shapes. -/
def gemmMatchesModel (m n k : Nat) (α β : Float32) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  (Mat.gemm α A B β C).toList == gemmModelList α A B β C

/-! ## `gemm` -/

-- `[[1, 2], [3, 4]] * [[5, 6], [7, 8]] = [[19, 22], [43, 50]]`, in column-major order.
#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  let C : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 1, 1, 1], by decide⟩
  (Mat.gemm 1 A B 0 C).toList == [19, 43, 22, 50] &&
    (Mat.gemm 2 A B 1 C).toList == [39, 87, 45, 101]

-- A `2 × 3` times a `3 × 1`.
#guard
  let A : Mat 2 3 := Mat.ofPMat ⟨.ofList [1, 4, 2, 5, 3, 6], by decide⟩
  let B : Mat 3 1 := Mat.ofPMat ⟨.ofList [1, 0, -1], by decide⟩
  let C : Mat 2 1 := Mat.ofPMat ⟨.ofList [10, 20], by decide⟩
  (Mat.gemm 1 A B (-1) C).toList == [-12, -22]

#guard gemmMatchesModel 5 4 3 1.5 0.5
#guard gemmMatchesModel 1 1 1 2 3
#guard gemmMatchesModel 17 9 13 (-0.25) 2
#guard gemmMatchesModel 32 33 31 1 1

-- Empty shapes: with `k = 0`, `gemm` is `β * C`.
#guard gemmMatchesModel 0 3 2 1 1
#guard gemmMatchesModel 3 0 2 1 1
#guard gemmMatchesModel 3 2 0 1 2
#guard (Mat.gemm 1 (mat 3 0) (mat 0 2) 2 (mat 3 2)).toList == (mat 3 2).toList.map (2 * ·)

#guard gemmMatchesModel 5 4 3 0 0.5
#guard gemmMatchesModel 5 4 3 1.5 0
#guard gemmMatchesModel 5 4 3 0 0

-- As in the reference BLAS, `β = 0` sets `C` to `0` without reading it, so a `NaN` in `C` goes.
#guard
  let C : Mat 1 1 := Mat.ofPMat ⟨.ofList [0 / 0], by decide⟩
  (Mat.gemm 1 (mat 1 1) (mat 1 1) 0 C).toList == [(mat 1 1)[(0, 0)] * (mat 1 1)[(0, 0)]] &&
    (Mat.gemmNaive 1 (mat 1 1) (mat 1 1) 0 C).toList == [(mat 1 1)[(0, 0)] * (mat 1 1)[(0, 0)]]

-- `α = 0` only scales `C`, without reading `A` or `B`.
#guard
  let A : Mat 1 1 := .ofFn fun _ _ => 0 / 0
  let C : Mat 1 1 := .ofFn fun _ _ => 3
  (Mat.gemm 0 A A 2 C).toList == [6] && (Mat.gemmNaive 0 A A 0 C).toList == [0]

/-- Whether `gemm` updates an unshared `C` in place. -/
def gemmInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmInPlace 8

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == gemmModelList 1 (mat 4 4 1) (mat 4 4 2) 1 C

/-! ## `gemmNaive` -/

/-- Whether `gemm` computes the same matrix as `gemmNaive`, to the bit, for these shapes. -/
def gemmNaiveMatches (m n k : Nat) (α β : Float32) : Bool :=
  let A := mat m k 1
  let B := mat k n 2
  let C := mat m n 3
  let D := (Mat.gemm α A B β C).data
  let E := (Mat.gemmNaive α A B β C).data
  D.size == E.size && (List.range D.size).all fun i => D[i]! == E[i]!

#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  (Mat.gemmNaive 1 A B 0 (mat 2 2)).toList == [19, 43, 22, 50]

-- Odd shapes cover the last column, the leftover terms and the last row block of `gemm`.
#guard gemmNaiveMatches 5 4 3 1.5 0.5
#guard gemmNaiveMatches 1 1 1 2 3
#guard gemmNaiveMatches 17 9 13 (-0.25) 2
#guard gemmNaiveMatches 63 7 130 1 1
#guard gemmNaiveMatches 257 3 129 0.5 (-1)
#guard gemmNaiveMatches 300 5 260 1.25 0.75

-- Empty shapes.
#guard gemmNaiveMatches 0 3 2 1 1
#guard gemmNaiveMatches 3 0 2 1 1
#guard gemmNaiveMatches 3 2 0 1 2

/-- Whether `gemmNaive` updates an unshared `C` in place. -/
def gemmNaiveInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  BLASTest.addr (Mat.gemmNaive 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmNaiveInPlace 8
#guard gemmNaiveInPlace 33

-- A shared `C` is copied, and keeps its elements.
#guard
  let C := mat 4 4 3
  let D := Mat.gemmNaive 1 (mat 4 4 1) (mat 4 4 2) 1 C
  C.toList == (mat 4 4 3).toList && D.toList == (Mat.gemm 1 (mat 4 4 1) (mat 4 4 2) 1 C).toList

/-! ## Matrices with an offset and a leading dimension -/

/--
The matrix `mat m n s` at the offset `off` with the leading dimension `ld`, in an array whose
other elements are `1e9 + 0.5`, a value that no test computes.
-/
def matLd (m n off ld : Nat) (s : Nat := 0) : Mat m n :=
  let a := ScalarArray.Float32Array.ofFn (n := off + ld * n) fun p =>
    let q := p.val - off
    if off ≤ p.val ∧ q % ld < m then ((q % ld * 7 + q / ld * 13 + s) % 11).toFloat32 - 5
    else 1e9 + 0.5
  (Mat.ofLd? a off ld).getD (mat m n s)

/-- The number of elements `1e9 + 0.5` in the array of `A`: those outside a matrix of `matLd`. -/
def outside (A : Mat m n) : Nat := A.data.toList.countP (· == 1e9 + 0.5)

#guard (matLd 3 4 5 7 1).toList == (mat 3 4 1).toList
#guard (matLd 3 4 5 7).data.size == 33
#guard outside (matLd 3 4 5 7) == 33 - 12
#guard ((Mat.ofLd? (m := 3) (n := 2) (.ofList [1, 2, 3, 4, 5]) 0 2).map Mat.toList).isNone
#guard ((Mat.ofLd? (m := 2) (n := 2) (.ofList [1, 2, 3, 4, 5]) 1 2).map Mat.toList) ==
  some [2, 3, 4, 5]

-- Rows and columns are vectors.
#guard ((matLd 3 4 5 7 1).col 2 (by decide)).toList == [(mat 3 4 1)[(0, 2)], (mat 3 4 1)[(1, 2)],
  (mat 3 4 1)[(2, 2)]]
#guard ((matLd 3 4 5 7 1).row 1 (by decide)).toList ==
  (List.range 4).map fun j => (mat 3 4 1).toList[1 + 3 * j]!

/-- Whether `gemm` and `gemmNaive` on matrices with offsets and leading dimensions compute the
same elements as on packed ones, and leave the rest of `C`'s array. -/
def gemmLdMatches (m n k : Nat) (α β : Float32) : Bool :=
  let A := matLd m k 3 (m + 2) 1
  let B := matLd k n 1 (k + 1) 2
  let C := matLd m n 4 (m + 3) 3
  let D := Mat.gemm α A B β C
  let E := Mat.gemmNaive α A B β C
  D.toList == gemmModelList α (mat m k 1) (mat k n 2) β (mat m n 3) &&
    E.toList == D.toList && outside D == outside C && outside E == outside C &&
    D.data.size == C.data.size

#guard gemmLdMatches 5 4 3 1.5 0.5
#guard gemmLdMatches 17 9 13 (-0.25) 2
#guard gemmLdMatches 257 3 129 0.5 (-1)
#guard gemmLdMatches 0 3 2 1 1
#guard gemmLdMatches 3 0 2 1 1
#guard gemmLdMatches 3 2 0 1 2

/-- Whether `gemm` updates the array of an unshared `C` with a leading dimension in place. -/
def gemmLdInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (matLd m m 2 (m + 1) 3)
  BLASTest.addr (Mat.gemm 1 (mat m m 1) (mat m m 2) 1 C).data == p

#guard gemmLdInPlace 8

/-! ## Transposed `gemm` -/

/--
The loops of the reference BLAS for `gemm` on an `Array`, for an `m × n` matrix `C` with the
elements `c`, column after column, and `op(A)[i, l] = a i l`, `op(B)[l, j] = b l j`: the loops of
`transa = 'T'` when `ta`, and of `transa = 'N'` otherwise.
-/
def gemmRef (m n k : Nat) (ta : Bool) (a b : Nat → Nat → Float32) (α β : Float32)
    (c : List Float32) : List Float32 :=
  Id.run do
  let mut c := c.toArray
  if m == 0 || n == 0 || ((α == 0 || k == 0) && β == 1) then return c.toList
  if α == 0 then
    for j in List.range n do
      for i in List.range m do
        c := c.set! (i + m * j) (if β == 0 then 0 else β * c[i + m * j]!)
    return c.toList
  for j in List.range n do
    if ta then
      for i in List.range m do
        let mut t : Float32 := 0
        for l in List.range k do
          t := t + a i l * b l j
        c := c.set! (i + m * j) (if β == 0 then α * t else α * t + β * c[i + m * j]!)
    else
      if β == 0 then
        for i in List.range m do c := c.set! (i + m * j) 0
      else if β != 1 then
        for i in List.range m do c := c.set! (i + m * j) (β * c[i + m * j]!)
      for l in List.range k do
        let t := α * b l j
        for i in List.range m do
          c := c.set! (i + m * j) (c[i + m * j]! + t * a i l)
  return c.toList

/-- The bits of the elements of `A`, column after column, to compare `-0` and `NaN` too. -/
def bits (A : Mat m n) := A.toList.map Float32.toBits

/-- The bits of the elements of a list. -/
def listBits (l : List Float32) := l.map Float32.toBits

/--
Whether `gemmTN`, `gemmNT` and `gemmTT` match the reference loops to the bit, on packed operands
and on operands with offsets and leading dimensions, and leave the rest of `C`'s array unchanged.
-/
def gemmTMatches (m n k : Nat) (α β : Float32) : Bool :=
  let get {p q} (A : Mat p q) (i j : Nat) : Float32 :=
    if h : i < p ∧ j < q then A[(i, j)] else 0
  let An := mat m k 1
  let At := mat k m 1
  let Bn := mat k n 2
  let Bt := mat n k 2
  let C := mat m n 3
  let c := C.toList
  let rTN := listBits (gemmRef m n k true (fun i l => get At l i) (fun l j => get Bn l j) α β c)
  let rNT := listBits (gemmRef m n k false (fun i l => get An i l) (fun l j => get Bt j l) α β c)
  let rTT := listBits (gemmRef m n k true (fun i l => get At l i) (fun l j => get Bt j l) α β c)
  let Ald := matLd m k 3 (m + 2) 1
  let Atld := matLd k m 3 (k + 2) 1
  let Bld := matLd k n 1 (k + 1) 2
  let Btld := matLd n k 1 (n + 1) 2
  let Cld := matLd m n 4 (m + 3) 3
  let D₁ := Mat.gemmTN α Atld Bld β Cld
  let D₂ := Mat.gemmNT α Ald Btld β Cld
  let D₃ := Mat.gemmTT α Atld Btld β Cld
  bits (Mat.gemmTN α At Bn β C) == rTN && bits (Mat.gemmNT α An Bt β C) == rNT &&
    bits (Mat.gemmTT α At Bt β C) == rTT && bits D₁ == rTN && bits D₂ == rNT && bits D₃ == rTT &&
    outside D₁ == outside Cld && outside D₂ == outside Cld && outside D₃ == outside Cld &&
    D₁.data.size == Cld.data.size && D₂.data.size == Cld.data.size &&
    D₃.data.size == Cld.data.size

#guard gemmTMatches 5 4 3 1.5 0.5
#guard gemmTMatches 1 1 1 2 3
#guard gemmTMatches 17 9 13 (-0.25) 2
#guard gemmTMatches 32 33 31 1 1
#guard gemmTMatches 63 7 130 1 1
#guard gemmTMatches 257 3 129 0.5 (-1)

-- Empty shapes, and the special cases of `α` and `β`.
#guard gemmTMatches 0 3 2 1 1
#guard gemmTMatches 3 0 2 1 1
#guard gemmTMatches 3 2 0 1 2
#guard gemmTMatches 3 2 0 1 1
#guard gemmTMatches 5 4 3 0 0.5
#guard gemmTMatches 5 4 3 1.5 0
#guard gemmTMatches 5 4 3 0 0
#guard gemmTMatches 5 4 3 0 1

-- `[[1, 2], [3, 4]]ᵀ * [[5, 6], [7, 8]] = [[26, 30], [38, 44]]`, in column-major order, and the
-- other two forms.
#guard
  let A : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := Mat.ofPMat ⟨.ofList [5, 7, 6, 8], by decide⟩
  let C : Mat 2 2 := Mat.ofPMat ⟨.ofList [1, 1, 1, 1], by decide⟩
  (Mat.gemmTN 1 A B 0 C).toList == [26, 38, 30, 44] &&
    (Mat.gemmNT 1 A B 0 C).toList == [17, 39, 23, 53] &&
    (Mat.gemmTT 1 A B 0 C).toList == [23, 34, 31, 46] &&
    (Mat.gemmTN 2 A B 1 C).toList == [53, 77, 61, 89]

-- `Mat.transpose` copies the transpose.
#guard (matLd 3 4 5 7 1).transpose.toList ==
  (List.range 3).flatMap fun i => (List.range 4).map fun j => (mat 3 4 1)[(i, j)]?.getD 0

-- `gemmTN` and `gemmTT` leave `C` unchanged when `k = 0` and `β = 1`, even a `-0`.
#guard
  let C : Mat 1 1 := .ofFn fun _ _ => -0
  (Mat.gemmTN 2 (mat 0 1) (mat 0 1) 1 C)[(0, 0)].toBits == (-0 : Float32).toBits &&
    (Mat.gemmTT 2 (mat 0 1) (mat 1 0) 1 C)[(0, 0)].toBits == (-0 : Float32).toBits

-- `β = 0` sets `C` to `0` without reading it, and `α = 0` doesn't read `A` or `B`.
#guard
  let nan : Float32 := 0 / 0
  let C : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.gemmTN 0 A A 0 C)[(0, 1)] == 0 && (Mat.gemmNT 0 A A 0 C)[(0, 1)] == 0 &&
    (Mat.gemmTT 0 A A 0 C)[(0, 1)] == 0 && (Mat.gemmTN 0 A A 2 (mat 2 2))[(1, 1)] ==
      (2 : Float32) * (mat 2 2)[(1, 1)] &&
    (Mat.gemmTN 1 (mat 2 2) (mat 2 2) 0 C)[(0, 1)] == (mat 2 2)[(0, 0)] * (mat 2 2)[(0, 1)] +
      (mat 2 2)[(1, 0)] * (mat 2 2)[(1, 1)]

/-- Whether `gemmTN`, `gemmNT` and `gemmTT` update an unshared `C` in place. -/
def gemmTInPlace (m : Nat) : Bool :=
  let (p, C) := withAddr (mat m m 3)
  let (q, C') := withAddr (matLd m m 2 (m + 1) 3)
  let (r, C'') := withAddr (mat m m 4)
  BLASTest.addr (Mat.gemmTN 1 (mat m m 1) (mat m m 2) 1 C).data == p &&
    BLASTest.addr (Mat.gemmTT 1 (mat m m 1) (mat m m 2) 1 C').data == q &&
    BLASTest.addr (Mat.gemmNT 1 (mat m m 1) (mat m m 2) 1 C'').data == r

#guard gemmTInPlace 8

/-! ## `syrk` and `syrkT` -/

/-- Whether `(i, j)` is in the triangle `uplo`. -/
def inTri (uplo : Uplo) (i j : Nat) : Bool :=
  match uplo with
  | .upper => i ≤ j
  | .lower => j ≤ i

/-- The loops of the reference BLAS for `syrk`, with `trans = 'N'`, on an `Array`. -/
def syrkRef (uplo : Uplo) (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) : List Float32 :=
  Id.run do
  let mut c := C.toList.toArray
  if n == 0 || ((α == 0 || k == 0) && β == 1) then return c.toList
  let rows (j : Nat) := (List.range n).filter (inTri uplo · j)
  if α == 0 then
    for j in List.range n do
      for i in rows j do
        c := c.set! (i + n * j) (if β == 0 then 0 else β * c[i + n * j]!)
    return c.toList
  for j in List.range n do
    if β == 0 then
      for i in rows j do c := c.set! (i + n * j) 0
    else if β != 1 then
      for i in rows j do c := c.set! (i + n * j) (β * c[i + n * j]!)
    for l in List.range k do
      let ajl := A[(j, l)]?.getD 0
      if ajl != 0 then
        let t := α * ajl
        for i in rows j do
          c := c.set! (i + n * j) (c[i + n * j]! + t * (A[(i, l)]?.getD 0))
  return c.toList

/-- The loops of the reference BLAS for `syrk`, with `trans = 'T'`, on an `Array`. -/
def syrkTRef (uplo : Uplo) (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) : List Float32 :=
  Id.run do
  let mut c := C.toList.toArray
  if n == 0 || ((α == 0 || k == 0) && β == 1) then return c.toList
  let rows (j : Nat) := (List.range n).filter (inTri uplo · j)
  if α == 0 then
    for j in List.range n do
      for i in rows j do
        c := c.set! (i + n * j) (if β == 0 then 0 else β * c[i + n * j]!)
    return c.toList
  for j in List.range n do
    for i in rows j do
      let mut t : Float32 := 0
      for l in List.range k do
        t := t + (A[(l, i)]?.getD 0) * (A[(l, j)]?.getD 0)
      c := c.set! (i + n * j) (if β == 0 then α * t else α * t + β * c[i + n * j]!)
  return c.toList

/--
Whether `syrk` and `syrkT` match the reference loops, on packed operands and on operands with
offsets and leading dimensions, and leave the rest of `C`'s array unchanged.
-/
def syrkMatches (n k : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let ok₁ := (Mat.syrk uplo α (mat n k 1) β (mat n n 3)).toList ==
    syrkRef uplo α (mat n k 1) β (mat n n 3)
  let ok₂ := (Mat.syrkT uplo α (mat k n 1) β (mat n n 3)).toList ==
    syrkTRef uplo α (mat k n 1) β (mat n n 3)
  let C := matLd n n 4 (n + 3) 3
  let D := Mat.syrk uplo α (matLd n k 3 (n + 2) 1) β C
  let E := Mat.syrkT uplo α (matLd k n 1 (k + 1) 1) β C
  ok₁ && ok₂ && D.toList == syrkRef uplo α (mat n k 1) β (mat n n 3) &&
    E.toList == syrkTRef uplo α (mat k n 1) β (mat n n 3) &&
    outside D == outside C && outside E == outside C

#guard [Uplo.lower, .upper].all fun u =>
  syrkMatches 5 3 u 1.5 0.5 && syrkMatches 1 1 u 2 3 && syrkMatches 17 13 u (-0.25) 2 &&
    syrkMatches 40 7 u 1 1 && syrkMatches 5 3 u 0 0.5 && syrkMatches 5 3 u 1.5 0 &&
    syrkMatches 5 3 u 0 0 && syrkMatches 5 3 u 0 1 && syrkMatches 0 3 u 1 1 &&
    syrkMatches 3 0 u 1 1 && syrkMatches 3 0 u 2 0.5

-- `[[1, 2], [3, 4]] * [[1, 2], [3, 4]]ᵀ = [[5, 11], [11, 25]]`, on the lower triangle.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let C : Mat 2 2 := .ofPMat ⟨.ofList [0, 0, 7, 0], by decide⟩
  (Mat.syrk .lower 1 A 0 C).toList == [5, 11, 7, 25] &&
    (Mat.syrkT .upper 1 A 0 C).toList == [10, 0, 14, 20]

-- `syrk` skips the terms with `A[j, l] = 0`, so the infinity in `A[1, 0]` doesn't reach `C[1, 0]`.
#guard
  let A : Mat 2 1 := .ofPMat ⟨.ofList [0, 1 / 0], by decide⟩
  let C := Mat.syrk .lower 1 A 1 (mat 2 2 3)
  C[(1, 0)] == (mat 2 2 3)[(1, 0)] && C[(1, 1)] == 1 / 0

-- `syrkT` leaves `C` unchanged when `k = 0` and `β = 1`, even a `-0`.
#guard
  let C : Mat 1 1 := .ofFn fun _ _ => -0
  (Mat.syrkT .upper 2 (mat 0 1) 1 C)[(0, 0)].toBits == (-0 : Float32).toBits

-- `β = 0` sets the triangle to `0` without reading it, and `α = 0` doesn't read `A`.
#guard
  let nan : Float32 := 0 / 0
  let C : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.syrk .lower 0 A 0 C)[(1, 0)] == 0 && (Mat.syrkT .upper 0 A 0 C)[(0, 1)] == 0 &&
    (Mat.syrkT .upper 2 (mat 2 2) 0 C)[(0, 1)] ==
      (2 : Float32) * (Mat.syrkT .upper 1 (mat 2 2) 0 C)[(0, 1)]

/-- Whether `syrk` and `syrkT` update an unshared `C` in place. -/
def syrkInPlace (n : Nat) : Bool :=
  let (p, C) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, C') := withAddr (mat n n 3)
  BLASTest.addr (Mat.syrk .lower 1 (mat n 5 1) 1 C).data == p &&
    BLASTest.addr (Mat.syrkT .upper 1 (mat 5 n 1) 1 C').data == q

#guard syrkInPlace 8

/-! ## `trsm` and `trsmRight` -/

/-- A matrix with the elements of `mat n n s` in the triangle `uplo`, `n + 4 + i` on the diagonal,
and `other` elsewhere. -/
def triM (n : Nat) (s : Nat := 0) (other : Float32 := 0) (uplo : Uplo := .lower) : Mat n n :=
  .ofFn fun i j =>
    if i.val = j.val then (n + 4 + i.val).toFloat32
    else if inTri uplo i.val j.val then ((i.val * 7 + j.val * 13 + s) % 11).toFloat32 - 5
    else other

/-- The loops of the reference BLAS for `trsm`, with `side = 'L'` and `transa = 'N'`. -/
def trsmRef (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) : List Float32 :=
  Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  for j in List.range n do
    for i in List.range m do b := b.set! (i + m * j) (α * b[i + m * j]!)
    match uplo with
    | .upper =>
      for k in (List.range m).reverse do
        if d == .nonUnit then b := b.set! (k + m * j) (b[k + m * j]! / a k k)
        for i in List.range k do
          b := b.set! (i + m * j) (b[i + m * j]! - b[k + m * j]! * a i k)
    | .lower =>
      for k in List.range m do
        if d == .nonUnit then b := b.set! (k + m * j) (b[k + m * j]! / a k k)
        for i in (List.range m).filter (k < ·) do
          b := b.set! (i + m * j) (b[i + m * j]! - b[k + m * j]! * a i k)
  return b.toList

/-- The loops of the reference BLAS for `trsm`, with `side = 'R'` and `transa = 'N'`. -/
def trsmRightRef (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    List Float32 := Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let cols := match uplo with
    | .upper => List.range n
    | .lower => (List.range n).reverse
  for j in cols do
    for i in List.range m do b := b.set! (i + m * j) (α * b[i + m * j]!)
    let ks := match uplo with
      | .upper => List.range j
      | .lower => (List.range n).filter (j < ·)
    for k in ks do
      for i in List.range m do
        b := b.set! (i + m * j) (b[i + m * j]! - a k j * b[i + m * k]!)
    if d == .nonUnit then
      for i in List.range m do b := b.set! (i + m * j) (b[i + m * j]! / a j j)
  return b.toList

/-- `A` with `NaN`s outside the triangle `uplo`, and on the diagonal when it is unit. -/
def withNaNs (uplo : Uplo) (d : Diag) (n : Nat) : Mat n n :=
  let nan : Float32 := 0 / 0
  let A := triM n 1 nan uplo
  match d with
  | .nonUnit => A
  | .unit => .ofFn fun i j => if i.val = j.val then nan else A[(i.val, j.val)]

/-- `A` at the offset `2` with the leading dimension `n + 3`, in an array of `1e9 + 0.5`. -/
def ldOf (A : Mat n n) : Mat n n :=
  (Mat.ofLd? (Mat.ofFn (m := n + 3) (n := n) fun i j =>
    if h : i.val < n then A[(i.val, j.val)]'⟨h, j.isLt⟩ else 1e9 + 0.5).data 0 (n + 3)).getD A

/--
Whether `trsm` and `trsmRight` match the reference loops, on packed operands and on operands with
offsets and leading dimensions, don't read the other triangle (nor the diagonal when it is unit),
and leave the rest of `B`'s array unchanged.
-/
def trsmMatches (m n : Nat) (uplo : Uplo) (d : Diag) (α : Float32) : Bool :=
  let A := triM m 1 0 uplo
  let A' := triM n 1 0 uplo
  let B := mat m n 2
  let B' := matLd m n 3 (m + 2) 2
  let X := Mat.trsm uplo d α (ldOf (withNaNs uplo d m)) B'
  let Y := Mat.trsmRight uplo d α (ldOf (withNaNs uplo d n)) B'
  (Mat.trsm uplo d α A B).toList == trsmRef uplo d α A B &&
    (Mat.trsmRight uplo d α A' B).toList == trsmRightRef uplo d α A' B &&
    X.toList == trsmRef uplo d α A B && Y.toList == trsmRightRef uplo d α A' B &&
    outside X == outside B' && outside Y == outside B'

#guard [Uplo.lower, .upper].all fun u => [Diag.unit, .nonUnit].all fun d =>
  trsmMatches 5 3 u d 1.5 && trsmMatches 1 1 u d 2 && trsmMatches 17 9 u d (-0.25) &&
    trsmMatches 40 33 u d 1 && trsmMatches 0 3 u d 1 && trsmMatches 3 0 u d 1 &&
    trsmMatches 5 3 u d 0

-- `α = 0` sets `B` to `0` without reading `A` or `B`.
#guard
  let nan : Float32 := 0 / 0
  let B : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.trsm .lower .nonUnit 0 A B).toList == [0, 0, 0, 0] &&
    (Mat.trsmRight .upper .unit 0 A B).toList == [0, 0, 0, 0]

/-- The residuals `A * X - α * B` and `X * A - α * B` of the solves, by `gemm`: zero up to
rounding. -/
def trsmResidual (n : Nat) (uplo : Uplo) : Float32 :=
  let A := triM n 1 0 uplo
  let B := mat n 4 2
  let X := Mat.trsm uplo .nonUnit 2 A B
  let Y := Mat.trsmRight uplo .nonUnit 2 (triM 4 1 0 uplo) B
  let r := Mat.gemm 1 A X (-2) B
  let s := Mat.gemm 1 Y (triM 4 1 0 uplo) (-2) B
  (r.toList ++ s.toList).foldl (fun s v => max s v.abs) 0

#guard trsmResidual 50 .lower < 1e-4 && trsmResidual 50 .upper < 1e-4

/-- Whether `trsm` and `trsmRight` update an unshared `B` in place. -/
def trsmInPlace (n : Nat) : Bool :=
  let (p, B) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, B') := withAddr (mat n n 3)
  let (r, B'') := withAddr (mat n n 4)
  let (s, B₃) := withAddr (mat n n 5)
  BLASTest.addr (Mat.trsm .lower .nonUnit 1 (triM n) B).data == p &&
    BLASTest.addr (Mat.trsm .upper .unit 2 (triM n 0 0 .upper) B₃).data == s &&
    BLASTest.addr (Mat.trsmRight .upper .unit 2 (triM n 0 0 .upper) B').data == q &&
    BLASTest.addr (Mat.trsmRight .lower .nonUnit 2 (triM n) B'').data == r

#guard trsmInPlace 8

/-! ## `trsmT` and `trsmRightT` -/

/-- The loops of the reference BLAS for `trsm`, with `side = 'L'` and `transa = 'T'`. -/
def trsmTRef (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) : List Float32 :=
  Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  for j in List.range n do
    let rows := match uplo with
      | .upper => List.range m
      | .lower => (List.range m).reverse
    for i in rows do
      let mut t := α * b[i + m * j]!
      let ks := match uplo with
        | .upper => List.range i
        | .lower => (List.range m).filter (i < ·)
      for k in ks do
        t := t - a k i * b[k + m * j]!
      if d == .nonUnit then t := t / a i i
      b := b.set! (i + m * j) t
  return b.toList

/-- The loops of the reference BLAS for `trsm`, with `side = 'R'` and `transa = 'T'`. -/
def trsmRightTRef (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    List Float32 := Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let cols := match uplo with
    | .upper => (List.range n).reverse
    | .lower => List.range n
  for k in cols do
    if d == .nonUnit then
      for i in List.range m do b := b.set! (i + m * k) (b[i + m * k]! / a k k)
    let js := match uplo with
      | .upper => List.range k
      | .lower => (List.range n).filter (k < ·)
    for j in js do
      for i in List.range m do
        b := b.set! (i + m * j) (b[i + m * j]! - a j k * b[i + m * k]!)
    for i in List.range m do b := b.set! (i + m * k) (α * b[i + m * k]!)
  return b.toList

/--
Whether `trsmT` and `trsmRightT` match the reference loops, on packed operands and on operands with
offsets and leading dimensions, don't read the other triangle (nor the diagonal when it is unit),
and leave the rest of `B`'s array unchanged.
-/
def trsmTMatches (m n : Nat) (uplo : Uplo) (d : Diag) (α : Float32) : Bool :=
  let A := triM m 1 0 uplo
  let A' := triM n 1 0 uplo
  let B := mat m n 2
  let B' := matLd m n 3 (m + 2) 2
  let X := Mat.trsmT uplo d α (ldOf (withNaNs uplo d m)) B'
  let Y := Mat.trsmRightT uplo d α (ldOf (withNaNs uplo d n)) B'
  (Mat.trsmT uplo d α A B).toList == trsmTRef uplo d α A B &&
    (Mat.trsmRightT uplo d α A' B).toList == trsmRightTRef uplo d α A' B &&
    X.toList == trsmTRef uplo d α A B && Y.toList == trsmRightTRef uplo d α A' B &&
    outside X == outside B' && outside Y == outside B'

#guard [Uplo.lower, .upper].all fun u => [Diag.unit, .nonUnit].all fun d =>
  trsmTMatches 5 3 u d 1.5 && trsmTMatches 1 1 u d 2 && trsmTMatches 17 9 u d (-0.25) &&
    trsmTMatches 40 33 u d 1 && trsmTMatches 0 3 u d 1 && trsmTMatches 3 0 u d 1 &&
    trsmTMatches 5 3 u d 0

-- `α = 0` sets `B` to `0` without reading `A` or `B`.
#guard
  let nan : Float32 := 0 / 0
  let B : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.trsmT .lower .nonUnit 0 A B).toList == [0, 0, 0, 0] &&
    (Mat.trsmRightT .upper .unit 0 A B).toList == [0, 0, 0, 0]

/-- The residuals `Aᵀ * X - α * B` and `X * Aᵀ - α * B` of the solves, by the transposed `gemm`:
zero up to rounding. -/
def trsmTResidual (n : Nat) (uplo : Uplo) : Float32 :=
  let A := triM n 1 0 uplo
  let B := mat n 4 2
  let X := Mat.trsmT uplo .nonUnit 2 A B
  let Y := Mat.trsmRightT uplo .nonUnit 2 (triM 4 1 0 uplo) B
  let r := Mat.gemmTN 1 A X (-2) B
  let s := Mat.gemmNT 1 Y (triM 4 1 0 uplo) (-2) B
  (r.toList ++ s.toList).foldl (fun s v => max s v.abs) 0

#guard trsmTResidual 50 .lower < 1e-4 && trsmTResidual 50 .upper < 1e-4

/-- Whether `trsmT` and `trsmRightT` update an unshared `B` in place. -/
def trsmTInPlace (n : Nat) : Bool :=
  let (p, B) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, B') := withAddr (mat n n 3)
  let (r, B'') := withAddr (mat n n 4)
  let (s, B₃) := withAddr (mat n n 5)
  BLASTest.addr (Mat.trsmT .lower .nonUnit 1 (triM n) B).data == p &&
    BLASTest.addr (Mat.trsmT .upper .unit 2 (triM n 0 0 .upper) B₃).data == s &&
    BLASTest.addr (Mat.trsmRightT .upper .unit 2 (triM n 0 0 .upper) B').data == q &&
    BLASTest.addr (Mat.trsmRightT .lower .nonUnit 2 (triM n) B'').data == r

#guard trsmTInPlace 8

/-! ## `trmm`, `trmmT`, `trmmRight` and `trmmRightT` -/

/-- The loops of the reference BLAS for `trmm`, with `side = 'L'`. -/
def trmmRef (t : Bool) (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) :
    List Float32 := Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  for j in List.range n do
    match t, uplo with
    | false, .upper =>
      for k in List.range m do
        let mut tk := α * b[k + m * j]!
        for i in List.range k do
          b := b.set! (i + m * j) (b[i + m * j]! + tk * a i k)
        if d == .nonUnit then tk := tk * a k k
        b := b.set! (k + m * j) tk
    | false, .lower =>
      for k in (List.range m).reverse do
        let tk := α * b[k + m * j]!
        b := b.set! (k + m * j) tk
        if d == .nonUnit then b := b.set! (k + m * j) (b[k + m * j]! * a k k)
        for i in (List.range m).filter (k < ·) do
          b := b.set! (i + m * j) (b[i + m * j]! + tk * a i k)
    | true, .upper =>
      for i in (List.range m).reverse do
        let mut s := b[i + m * j]!
        if d == .nonUnit then s := s * a i i
        for k in List.range i do
          s := s + a k i * b[k + m * j]!
        b := b.set! (i + m * j) (α * s)
    | true, .lower =>
      for i in List.range m do
        let mut s := b[i + m * j]!
        if d == .nonUnit then s := s * a i i
        for k in (List.range m).filter (i < ·) do
          s := s + a k i * b[k + m * j]!
        b := b.set! (i + m * j) (α * s)
  return b.toList

/-- The loops of the reference BLAS for `trmm`, with `side = 'R'`. -/
def trmmRightRef (t : Bool) (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    List Float32 := Id.run do
  let mut b := B.toList.toArray
  if m == 0 || n == 0 then return b.toList
  if α == 0 then return b.toList.map fun _ => 0
  let a (i j : Nat) := A[(i, j)]?.getD 0
  if !t then
    let cols := match uplo with
      | .upper => (List.range n).reverse
      | .lower => List.range n
    for j in cols do
      let mut tj := α
      if d == .nonUnit then tj := tj * a j j
      for i in List.range m do b := b.set! (i + m * j) (tj * b[i + m * j]!)
      let ks := match uplo with
        | .upper => List.range j
        | .lower => (List.range n).filter (j < ·)
      for k in ks do
        let w := α * a k j
        for i in List.range m do
          b := b.set! (i + m * j) (b[i + m * j]! + w * b[i + m * k]!)
  else
    let cols := match uplo with
      | .upper => List.range n
      | .lower => (List.range n).reverse
    for k in cols do
      let js := match uplo with
        | .upper => List.range k
        | .lower => (List.range n).filter (k < ·)
      for j in js do
        let w := α * a j k
        for i in List.range m do
          b := b.set! (i + m * j) (b[i + m * j]! + w * b[i + m * k]!)
      let mut tk := α
      if d == .nonUnit then tk := tk * a k k
      if tk != 1 then
        for i in List.range m do b := b.set! (i + m * k) (tk * b[i + m * k]!)
  return b.toList

/-- The elements of `A` divided by `3`, so that the order of the sums changes their roundings. -/
def thirds (A : Mat n n) : Mat n n := .ofFn fun i j => A[(i.val, j.val)] / 3

/--
Whether the four `trmm` forms match the reference loops bit for bit, on packed operands and on
operands with offsets and leading dimensions, don't read the other triangle (nor the diagonal when
it is unit), and leave the rest of `B`'s array unchanged.
-/
def trmmMatches (m n : Nat) (uplo : Uplo) (d : Diag) (α : Float32) : Bool :=
  let A := thirds (triM m 1 0 uplo)
  let A' := thirds (triM n 1 0 uplo)
  let B := mat m n 2
  let B' := matLd m n 3 (m + 2) 2
  let N := ldOf (thirds (withNaNs uplo d m))
  let N' := ldOf (thirds (withNaNs uplo d n))
  let X := Mat.trmm uplo d α N B'
  let XT := Mat.trmmT uplo d α N B'
  let Y := Mat.trmmRight uplo d α N' B'
  let YT := Mat.trmmRightT uplo d α N' B'
  let r := trmmRef false uplo d α A B
  let rT := trmmRef true uplo d α A B
  let s := trmmRightRef false uplo d α A' B
  let sT := trmmRightRef true uplo d α A' B
  bits (Mat.trmm uplo d α A B) == listBits r && bits (Mat.trmmT uplo d α A B) == listBits rT &&
    bits (Mat.trmmRight uplo d α A' B) == listBits s &&
    bits (Mat.trmmRightT uplo d α A' B) == listBits sT &&
    bits X == listBits r && bits XT == listBits rT && bits Y == listBits s &&
    bits YT == listBits sT &&
    [X, XT, Y, YT].all fun Z => outside Z == outside B'

#guard [Uplo.lower, .upper].all fun u => [Diag.unit, .nonUnit].all fun d =>
  trmmMatches 5 3 u d 1.5 && trmmMatches 1 1 u d 2 && trmmMatches 17 9 u d (-0.25) &&
    trmmMatches 40 33 u d 1 && trmmMatches 0 3 u d 1 && trmmMatches 3 0 u d 1 &&
    trmmMatches 5 3 u d 0 && trmmMatches 6 4 u d (1 / 7)

-- `α = 0` sets `B` to `0` without reading `A` or `B`.
#guard
  let nan : Float32 := 0 / 0
  let B : Mat 2 2 := .ofFn fun _ _ => nan
  let A : Mat 2 2 := .ofFn fun _ _ => nan
  (Mat.trmm .lower .nonUnit 0 A B).toList == [0, 0, 0, 0] &&
    (Mat.trmmT .upper .unit 0 A B).toList == [0, 0, 0, 0] &&
    (Mat.trmmRight .upper .nonUnit 0 A B).toList == [0, 0, 0, 0] &&
    (Mat.trmmRightT .lower .unit 0 A B).toList == [0, 0, 0, 0]

/-- The products undo the solves of `trsm`: zero up to rounding. -/
def trmmResidual (n : Nat) (uplo : Uplo) : Float32 :=
  let A := triM n 1 0 uplo
  let A' := triM 4 1 0 uplo
  let B := mat n 4 2
  let r := Mat.trmm uplo .nonUnit 1 A (Mat.trsm uplo .nonUnit 2 A B)
  let rT := Mat.trmmT uplo .nonUnit 1 A (Mat.trsmT uplo .nonUnit 2 A B)
  let s := Mat.trmmRight uplo .nonUnit 1 A' (Mat.trsmRight uplo .nonUnit 2 A' B)
  let sT := Mat.trmmRightT uplo .nonUnit 1 A' (Mat.trsmRightT uplo .nonUnit 2 A' B)
  [r, rT, s, sT].foldl (fun s X => (X.toList.zip B.toList).foldl
    (fun s (x, y) => max s (x - 2 * y).abs) s) 0

#guard trmmResidual 50 .lower < 1e-4 && trmmResidual 50 .upper < 1e-4

/-- Whether the four `trmm` forms update an unshared `B` in place. -/
def trmmInPlace (n : Nat) : Bool :=
  let (p, B) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, B') := withAddr (mat n n 3)
  let (r, B'') := withAddr (mat n n 4)
  let (s, B₃) := withAddr (mat n n 5)
  BLASTest.addr (Mat.trmm .lower .nonUnit 1 (triM n) B).data == p &&
    BLASTest.addr (Mat.trmmT .upper .unit 2 (triM n 0 0 .upper) B₃).data == s &&
    BLASTest.addr (Mat.trmmRight .upper .unit 2 (triM n 0 0 .upper) B').data == q &&
    BLASTest.addr (Mat.trmmRightT .lower .nonUnit 2 (triM n) B'').data == r

#guard trmmInPlace 8

/-! ## `symm` and `symmRight` -/

/-- The loops of the reference BLAS for `symm`, with `side = 'L'` (or `'R'` when `right`). -/
def symmRef (right : Bool) (uplo : Uplo) (α : Float32) (A : Mat k k) (B : Mat m n) (β : Float32)
    (C : Mat m n) : List Float32 := Id.run do
  let mut c := C.toList.toArray
  if m == 0 || n == 0 || (α == 0 && β == 1) then return c.toList
  if α == 0 then
    return c.toList.map fun v => if β == 0 then 0 else β * v
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let b (i j : Nat) := B[(i, j)]?.getD 0
  if !right then
    for j in List.range n do
      let rows := match uplo with
        | .upper => List.range m
        | .lower => (List.range m).reverse
      for i in rows do
        let t1 := α * b i j
        let mut t2 := 0
        let ks := match uplo with
          | .upper => List.range i
          | .lower => (List.range m).filter (i < ·)
        for k in ks do
          c := c.set! (k + m * j) (c[k + m * j]! + t1 * a k i)
          t2 := t2 + b k j * a k i
        if β == 0 then c := c.set! (i + m * j) (t1 * a i i + α * t2)
        else c := c.set! (i + m * j) (β * c[i + m * j]! + t1 * a i i + α * t2)
  else
    for j in List.range n do
      let t1 := α * a j j
      for i in List.range m do
        if β == 0 then c := c.set! (i + m * j) (t1 * b i j)
        else c := c.set! (i + m * j) (β * c[i + m * j]! + t1 * b i j)
      for k in List.range j do
        let t := match uplo with
          | .upper => α * a k j
          | .lower => α * a j k
        for i in List.range m do c := c.set! (i + m * j) (c[i + m * j]! + t * b i k)
      for k in (List.range n).filter (j < ·) do
        let t := match uplo with
          | .upper => α * a j k
          | .lower => α * a k j
        for i in List.range m do c := c.set! (i + m * j) (c[i + m * j]! + t * b i k)
  return c.toList

/-- The elements of `mat m n s` divided by `3`. -/
def matThirds (m n : Nat) (s : Nat := 0) : Mat m n :=
  let A := mat m n s
  .ofFn fun i j => A[(i.val, j.val)] / 3

/-- The matrix `A` at the offset `3` with the leading dimension `m + 2`, in an array of
`1e9 + 0.5`. -/
def ldOf' (A : Mat m n) : Mat m n :=
  (Mat.ofLd? (Mat.ofFn (m := m + 2) (n := n) fun i j =>
    if h : i.val < m then A[(i.val, j.val)]'⟨h, j.isLt⟩ else 1e9 + 0.5).data 0 (m + 2)).getD A

/--
Whether `symm` and `symmRight` match the reference loops bit for bit, on packed operands and on
operands with offsets and leading dimensions, don't read the other triangle of `A`, nor `C` when
`β = 0`, and leave the rest of `C`'s array unchanged.
-/
def symmMatches (m n : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let A := thirds (triM m 1 0 uplo)
  let A' := thirds (triM n 1 0 uplo)
  let B := matThirds m n 2
  let C := matThirds m n 3
  let nan : Float32 := 0 / 0
  let C' := if β == 0 then ldOf' (Mat.ofFn (m := m) (n := n) fun _ _ => nan) else ldOf' C
  let N := ldOf (thirds (withNaNs uplo .nonUnit m))
  let N' := ldOf (thirds (withNaNs uplo .nonUnit n))
  let X := Mat.symm uplo α N (ldOf' B) β C'
  let Y := Mat.symmRight uplo α N' (ldOf' B) β C'
  let r := symmRef false uplo α A B β C
  let s := symmRef true uplo α A' B β C
  bits (Mat.symm uplo α A B β C) == listBits r && bits (Mat.symmRight uplo α A' B β C) ==
    listBits s && bits X == listBits r && bits Y == listBits s &&
    outside X == outside C' && outside Y == outside C'

#guard [Uplo.lower, .upper].all fun u =>
  symmMatches 5 3 u 1.5 0.5 && symmMatches 1 1 u 2 0 && symmMatches 17 9 u (-0.25) 1 &&
    symmMatches 40 33 u 1 (1 / 7) && symmMatches 0 3 u 1 1 && symmMatches 3 0 u 1 1 &&
    symmMatches 6 4 u (1 / 3) 0 && symmMatches 9 12 u 0.7 (-2)

-- `α = 0` only scales `C`, without reading `A` or `B`, nor `C` when `β = 0`.
#guard
  let nan : Float32 := 0 / 0
  let N : Mat 2 2 := .ofFn fun _ _ => nan
  let C : Mat 2 2 := .ofFn fun i j => (i.val + 2 * j.val).toFloat32
  (Mat.symm .lower 0 N N 0 N).toList == [0, 0, 0, 0] &&
    (Mat.symmRight .upper 0 N N 0 N).toList == [0, 0, 0, 0] &&
    (Mat.symm .upper 0 N N 3 C).toList == [0, 3, 6, 9] &&
    (Mat.symmRight .lower 0 N N 1 C).toList == C.toList

/-- The products against `gemm` with the full symmetric matrix: zero up to rounding. -/
def symmResidual (m n : Nat) (uplo : Uplo) : Float32 :=
  let S (k : Nat) : Mat k k := .ofFn fun i j =>
    let T := triM k 1 0 .upper
    (if i.val ≤ j.val then T[(i.val, j.val)] else T[(j.val, i.val)]) / 3
  let B := matThirds m n 2
  let C := matThirds m n 3
  let r := Mat.symm uplo 1.5 (S m) B 0.5 C
  let s := Mat.symmRight uplo 1.5 (S n) B 0.5 C
  let r' := Mat.gemm 1.5 (S m) B 0.5 C
  let s' := Mat.gemm 1.5 B (S n) 0.5 C
  ((r.toList.zip r'.toList) ++ (s.toList.zip s'.toList)).foldl
    (fun s (x, y) => max s (x - y).abs) 0

#guard symmResidual 30 20 .lower < 1e-4 && symmResidual 30 20 .upper < 1e-4

/-- Whether `symm` and `symmRight` update an unshared `C` in place. -/
def symmInPlace (n : Nat) : Bool :=
  let (p, C) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, C') := withAddr (mat n n 3)
  let (r, C'') := withAddr (mat n n 4)
  let (s, C₃) := withAddr (mat n n 5)
  BLASTest.addr (Mat.symm .lower 1 (triM n) (mat n n 1) 1 C).data == p &&
    BLASTest.addr (Mat.symm .upper 2 (triM n 0 0 .upper) (mat n n 1) 0 C₃).data == s &&
    BLASTest.addr (Mat.symmRight .upper 2 (triM n 0 0 .upper) (mat n n 1) 1 C').data == q &&
    BLASTest.addr (Mat.symmRight .lower 2 (triM n) (mat n n 1) 0.5 C'').data == r

#guard symmInPlace 8

/-! ## `syr2k` and `syr2kT` -/

/-- The loops of the reference BLAS for `syr2k`, with `trans = 'N'` (or `'T'` when `t`). -/
def syr2kRef (t : Bool) (uplo : Uplo) (α : Float32) (A B : Mat p q) (β : Float32) (C : Mat n n) :
    List Float32 := Id.run do
  let k := if t then p else q
  let mut c := C.toList.toArray
  if n == 0 || ((α == 0 || k == 0) && β == 1) then return c.toList
  let rows (j : Nat) := (List.range n).filter (inTri uplo · j)
  if α == 0 then
    for j in List.range n do
      for i in rows j do
        c := c.set! (i + n * j) (if β == 0 then 0 else β * c[i + n * j]!)
    return c.toList
  let a (i j : Nat) := A[(i, j)]?.getD 0
  let b (i j : Nat) := B[(i, j)]?.getD 0
  for j in List.range n do
    if !t then
      if β == 0 then
        for i in rows j do c := c.set! (i + n * j) 0
      else if β != 1 then
        for i in rows j do c := c.set! (i + n * j) (β * c[i + n * j]!)
      for l in List.range k do
        if a j l != 0 || b j l != 0 then
          let t₁ := α * b j l
          let t₂ := α * a j l
          for i in rows j do
            c := c.set! (i + n * j) (c[i + n * j]! + a i l * t₁ + b i l * t₂)
    else
      for i in rows j do
        let mut t₁ : Float32 := 0
        let mut t₂ : Float32 := 0
        for l in List.range k do
          t₁ := t₁ + a l i * b l j
          t₂ := t₂ + b l i * a l j
        c := c.set! (i + n * j)
          (if β == 0 then α * t₁ + α * t₂ else β * c[i + n * j]! + α * t₁ + α * t₂)
  return c.toList

/--
Whether `syr2k` and `syr2kT` match the reference loops bit for bit, on packed operands and on
operands with leading dimensions, don't read `C` when `β = 0`, and leave the other triangle and the
rest of `C`'s array unchanged.
-/
def syr2kMatches (n k : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let nan : Float32 := 0 / 0
  let A := matThirds n k 1
  let B := matThirds n k 4
  let AT := matThirds k n 1
  let BT := matThirds k n 4
  let C₃ := matThirds n n 3
  let C : Mat n n := .ofFn fun i j =>
    if inTri uplo i.val j.val then C₃[(i.val, j.val)] else nan
  let C₀ : Mat n n := .ofFn fun i j =>
    if inTri uplo i.val j.val && β == 0 then nan else C[(i.val, j.val)]
  let r := syr2kRef false uplo α A B β C
  let rT := syr2kRef true uplo α AT BT β C
  let D := Mat.syr2k uplo α (ldOf' A) (ldOf' B) β (ldOf' C₀)
  let E := Mat.syr2kT uplo α (ldOf' AT) (ldOf' BT) β (ldOf' C₀)
  bits (Mat.syr2k uplo α A B β C) == listBits r &&
    bits (Mat.syr2kT uplo α AT BT β C) == listBits rT &&
    bits D == listBits r && bits E == listBits rT &&
    outside D == outside (ldOf' C₀) && outside E == outside (ldOf' C₀)

#guard [Uplo.lower, .upper].all fun u =>
  syr2kMatches 5 3 u 1.5 0.5 && syr2kMatches 1 1 u 2 3 && syr2kMatches 17 13 u (-0.25) 2 &&
    syr2kMatches 40 7 u 1 1 && syr2kMatches 5 3 u 0 0.5 && syr2kMatches 5 3 u (1 / 3) 0 &&
    syr2kMatches 5 3 u 0 0 && syr2kMatches 5 3 u 0 1 && syr2kMatches 0 3 u 1 1 &&
    syr2kMatches 3 0 u 1 1 && syr2kMatches 3 0 u 2 0.5 && syr2kMatches 33 20 u (1 / 7) 0

-- `syr2k` skips the terms with `A[j, l] = B[j, l] = 0`, so the infinities in `A[1, 0]` and
-- `B[1, 0]` don't reach `C[1, 0]`.
#guard
  let A : Mat 2 1 := .ofPMat ⟨.ofList [0, 1 / 0], by decide⟩
  let C := Mat.syr2k .lower 1 A A 1 (mat 2 2 3)
  C[(1, 0)] == (mat 2 2 3)[(1, 0)] && C[(1, 1)] == 1 / 0

-- `syr2kT` leaves `C` unchanged when `k = 0` and `β = 1`, even a `-0`.
#guard
  let C : Mat 1 1 := .ofFn fun _ _ => -0
  (Mat.syr2kT .upper 2 (mat 0 1) (mat 0 1) 1 C)[(0, 0)].toBits == (-0 : Float32).toBits

/-- The products against `gemm`: zero up to rounding. -/
def syr2kResidual (n k : Nat) (uplo : Uplo) : Float32 :=
  let A := matThirds n k 1
  let B := matThirds n k 4
  let C := matThirds n n 3
  let g := Mat.gemm 1.5 B (Mat.transpose A) 1 (Mat.gemm 1.5 A (Mat.transpose B) 0.5 C)
  let D := Mat.syr2k uplo 1.5 A B 0.5 C
  let E := Mat.syr2kT uplo 1.5 (Mat.transpose A) (Mat.transpose B) 0.5 C
  (List.range n).foldl (fun s j => (List.range n).foldl (fun s i =>
    if inTri uplo i j then max s (max ((D[(i, j)]?.getD 0) - (g[(i, j)]?.getD 0)).abs
      ((E[(i, j)]?.getD 0) - (g[(i, j)]?.getD 0)).abs) else s) s) 0

#guard syr2kResidual 30 20 .lower < 1e-4 && syr2kResidual 30 20 .upper < 1e-4

/-- Whether `syr2k` and `syr2kT` update an unshared `C` in place. -/
def syr2kInPlace (n : Nat) : Bool :=
  let (p, C) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, C') := withAddr (mat n n 3)
  BLASTest.addr (Mat.syr2k .lower 1 (mat n 5 1) (mat n 5 2) 1 C).data == p &&
    BLASTest.addr (Mat.syr2kT .upper 1 (mat 5 n 1) (mat 5 n 2) 1 C').data == q

#guard syr2kInPlace 8

/-! ## `gemmtr`, `gemmtrTN`, `gemmtrNT` and `gemmtrTT` -/

/-- The loops of the reference BLAS for `gemmtr`, with `transa = 'T'` when `ta` and `transb = 'T'`
when `tb`. -/
def gemmtrRef (ta tb : Bool) (uplo : Uplo) (α : Float32) (A : Mat p q) (B : Mat r s) (β : Float32)
    (C : Mat n n) : List Float32 := Id.run do
  let k := if ta then p else q
  let mut c := C.toList.toArray
  if n == 0 then return c.toList
  let rows (j : Nat) := (List.range n).filter (inTri uplo · j)
  if α == 0 then
    for j in List.range n do
      for i in rows j do
        c := c.set! (i + n * j) (if β == 0 then 0 else β * c[i + n * j]!)
    return c.toList
  let a (i l : Nat) := if ta then A[(l, i)]?.getD 0 else A[(i, l)]?.getD 0
  let b (l j : Nat) := if tb then B[(j, l)]?.getD 0 else B[(l, j)]?.getD 0
  for j in List.range n do
    if !ta then
      if β == 0 then
        for i in rows j do c := c.set! (i + n * j) 0
      else if β != 1 then
        for i in rows j do c := c.set! (i + n * j) (β * c[i + n * j]!)
      for l in List.range k do
        let t := α * b l j
        for i in rows j do c := c.set! (i + n * j) (c[i + n * j]! + t * a i l)
    else
      for i in rows j do
        let mut t : Float32 := 0
        for l in List.range k do t := t + a i l * b l j
        c := c.set! (i + n * j) (if β == 0 then α * t else α * t + β * c[i + n * j]!)
  return c.toList

/--
Whether the four `gemmtr` forms match the reference loops bit for bit, on packed operands and on
operands with leading dimensions, don't read `C` when `β = 0`, and leave the other triangle and the
rest of `C`'s array unchanged.
-/
def gemmtrMatches (n k : Nat) (uplo : Uplo) (α β : Float32) : Bool :=
  let nan : Float32 := 0 / 0
  let A := matThirds n k 1
  let AT := matThirds k n 1
  let B := matThirds k n 4
  let BT := matThirds n k 4
  let C₃ := matThirds n n 3
  let C : Mat n n := .ofFn fun i j =>
    if inTri uplo i.val j.val then C₃[(i.val, j.val)] else nan
  let C₀ : Mat n n := .ofFn fun i j =>
    if inTri uplo i.val j.val && β == 0 then nan else C[(i.val, j.val)]
  let r := gemmtrRef false false uplo α A B β C
  let rTN := gemmtrRef true false uplo α AT B β C
  let rNT := gemmtrRef false true uplo α A BT β C
  let rTT := gemmtrRef true true uplo α AT BT β C
  let Ds := [Mat.gemmtr uplo α (ldOf' A) (ldOf' B) β (ldOf' C₀),
    Mat.gemmtrTN uplo α (ldOf' AT) (ldOf' B) β (ldOf' C₀),
    Mat.gemmtrNT uplo α (ldOf' A) (ldOf' BT) β (ldOf' C₀),
    Mat.gemmtrTT uplo α (ldOf' AT) (ldOf' BT) β (ldOf' C₀)]
  bits (Mat.gemmtr uplo α A B β C) == listBits r &&
    bits (Mat.gemmtrTN uplo α AT B β C) == listBits rTN &&
    bits (Mat.gemmtrNT uplo α A BT β C) == listBits rNT &&
    bits (Mat.gemmtrTT uplo α AT BT β C) == listBits rTT &&
    (Ds.map bits) == [r, rTN, rNT, rTT].map listBits &&
    Ds.all fun D => outside D == outside (ldOf' C₀)

#guard [Uplo.lower, .upper].all fun u =>
  gemmtrMatches 5 3 u 1.5 0.5 && gemmtrMatches 1 1 u 2 3 && gemmtrMatches 17 13 u (-0.25) 2 &&
    gemmtrMatches 40 7 u 1 1 && gemmtrMatches 5 3 u 0 0.5 && gemmtrMatches 5 3 u (1 / 3) 0 &&
    gemmtrMatches 5 3 u 0 0 && gemmtrMatches 5 3 u 0 1 && gemmtrMatches 0 3 u 1 1 &&
    gemmtrMatches 3 0 u 1 1 && gemmtrMatches 3 0 u 2 0.5 && gemmtrMatches 33 20 u (1 / 7) 0

-- Unlike `syrkT`, the reference `gemmtr` has no quick return for `k = 0` and `β = 1`: with
-- `transa = 'T'`, it writes `α * 0 + 1 * C[i, j]`, which turns a `-0` into `0`.
#guard
  let C : Mat 1 1 := .ofFn fun _ _ => -0
  (Mat.gemmtrTN .upper 2 (mat 0 1) (mat 0 1) 1 C)[(0, 0)].toBits == (0 : Float32).toBits &&
    (Mat.gemmtr .upper 2 (mat 1 0) (mat 0 1) 1 C)[(0, 0)].toBits == (-0 : Float32).toBits

/-- The products against `gemm`: zero up to rounding. -/
def gemmtrResidual (n k : Nat) (uplo : Uplo) : Float32 :=
  let A := matThirds n k 1
  let B := matThirds k n 4
  let C := matThirds n n 3
  let g := Mat.gemm 1.5 A B 0.5 C
  let Ds := [Mat.gemmtr uplo 1.5 A B 0.5 C, Mat.gemmtrTN uplo 1.5 (Mat.transpose A) B 0.5 C,
    Mat.gemmtrNT uplo 1.5 A (Mat.transpose B) 0.5 C,
    Mat.gemmtrTT uplo 1.5 (Mat.transpose A) (Mat.transpose B) 0.5 C]
  Ds.foldl (fun s D => (List.range n).foldl (fun s j => (List.range n).foldl (fun s i =>
    if inTri uplo i j then max s ((D[(i, j)]?.getD 0) - (g[(i, j)]?.getD 0)).abs else s) s) s) 0

#guard gemmtrResidual 30 20 .lower < 1e-4 && gemmtrResidual 30 20 .upper < 1e-4

/-- Whether `gemmtr` and `gemmtrTN` update an unshared `C` in place. -/
def gemmtrInPlace (n : Nat) : Bool :=
  let (p, C) := withAddr (matLd n n 2 (n + 1) 3)
  let (q, C') := withAddr (mat n n 3)
  BLASTest.addr (Mat.gemmtr .lower 1 (mat n 5 1) (mat 5 n 2) 1 C).data == p &&
    BLASTest.addr (Mat.gemmtrTN .upper 1 (mat 5 n 1) (mat 5 n 2) 1 C').data == q

#guard gemmtrInPlace 8
