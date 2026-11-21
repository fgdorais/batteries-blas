/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.View
public import BLAS.Float64.Gbmv
public import BLAS.Float64.Sbmv
public import BLAS.Float64.Tbmv
public import BLAS.Float64.Tbsv

/-!
# Band views

The views of a matrix `A` that holds a band matrix in the band storage of the reference BLAS, for
`blas%`: `A.band m kl ku` (`Band`) is the general `m × n` band matrix with `kl` subdiagonals and
`ku` superdiagonals in `A : Mat (kl + ku + 1) n`, which selects `gbmv`, and `gbmvT` for its
transpose; `A.upperBand`, `A.unitLowerBand`, … (`TriBand`) are the triangular band matrices with
`k` off-diagonals in `A : Mat (k + 1) n`, which select `tbmv` and `tbsv`, and `tbmvT` and `tbsvT`
for their transposes; and `A.symUpperBand` and `A.symLowerBand` (`SymBand`) are the symmetric band
matrices, which select `sbmv`. As for the other views, a view is the matrix itself, with no copy.

The element `i, j` of a view is the element of the band matrix, from its storage: `0` outside the
band, `1` on a unit diagonal, and, for a symmetric band matrix, the element `j, i` of the stored
triangle outside it.
-/

open ScalarArray

namespace BLAS.Float64

/-! ## General band matrices -/

/--
The `m × n` band matrix with `kl` subdiagonals and `ku` superdiagonals stored in `mat`: row
`ku + i - j` of column `j` of `mat` holds the element `i, j`, for `j - ku ≤ i ≤ j + kl`.
-/
public structure Band (m kl ku n : Nat) where
  /-- The band storage. -/
  mat : Mat (kl + ku + 1) n

/--
The triangular band matrix with `k` off-diagonals stored by its triangle `uplo` in `mat`, with a
unit diagonal if `d` is `.unit`: row `k + i - j` (upper) or `i - j` (lower) of column `j` of `mat`
holds the element `i, j`. The routines read only the band, and not the diagonal when it is unit.
-/
public structure TriBand (uplo : Uplo) (d : Diag) (k n : Nat) where
  /-- The band storage. -/
  mat : Mat (k + 1) n

/--
The symmetric band matrix with `k` off-diagonals stored by its triangle `uplo` in `mat`, as for
`TriBand`. The routines read only the band of the triangle.
-/
public structure SymBand (uplo : Uplo) (k n : Nat) where
  /-- The band storage. -/
  mat : Mat (k + 1) n

namespace Mat

variable {k n : Nat}

/-- The `m × n` band matrix with `kl` subdiagonals and `ku` superdiagonals stored in `A`. -/
@[expose] public def band (m kl ku : Nat) (A : Mat (kl + ku + 1) n) : Band m kl ku n := ⟨A⟩

/-- The upper triangular band matrix stored in `A`, with its diagonal. -/
@[expose] public def upperBand (A : Mat (k + 1) n) : TriBand .upper .nonUnit k n := ⟨A⟩

/-- The lower triangular band matrix stored in `A`, with its diagonal. -/
@[expose] public def lowerBand (A : Mat (k + 1) n) : TriBand .lower .nonUnit k n := ⟨A⟩

/-- The upper triangular band matrix stored in `A`, with a unit diagonal, which isn't read. -/
@[expose] public def unitUpperBand (A : Mat (k + 1) n) : TriBand .upper .unit k n := ⟨A⟩

/-- The lower triangular band matrix stored in `A`, with a unit diagonal, which isn't read. -/
@[expose] public def unitLowerBand (A : Mat (k + 1) n) : TriBand .lower .unit k n := ⟨A⟩

/-- The symmetric band matrix with the upper triangle stored in `A`. -/
@[expose] public def symUpperBand (A : Mat (k + 1) n) : SymBand .upper k n := ⟨A⟩

/-- The symmetric band matrix with the lower triangle stored in `A`. -/
@[expose] public def symLowerBand (A : Mat (k + 1) n) : SymBand .lower k n := ⟨A⟩

@[simp] public theorem band_eq (m kl ku : Nat) (A : Mat (kl + ku + 1) n) :
    A.band m kl ku = Band.mk A := rfl

@[simp] public theorem upperBand_eq (A : Mat (k + 1) n) : A.upperBand = TriBand.mk A := rfl

@[simp] public theorem lowerBand_eq (A : Mat (k + 1) n) : A.lowerBand = TriBand.mk A := rfl

@[simp] public theorem unitUpperBand_eq (A : Mat (k + 1) n) : A.unitUpperBand = TriBand.mk A :=
  rfl

@[simp] public theorem unitLowerBand_eq (A : Mat (k + 1) n) : A.unitLowerBand = TriBand.mk A :=
  rfl

@[simp] public theorem symUpperBand_eq (A : Mat (k + 1) n) : A.symUpperBand = SymBand.mk A := rfl

@[simp] public theorem symLowerBand_eq (A : Mat (k + 1) n) : A.symLowerBand = SymBand.mk A := rfl

end Mat

/-! ## Elements -/

/-- `B[(i, j)]` is the element of the band matrix: its stored element in the band, else `0`. -/
public instance {m kl ku n : Nat} : GetElem (Band m kl ku n) (Nat × Nat) Float
    fun _ p => p.1 < m ∧ p.2 < n where
  getElem B p h :=
    if h' : p.2 ≤ p.1 + ku ∧ p.1 ≤ p.2 + kl then B.mat[(ku + p.1 - p.2, p.2)]'⟨by lia, h.2⟩
    else 0

/--
`T[(i, j)]` is the element of the triangular band matrix: its stored element in the band, `1` on
a unit diagonal, and `0` outside the band.
-/
public instance {uplo : Uplo} {d : Diag} {k n : Nat} : GetElem (TriBand uplo d k n) (Nat × Nat)
    Float fun _ p => p.1 < n ∧ p.2 < n where
  getElem T p h :=
    if p.1 = p.2 ∧ d = .unit then 1
    else match uplo with
      | .upper => if h' : p.1 ≤ p.2 ∧ p.2 ≤ p.1 + k then T.mat[(k + p.1 - p.2, p.2)]'⟨by lia, h.2⟩
        else 0
      | .lower => if h' : p.2 ≤ p.1 ∧ p.1 ≤ p.2 + k then T.mat[(p.1 - p.2, p.2)]'⟨by lia, h.2⟩
        else 0

/--
`S[(i, j)]` is the element of the symmetric band matrix: the stored element `i, j` in the band of
the triangle, the element `j, i` in the band of the other triangle, and `0` outside the band.
-/
public instance {uplo : Uplo} {k n : Nat} : GetElem (SymBand uplo k n) (Nat × Nat) Float
    fun _ p => p.1 < n ∧ p.2 < n where
  getElem S p h :=
    if h' : max p.1 p.2 ≤ min p.1 p.2 + k then
      match uplo with
      | .upper => S.mat[(k + min p.1 p.2 - max p.1 p.2, max p.1 p.2)]'⟨by lia, by lia⟩
      | .lower => S.mat[(max p.1 p.2 - min p.1 p.2, min p.1 p.2)]'⟨by lia, by lia⟩
    else 0

/-! ## Instances -/

/-- `α * B * x + β * y` is `gbmv`. -/
public instance {m kl ku n : Nat} : MulAdd Float (Band m kl ku n) (Vec n) (Vec m) where
  run α B x β y := Mat.gbmv kl ku α B.mat x β y

/-- `α * Bᵀ * x + β * y` is `gbmvT`. -/
public instance {m kl ku n : Nat} :
    MulAdd Float (Transpose (Band m kl ku n)) (Vec m) (Vec n) where
  run α B x β y := Mat.gbmvT kl ku α B.mat.mat x β y

/-- `α * S * x + β * y` is `sbmv`. -/
public instance {uplo : Uplo} {k n : Nat} : MulAdd Float (SymBand uplo k n) (Vec n) (Vec n) where
  run α S x β y := Mat.sbmv uplo α S.mat x β y

/-- `T * x` is `tbmv`. -/
public instance {uplo : Uplo} {d : Diag} {k n : Nat} : MulIn (TriBand uplo d k n) (Vec n) where
  run T x := Mat.tbmv uplo d T.mat x

/-- `Tᵀ * x` is `tbmvT`. -/
public instance {uplo : Uplo} {d : Diag} {k n : Nat} :
    MulIn (Transpose (TriBand uplo d k n)) (Vec n) where
  run T x := Mat.tbmvT uplo d T.mat.mat x

/-- `T⁻¹ * x` is `tbsv`. -/
public instance {uplo : Uplo} {d : Diag} {k n : Nat} : Solve (TriBand uplo d k n) (Vec n) where
  run T x := Mat.tbsv uplo d T.mat x

/-- `Tᵀ⁻¹ * x` is `tbsvT`. -/
public instance {uplo : Uplo} {d : Diag} {k n : Nat} :
    Solve (Transpose (TriBand uplo d k n)) (Vec n) where
  run T x := Mat.tbsvT uplo d T.mat.mat x

/-! ## The routines of the instances -/

section

variable {m kl ku k n : Nat} {uplo : Uplo} {d : Diag}

@[simp] public theorem mulAdd_band_vec (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) :
    MulAdd.run α (Band.mk (m := m) A) x β y = Mat.gbmv kl ku α A x β y := rfl

@[simp] public theorem mulAdd_transpose_band_vec (α : Float) (A : Mat (kl + ku + 1) n)
    (x : Vec m) (β : Float) (y : Vec n) :
    MulAdd.run α (Transpose.mk (Band.mk (m := m) A)) x β y = Mat.gbmvT kl ku α A x β y := rfl

@[simp] public theorem mulAdd_symBand_vec (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) :
    MulAdd.run α (SymBand.mk (uplo := uplo) A) x β y = Mat.sbmv uplo α A x β y := rfl

@[simp] public theorem mulIn_triBand_vec (A : Mat (k + 1) n) (x : Vec n) :
    MulIn.run (TriBand.mk (uplo := uplo) (d := d) A) x = Mat.tbmv uplo d A x := rfl

@[simp] public theorem mulIn_transpose_triBand_vec (A : Mat (k + 1) n) (x : Vec n) :
    MulIn.run (Transpose.mk (TriBand.mk (uplo := uplo) (d := d) A)) x = Mat.tbmvT uplo d A x :=
  rfl

@[simp] public theorem solve_triBand_vec (A : Mat (k + 1) n) (x : Vec n) :
    Solve.run (TriBand.mk (uplo := uplo) (d := d) A) x = Mat.tbsv uplo d A x := rfl

@[simp] public theorem solve_transpose_triBand_vec (A : Mat (k + 1) n) (x : Vec n) :
    Solve.run (Transpose.mk (TriBand.mk (uplo := uplo) (d := d) A)) x = Mat.tbsvT uplo d A x :=
  rfl

end

end BLAS.Float64
