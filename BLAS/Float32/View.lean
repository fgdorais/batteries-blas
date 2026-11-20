/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Ops
public import BLAS.Float32.Level1
public import BLAS.Float32.Level2
public import BLAS.Float32.Trsv
public import BLAS.Float32.Gemm
public import BLAS.Float32.Trsm
public import BLAS.Float32.GemmT
public import BLAS.Float32.TrsvT
public import BLAS.Float32.TrsmT
public import BLAS.Float32.Trmv
public import BLAS.Float32.Trmm
public import BLAS.Float32.TrmmRight
public import BLAS.Float32.Symv
public import BLAS.Float32.Symm
public import BLAS.Float32.Syr
public import BLAS.Float32.Syrk
public import BLAS.Float32.Syr2k
public import BLAS.Float32.Gemmtr

/-!
# Views

The views of a matrix select a routine and its options from the kinds of its operands, in place of
the flags of the reference BLAS: `Aᵀ` (`Transpose`) selects the transposed routines,
`A.lower`, `A.unitUpper`, … (`Tri`) select a triangle and a diagonal, and `A.symLower` and
`A.symUpper` (`Sym`) select the symmetric routines and the triangle they read. A view is the matrix
itself, with no copy.

A triangle `C.lower` is also the target of the routines that update only one triangle of a square
matrix: `syr`, `syr2`, `syrk`, `syr2k` and `gemmtr`.

## Instances

The instances of the classes of `BLAS.Ops` on vectors, matrices and views, which `blas%` expands
to, each with a `simp` lemma that unfolds it to its routine. So the specifications of the routines,
such as `getElem_gemv`, apply to the expansions of `blas%` with no new proofs.
-/

open ScalarArray

namespace BLAS.Float32

/-! ## Transposes -/

/-- `Aᵀ[(i, j)]` is `A[(j, i)]`. -/
public instance {m n : Nat} : GetElem (Transpose (Mat m n)) (Nat × Nat) Float32
    fun _ p => p.1 < n ∧ p.2 < m where
  getElem T p h := T.mat[(p.2, p.1)]'⟨h.2, h.1⟩

@[simp] public theorem getElem_transpose {m n : Nat} (A : Mat m n) (i j : Nat)
    (h : i < n ∧ j < m) : (Transpose.mk A)[(i, j)] = A[(j, i)]'⟨h.2, h.1⟩ := rfl

/-! ## Triangles -/

/--
The triangle `uplo` of the square matrix `mat`, with a unit diagonal if `d` is `.unit`, with no
copy. The routines read only the triangle, and not the diagonal when it is unit.
-/
public structure Tri (uplo : Uplo) (d : Diag) (n : Nat) where
  /-- The matrix that holds the triangle. -/
  mat : Mat n n

namespace Mat

variable {n : Nat}

/-- The upper triangle of `A`, with its diagonal. -/
@[expose] public def upper (A : Mat n n) : Tri .upper .nonUnit n := ⟨A⟩

/-- The lower triangle of `A`, with its diagonal. -/
@[expose] public def lower (A : Mat n n) : Tri .lower .nonUnit n := ⟨A⟩

/-- The upper triangle of `A`, with a unit diagonal, which the routines don't read. -/
@[expose] public def unitUpper (A : Mat n n) : Tri .upper .unit n := ⟨A⟩

/-- The lower triangle of `A`, with a unit diagonal, which the routines don't read. -/
@[expose] public def unitLower (A : Mat n n) : Tri .lower .unit n := ⟨A⟩

@[simp] public theorem upper_eq (A : Mat n n) : A.upper = Tri.mk A := rfl

@[simp] public theorem lower_eq (A : Mat n n) : A.lower = Tri.mk A := rfl

@[simp] public theorem unitUpper_eq (A : Mat n n) : A.unitUpper = Tri.mk A := rfl

@[simp] public theorem unitLower_eq (A : Mat n n) : A.unitLower = Tri.mk A := rfl

end Mat

/--
`T[(i, j)]` is the element of the triangular matrix: `A[(i, j)]` in the triangle, `1` on a unit
diagonal, and `0` outside the triangle.
-/
public instance {uplo : Uplo} {d : Diag} {n : Nat} : GetElem (Tri uplo d n) (Nat × Nat) Float32
    fun _ p => p.1 < n ∧ p.2 < n where
  getElem T p h :=
    if p.1 = p.2 then (if d = .unit then 1 else T.mat[p]'h)
    else if (uplo = .upper ∧ p.1 < p.2) ∨ (uplo = .lower ∧ p.2 < p.1) then T.mat[p]'h
    else 0

/-! ## Symmetric matrices -/

/--
The symmetric matrix with the triangle `uplo` of the square matrix `mat`, with no copy. The
routines read only the triangle.
-/
public structure Sym (uplo : Uplo) (n : Nat) where
  /-- The matrix that holds the triangle. -/
  mat : Mat n n

namespace Mat

variable {n : Nat}

/-- The symmetric matrix with the upper triangle of `A`. -/
@[expose] public def symUpper (A : Mat n n) : Sym .upper n := ⟨A⟩

/-- The symmetric matrix with the lower triangle of `A`. -/
@[expose] public def symLower (A : Mat n n) : Sym .lower n := ⟨A⟩

@[simp] public theorem symUpper_eq (A : Mat n n) : A.symUpper = Sym.mk A := rfl

@[simp] public theorem symLower_eq (A : Mat n n) : A.symLower = Sym.mk A := rfl

end Mat

/--
`S[(i, j)]` is the element of the symmetric matrix: `A[(i, j)]` in the triangle and on the
diagonal, and `A[(j, i)]` outside the triangle.
-/
public instance {uplo : Uplo} {n : Nat} : GetElem (Sym uplo n) (Nat × Nat) Float32
    fun _ p => p.1 < n ∧ p.2 < n where
  getElem S p h :=
    if (uplo = .upper ∧ p.1 ≤ p.2) ∨ (uplo = .lower ∧ p.2 ≤ p.1) then S.mat[p]'h
    else S.mat[(p.2, p.1)]'⟨h.2, h.1⟩

/-! ## Instances -/

/-- `α * A * x + β * y` is `gemv`. -/
public instance {m n : Nat} : MulAdd Float32 (Mat m n) (Vec n) (Vec m) where
  run := Mat.gemv

/-- `α * Aᵀ * x + β * y` is `gemvT`. -/
public instance {m n : Nat} : MulAdd Float32 (Transpose (Mat m n)) (Vec m) (Vec n) where
  run α T x β y := Mat.gemvT α T.mat x β y

/-- `α * A * B + β * C` is `gemm`. -/
public instance {m k n : Nat} : MulAdd Float32 (Mat m k) (Mat k n) (Mat m n) where
  run := Mat.gemm

/-- `α * Aᵀ * B + β * C` is `gemmTN`. -/
public instance {m k n : Nat} : MulAdd Float32 (Transpose (Mat k m)) (Mat k n) (Mat m n) where
  run α A B β C := Mat.gemmTN α A.mat B β C

/-- `α * A * Bᵀ + β * C` is `gemmNT`. -/
public instance {m k n : Nat} : MulAdd Float32 (Mat m k) (Transpose (Mat n k)) (Mat m n) where
  run α A B β C := Mat.gemmNT α A B.mat β C

/-- `α * Aᵀ * Bᵀ + β * C` is `gemmTT`. -/
public instance {m k n : Nat} :
    MulAdd Float32 (Transpose (Mat k m)) (Transpose (Mat n k)) (Mat m n) where
  run α A B β C := Mat.gemmTT α A.mat B.mat β C

/-- `α * x + β * y` is `axpby`. -/
public instance {n : Nat} : Axpby Float32 (Vec n) where
  run := Vec.axpby

/-- `α * x + y` is `axpy`. -/
public instance {n : Nat} : Axpy Float32 (Vec n) where
  run := Vec.axpy

/-- `α * x` is `scal`. -/
public instance {n : Nat} : Scal Float32 (Vec n) where
  run := Vec.scal

/-- `x`, over `y`, is `copy`. -/
public instance {n : Nat} : Copy (Vec n) where
  run := Vec.copy

/-- `T⁻¹ * x` is `trsv`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} : Solve (Tri uplo d n) (Vec n) where
  run T x := Mat.trsv uplo d T.mat x

/-- `T⁻¹ * B` is `trsm` with `α = 1`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} : Solve (Tri uplo d m) (Mat m n) where
  run T B := Mat.trsm uplo d 1 T.mat B

/-- `α * T⁻¹ * B` is `trsm`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    ScaledSolve Float32 (Tri uplo d m) (Mat m n) where
  run α T B := Mat.trsm uplo d α T.mat B

/-- `α * B * T⁻¹` is `trsmRight`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    SolveRight Float32 (Tri uplo d n) (Mat m n) where
  run α B T := Mat.trsmRight uplo d α T.mat B

/-- `Tᵀ⁻¹ * x` is `trsvT`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} :
    Solve (Transpose (Tri uplo d n)) (Vec n) where
  run T x := Mat.trsvT uplo d T.mat.mat x

/-- `Tᵀ⁻¹ * B` is `trsmT` with `α = 1`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    Solve (Transpose (Tri uplo d m)) (Mat m n) where
  run T B := Mat.trsmT uplo d 1 T.mat.mat B

/-- `α * Tᵀ⁻¹ * B` is `trsmT`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    ScaledSolve Float32 (Transpose (Tri uplo d m)) (Mat m n) where
  run α T B := Mat.trsmT uplo d α T.mat.mat B

/-- `α * B * Tᵀ⁻¹` is `trsmRightT`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    SolveRight Float32 (Transpose (Tri uplo d n)) (Mat m n) where
  run α B T := Mat.trsmRightT uplo d α T.mat.mat B

/-- `T * x` is `trmv`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} : MulIn (Tri uplo d n) (Vec n) where
  run T x := Mat.trmv uplo d T.mat x

/-- `Tᵀ * x` is `trmvT`. -/
public instance {uplo : Uplo} {d : Diag} {n : Nat} : MulIn (Transpose (Tri uplo d n)) (Vec n) where
  run T x := Mat.trmvT uplo d T.mat.mat x

/-- `T * B` is `trmm` with `α = 1`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} : MulIn (Tri uplo d m) (Mat m n) where
  run T B := Mat.trmm uplo d 1 T.mat B

/-- `Tᵀ * B` is `trmmT` with `α = 1`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    MulIn (Transpose (Tri uplo d m)) (Mat m n) where
  run T B := Mat.trmmT uplo d 1 T.mat.mat B

/-- `α * T * B` is `trmm`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    ScaledMulIn Float32 (Tri uplo d m) (Mat m n) where
  run α T B := Mat.trmm uplo d α T.mat B

/-- `α * Tᵀ * B` is `trmmT`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    ScaledMulIn Float32 (Transpose (Tri uplo d m)) (Mat m n) where
  run α T B := Mat.trmmT uplo d α T.mat.mat B

/-- `α * B * T` is `trmmRight`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    MulInRight Float32 (Tri uplo d n) (Mat m n) where
  run α B T := Mat.trmmRight uplo d α T.mat B

/-- `α * B * Tᵀ` is `trmmRightT`. -/
public instance {uplo : Uplo} {d : Diag} {m n : Nat} :
    MulInRight Float32 (Transpose (Tri uplo d n)) (Mat m n) where
  run α B T := Mat.trmmRightT uplo d α T.mat.mat B

/-- `α * S * x + β * y` is `symv`. -/
public instance {uplo : Uplo} {n : Nat} : MulAdd Float32 (Sym uplo n) (Vec n) (Vec n) where
  run α S x β y := Mat.symv uplo α S.mat x β y

/-- `α * S * B + β * C` is `symm`. -/
public instance {uplo : Uplo} {m n : Nat} : MulAdd Float32 (Sym uplo m) (Mat m n) (Mat m n) where
  run α S B β C := Mat.symm uplo α S.mat B β C

/-- `α * B * S + β * C` is `symmRight`. -/
public instance {uplo : Uplo} {m n : Nat} : MulAdd Float32 (Mat m n) (Sym uplo n) (Mat m n) where
  run α B S β C := Mat.symmRight uplo α S.mat B β C

/-- `α * x * yᵀ + A` is `ger`. -/
public instance {m n : Nat} : MulAcc Float32 (Vec m) (Transpose (Vec n)) (Mat m n) where
  run α x y A := Mat.ger α x y.mat A

/-- `α * A * B + β * C`, over the triangle `C`, is `gemmtr`. -/
public instance {uplo : Uplo} {k n : Nat} :
    MulAdd Float32 (Mat n k) (Mat k n) (Tri uplo .nonUnit n) where
  run α A B β C := ⟨Mat.gemmtr uplo α A B β C.mat⟩

/-- `α * Aᵀ * B + β * C`, over the triangle `C`, is `gemmtrTN`. -/
public instance {uplo : Uplo} {k n : Nat} :
    MulAdd Float32 (Transpose (Mat k n)) (Mat k n) (Tri uplo .nonUnit n) where
  run α A B β C := ⟨Mat.gemmtrTN uplo α A.mat B β C.mat⟩

/-- `α * A * Bᵀ + β * C`, over the triangle `C`, is `gemmtrNT`. -/
public instance {uplo : Uplo} {k n : Nat} :
    MulAdd Float32 (Mat n k) (Transpose (Mat n k)) (Tri uplo .nonUnit n) where
  run α A B β C := ⟨Mat.gemmtrNT uplo α A B.mat β C.mat⟩

/-- `α * Aᵀ * Bᵀ + β * C`, over the triangle `C`, is `gemmtrTT`. -/
public instance {uplo : Uplo} {k n : Nat} :
    MulAdd Float32 (Transpose (Mat k n)) (Transpose (Mat n k)) (Tri uplo .nonUnit n) where
  run α A B β C := ⟨Mat.gemmtrTT uplo α A.mat B.mat β C.mat⟩

/-- `α * x * xᵀ + A`, over the triangle `A`, is `syr`. -/
public instance {uplo : Uplo} {n : Nat} : RankKAcc Float32 (Vec n) (Tri uplo .nonUnit n) where
  run α x A := ⟨Mat.syr uplo α x A.mat⟩

/-- `α * A * Aᵀ + β * C`, over the triangle `C`, is `syrk`. -/
public instance {uplo : Uplo} {k n : Nat} : RankK Float32 (Mat n k) (Tri uplo .nonUnit n) where
  run α A β C := ⟨Mat.syrk uplo α A β C.mat⟩

/-- `α * Aᵀ * A + β * C`, over the triangle `C`, is `syrkT`. -/
public instance {uplo : Uplo} {k n : Nat} :
    RankK Float32 (Transpose (Mat k n)) (Tri uplo .nonUnit n) where
  run α A β C := ⟨Mat.syrkT uplo α A.mat β C.mat⟩

/-- `α * x * yᵀ + α * y * xᵀ + A`, over the triangle `A`, is `syr2`. -/
public instance {uplo : Uplo} {n : Nat} : Rank2KAcc Float32 (Vec n) (Tri uplo .nonUnit n) where
  run α x y A := ⟨Mat.syr2 uplo α x y A.mat⟩

/-- `α * A * Bᵀ + α * B * Aᵀ + β * C`, over the triangle `C`, is `syr2k`. -/
public instance {uplo : Uplo} {k n : Nat} : Rank2K Float32 (Mat n k) (Tri uplo .nonUnit n) where
  run α A B β C := ⟨Mat.syr2k uplo α A B β C.mat⟩

/-- `α * Aᵀ * B + α * Bᵀ * A + β * C`, over the triangle `C`, is `syr2kT`. -/
public instance {uplo : Uplo} {k n : Nat} :
    Rank2K Float32 (Transpose (Mat k n)) (Tri uplo .nonUnit n) where
  run α A B β C := ⟨Mat.syr2kT uplo α A.mat B.mat β C.mat⟩

/-! ## The routines of the instances -/

section

variable {m k n : Nat} {uplo : Uplo} {d : Diag}

@[simp] public theorem mulAdd_mat_vec (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32)
    (y : Vec m) : MulAdd.run α A x β y = Mat.gemv α A x β y := rfl

@[simp] public theorem mulAdd_transpose_vec (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32)
    (y : Vec n) : MulAdd.run α (Transpose.mk A) x β y = Mat.gemvT α A x β y := rfl

@[simp] public theorem mulAdd_mat_mat (α : Float32) (A : Mat m k) (B : Mat k n) (β : Float32)
    (C : Mat m n) : MulAdd.run α A B β C = Mat.gemm α A B β C := rfl

@[simp] public theorem mulAdd_transpose_mat (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32)
    (C : Mat m n) : MulAdd.run α (Transpose.mk A) B β C = Mat.gemmTN α A B β C := rfl

@[simp] public theorem mulAdd_mat_transpose (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) : MulAdd.run α A (Transpose.mk B) β C = Mat.gemmNT α A B β C := rfl

@[simp] public theorem mulAdd_transpose_transpose (α : Float32) (A : Mat k m) (B : Mat n k)
    (β : Float32) (C : Mat m n) :
    MulAdd.run α (Transpose.mk A) (Transpose.mk B) β C = Mat.gemmTT α A B β C := rfl

@[simp] public theorem axpby_vec (α : Float32) (x : Vec n) (β : Float32) (y : Vec n) :
    Axpby.run α x β y = Vec.axpby α x β y := rfl

@[simp] public theorem axpy_vec (α : Float32) (x y : Vec n) : Axpy.run α x y = Vec.axpy α x y :=
  rfl

@[simp] public theorem scal_vec (α : Float32) (x : Vec n) : Scal.run α x = Vec.scal α x := rfl

@[simp] public theorem copy_vec (x y : Vec n) : Copy.run x y = Vec.copy x y := rfl

@[simp] public theorem solve_tri_vec (A : Mat n n) (x : Vec n) :
    Solve.run (Tri.mk (uplo := uplo) (d := d) A) x = Mat.trsv uplo d A x := rfl

@[simp] public theorem solve_tri_mat (A : Mat m m) (B : Mat m n) :
    Solve.run (Tri.mk (uplo := uplo) (d := d) A) B = Mat.trsm uplo d 1 A B := rfl

@[simp] public theorem scaledSolve_tri_mat (α : Float32) (A : Mat m m) (B : Mat m n) :
    ScaledSolve.run α (Tri.mk (uplo := uplo) (d := d) A) B = Mat.trsm uplo d α A B := rfl

@[simp] public theorem solveRight_tri_mat (α : Float32) (A : Mat n n) (B : Mat m n) :
    SolveRight.run α B (Tri.mk (uplo := uplo) (d := d) A) = Mat.trsmRight uplo d α A B := rfl

@[simp] public theorem solve_transpose_tri_vec (A : Mat n n) (x : Vec n) :
    Solve.run (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) x = Mat.trsvT uplo d A x := rfl

@[simp] public theorem solve_transpose_tri_mat (A : Mat m m) (B : Mat m n) :
    Solve.run (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) B = Mat.trsmT uplo d 1 A B :=
  rfl

@[simp] public theorem scaledSolve_transpose_tri_mat (α : Float32) (A : Mat m m) (B : Mat m n) :
    ScaledSolve.run α (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) B =
      Mat.trsmT uplo d α A B := rfl

@[simp] public theorem solveRight_transpose_tri_mat (α : Float32) (A : Mat n n) (B : Mat m n) :
    SolveRight.run α B (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) =
      Mat.trsmRightT uplo d α A B := rfl

@[simp] public theorem mulIn_tri_vec (A : Mat n n) (x : Vec n) :
    MulIn.run (Tri.mk (uplo := uplo) (d := d) A) x = Mat.trmv uplo d A x := rfl

@[simp] public theorem mulIn_transpose_tri_vec (A : Mat n n) (x : Vec n) :
    MulIn.run (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) x = Mat.trmvT uplo d A x := rfl

@[simp] public theorem mulIn_tri_mat (A : Mat m m) (B : Mat m n) :
    MulIn.run (Tri.mk (uplo := uplo) (d := d) A) B = Mat.trmm uplo d 1 A B := rfl

@[simp] public theorem mulIn_transpose_tri_mat (A : Mat m m) (B : Mat m n) :
    MulIn.run (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) B = Mat.trmmT uplo d 1 A B := rfl

@[simp] public theorem scaledMulIn_tri_mat (α : Float32) (A : Mat m m) (B : Mat m n) :
    ScaledMulIn.run α (Tri.mk (uplo := uplo) (d := d) A) B = Mat.trmm uplo d α A B := rfl

@[simp] public theorem scaledMulIn_transpose_tri_mat (α : Float32) (A : Mat m m) (B : Mat m n) :
    ScaledMulIn.run α (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) B =
      Mat.trmmT uplo d α A B := rfl

@[simp] public theorem mulInRight_tri_mat (α : Float32) (A : Mat n n) (B : Mat m n) :
    MulInRight.run α B (Tri.mk (uplo := uplo) (d := d) A) = Mat.trmmRight uplo d α A B := rfl

@[simp] public theorem mulInRight_transpose_tri_mat (α : Float32) (A : Mat n n) (B : Mat m n) :
    MulInRight.run α B (Transpose.mk (Tri.mk (uplo := uplo) (d := d) A)) =
      Mat.trmmRightT uplo d α A B := rfl

@[simp] public theorem mulAdd_sym_vec (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) : MulAdd.run α (Sym.mk (uplo := uplo) A) x β y = Mat.symv uplo α A x β y := rfl

@[simp] public theorem mulAdd_sym_mat (α : Float32) (A : Mat m m) (B : Mat m n) (β : Float32)
    (C : Mat m n) : MulAdd.run α (Sym.mk (uplo := uplo) A) B β C = Mat.symm uplo α A B β C := rfl

@[simp] public theorem mulAdd_mat_sym (α : Float32) (B : Mat m n) (A : Mat n n) (β : Float32)
    (C : Mat m n) :
    MulAdd.run α B (Sym.mk (uplo := uplo) A) β C = Mat.symmRight uplo α A B β C := rfl

@[simp] public theorem mulAcc_vec_transpose (α : Float32) (x : Vec m) (y : Vec n) (A : Mat m n) :
    MulAcc.run α x (Transpose.mk y) A = Mat.ger α x y A := rfl

@[simp] public theorem mulAdd_mat_mat_tri (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) :
    MulAdd.run α A B β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.gemmtr uplo α A B β C) := rfl

@[simp] public theorem mulAdd_transpose_mat_tri (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) :
    MulAdd.run α (Transpose.mk A) B β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.gemmtrTN uplo α A B β C) := rfl

@[simp] public theorem mulAdd_mat_transpose_tri (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) :
    MulAdd.run α A (Transpose.mk B) β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.gemmtrNT uplo α A B β C) := rfl

@[simp] public theorem mulAdd_transpose_transpose_tri (α : Float32) (A : Mat k n) (B : Mat n k)
    (β : Float32) (C : Mat n n) :
    MulAdd.run α (Transpose.mk A) (Transpose.mk B) β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.gemmtrTT uplo α A B β C) := rfl

@[simp] public theorem rankKAcc_vec_tri (α : Float32) (x : Vec n) (A : Mat n n) :
    RankKAcc.run α x (Tri.mk (uplo := uplo) (d := .nonUnit) A) = Tri.mk (Mat.syr uplo α x A) :=
  rfl

@[simp] public theorem rankK_mat_tri (α : Float32) (A : Mat n k) (β : Float32) (C : Mat n n) :
    RankK.run α A β (Tri.mk (uplo := uplo) (d := .nonUnit) C) = Tri.mk (Mat.syrk uplo α A β C) :=
  rfl

@[simp] public theorem rankK_transpose_tri (α : Float32) (A : Mat k n) (β : Float32) (C : Mat n n) :
    RankK.run α (Transpose.mk A) β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.syrkT uplo α A β C) := rfl

@[simp] public theorem rank2KAcc_vec_tri (α : Float32) (x y : Vec n) (A : Mat n n) :
    Rank2KAcc.run α x y (Tri.mk (uplo := uplo) (d := .nonUnit) A) =
      Tri.mk (Mat.syr2 uplo α x y A) := rfl

@[simp] public theorem rank2K_mat_tri (α : Float32) (A B : Mat n k) (β : Float32) (C : Mat n n) :
    Rank2K.run α A B β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.syr2k uplo α A B β C) := rfl

@[simp] public theorem rank2K_transpose_tri (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) :
    Rank2K.run α (Transpose.mk A) (Transpose.mk B) β (Tri.mk (uplo := uplo) (d := .nonUnit) C) =
      Tri.mk (Mat.syr2kT uplo α A B β C) := rfl

end

end BLAS.Float32
