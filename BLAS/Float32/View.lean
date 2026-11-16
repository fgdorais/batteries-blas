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

/-!
# Views

The views of a matrix select a routine and its options from the kinds of its operands, in place of
the flags of the reference BLAS: `Aᵀ` (`Transpose`) selects the transposed routines, and
`A.lower`, `A.unitUpper`, … (`Tri`) select a triangle and a diagonal. A view is the matrix itself,
with no copy.

## Instances

The instances of the classes of `BLAS.Ops` on vectors, matrices and views, which `blas!` expands
to, each with a `simp` lemma that unfolds it to its routine. So the specifications of the routines,
such as `getElem_gemv`, apply to the expansions of `blas!` with no new proofs.
-/

open ScalarArray

namespace BLAS.Float32

/-! ## Transposes -/

namespace Mat

variable {m n : Nat}

/-- The transpose of `A`, with no copy. -/
@[expose] public def transpose (A : Mat m n) : Transpose (Mat m n) := ⟨A⟩

@[simp] public theorem transpose_eq (A : Mat m n) : A.transpose = Transpose.mk A := rfl

end Mat

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

/-! ## The routines of the instances -/

section

variable {m k n : Nat} {uplo : Uplo} {d : Diag}

@[simp] public theorem mulAdd_mat_vec (α : Float32) (A : Mat m n) (x : Vec n) (β : Float32)
    (y : Vec m) : MulAdd.run α A x β y = Mat.gemv α A x β y := rfl

@[simp] public theorem mulAdd_transpose_vec (α : Float32) (A : Mat m n) (x : Vec m) (β : Float32)
    (y : Vec n) : MulAdd.run α (Transpose.mk A) x β y = Mat.gemvT α A x β y := rfl

@[simp] public theorem mulAdd_mat_mat (α : Float32) (A : Mat m k) (B : Mat k n) (β : Float32)
    (C : Mat m n) : MulAdd.run α A B β C = Mat.gemm α A B β C := rfl

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

end

end BLAS.Float32
