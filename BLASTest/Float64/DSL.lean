/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
import BLAS.Notation
import BLASTest.Util
meta import BLAS
meta import BLAS.Notation
meta import BLASTest.Util

/-!
Tests for the `blas%` notation on `Float`: the routine of each update, its values, and the updates
that no single routine computes.
-/

open BLAS BLAS.Float64 BLAS.Notation

/-! ## Expansions

Each update is one call of its routine, which `simp` unfolds, so the routine's specification
applies. -/

section

variable {m k n : Nat} (α β : Float)

example (A : Mat m n) (x : Vec n) (y : Vec m) :
    blas%(y := α • A * x + β • y) = Mat.gemv α A x β y := by simp

example (A : Mat m n) (x : Vec n) (y : Vec m) :
    blas%(y := β • y + α • A * x) = Mat.gemv α A x β y := by simp

-- A scalar is a product or quotient of terms, with no parentheses.
example (a : Float) (A : Mat m n) (x : Vec n) (y : Vec m) :
    blas%(y := 2 * a • A * x + -β / 2 • y) = Mat.gemv (2 * a) A x (-β / 2) y := by simp

example (a : Float) (x y : Vec n) : blas%(y := (a + β) • x + y) = Vec.axpy (a + β) x y := by
  simp

example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y := A * x) = Mat.gemv 1 A x 0 y := by
  simp

example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y += α • A * x) = Mat.gemv α A x 1 y := by
  simp

example (A : Mat m n) (x : Vec m) (y : Vec n) :
    blas%(y := α • Aᵀ * x + β • y) = Mat.gemvT α A x β y := by simp

example (A : Mat m k) (B : Mat k n) (C : Mat m n) :
    blas%(C := α • A * B + β • C) = Mat.gemm α A B β C := by simp

example (A : Mat m k) (B : Mat k n) (C : Mat m n) : blas%(C += A * B) = Mat.gemm 1 A B 1 C := by
  simp

example (A : Mat k m) (B : Mat k n) (C : Mat m n) :
    blas%(C := α • Aᵀ * B + β • C) = Mat.gemmTN α A B β C := by simp

example (A : Mat m k) (B : Mat n k) (C : Mat m n) :
    blas%(C += A * Bᵀ) = Mat.gemmNT 1 A B 1 C := by simp

example (A : Mat k m) (B : Mat n k) (C : Mat m n) :
    blas%(C := Aᵀ * Bᵀ) = Mat.gemmTT 1 A B 0 C := by simp

example (x y : Vec n) : blas%(y := α • x + y) = Vec.axpy α x y := by simp

example (x y : Vec n) : blas%(y := α • x + β • y) = Vec.axpby α x β y := by simp

example (x y : Vec n) : blas%(y := α • x) = Vec.axpby α x 0 y := by simp

example (x y : Vec n) : blas%(y := x - y) = Vec.axpby 1 x (-1) y := by simp

example (x y : Vec n) : blas%(y += x) = Vec.axpy 1 x y := by simp

example (x : Vec n) : blas%(x := α • x) = Vec.scal α x := by simp

example (x y : Vec n) : blas%(y := x) = Vec.copy x y := by simp

example (A : Mat n n) (x : Vec n) : blas%(x := A.lower⁻¹ * x) = Mat.trsv .lower .nonUnit A x := by
  simp

example (A : Mat n n) (x : Vec n) : blas%(x := A.unitUpper⁻¹ * x) = Mat.trsv .upper .unit A x :=
  by simp

example (A : Mat m m) (B : Mat m n) :
    blas%(B := α • A.lower⁻¹ * B) = Mat.trsm .lower .nonUnit α A B := by simp

example (A : Mat n n) (B : Mat m n) :
    blas%(B := α • B * A.unitUpper⁻¹) = Mat.trsmRight .upper .unit α A B := by simp

-- A subtracted summand has the negated scalar.
example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y := A * x - y) = Mat.gemv 1 A x (-1) y :=
  by simp

example (A : Mat m n) (x : Vec n) (y : Vec m) : blas%(y -= A * x) = Mat.gemv (-1) A x 1 y := by
  simp

example (A : Mat m k) (B : Mat k n) (C : Mat m n) :
    blas%(C := -α • A * B - β • C) = Mat.gemm (-α) A B (-β) C := by simp

example (x y : Vec n) : blas%(y := y - α • x) = Vec.axpy (-α) x y := by simp

example (x y : Vec n) : blas%(y -= α • x) = Vec.axpy (-α) x y := by simp

example (x : Vec n) : blas%(x := -x) = Vec.scal (-1) x := by simp

-- The specifications of the routines apply to the updates.
example (A : Mat m n) (x : Vec n) (y : Vec m) (i : Nat) (h : i < m) (hn : n ≠ 0)
    (hα : (α == 0) = false) :
    (blas%(y := α • A * x + β • y))[i] =
      Nat.fold n (fun j _ s => s + α * x[j] * A[(i, j)]) (betaMul β y[i]) := by
  simp [hn, hα]

end

/-! ## Values -/

-- `[[1, 2], [3, 4]] * [1, 1] = [3, 7]`, its transpose `[4, 6]`, and `2 * [3, 7] - [1, 1]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [1, 1]
  (blas%(y := A * x)).toList == [3, 7] && (blas%(y := Aᵀ * x)).toList == [4, 6] &&
    (blas%(y := 2 • A * x + (-1) • y)).toList == [5, 13]

-- In a `do` block, `blas%` updates a mutable variable, and `A[:, j]` is a column of `A`.
#guard Id.run do
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let mut y : Vec 2 := .ofList [0, 0]
  blas% y := A[:, 1]
  blas% y += 2 • A[:, 0]
  blas% y := 3 • y
  blas% y += A * A[:, 0]
  -- `3 * ([2, 4] + 2 * [1, 3]) + [[1, 2], [3, 4]] * [1, 3]`
  return y.toList == [19, 45]

-- `y - 2 * x` and `A * x - y`, for `A = [[1, 2], [3, 4]]`, `x = [1, 1]` and `y = [5, 5]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 1]
  let y : Vec 2 := .ofList [5, 5]
  (blas%(y -= 2 • x)).toList == [3, 3] && (blas%(y := A * x - y)).toList == [-2, 2]

-- `2 • x + 3 • y` and `y := 2 • x`, by `axpby`, and `Aᵀ * B` by `gemmTN`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let x : Vec 2 := .ofList [1, 2]
  let y : Vec 2 := .ofList [10, 20]
  let C : Mat 2 2 := .ofPMat ⟨.ofList [0, 0, 0, 0], by decide⟩
  (blas%(y := 2 • x + 3 • y)).toList == [32, 64] && (blas%(y := 2 • x)).toList == [2, 4] &&
    (blas%(C := Aᵀ * A)).toList == [10, 14, 14, 20]

-- `C := A * B + C`, for `A = [[1, 2], [3, 4]]`, `B = I` and `C = [[1, 1], [1, 1]]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [1, 3, 2, 4], by decide⟩
  let B : Mat 2 2 := .ofPMat ⟨.ofList [1, 0, 0, 1], by decide⟩
  let C : Mat 2 2 := .ofPMat ⟨.ofList [1, 1, 1, 1], by decide⟩
  (blas%(C += A * B)).toList == [2, 4, 3, 5]

-- `[[2, 0], [1, 1]]⁻¹ * [2, 3] = [1, 2]`, from the lower triangle of `[[2, 9], [1, 1]]`.
#guard
  let A : Mat 2 2 := .ofPMat ⟨.ofList [2, 1, 9, 1], by decide⟩
  let x : Vec 2 := .ofList [2, 3]
  (blas%(x := A.lower⁻¹ * x)).toList == [1, 2]

/-! ## In place

An update compiles to its routine's call, so it updates its target in place when the target's
array is not shared. -/

/-- The address of the array of `x`, with `x`, taken before `x` goes on to an update. -/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-- `gemv`, `gemvT`, `axpy` and `trsv` by `blas%` update `y` in place. -/
def inPlace (m : Nat) : Bool := Id.run do
  let A : Mat m m := .ofFn fun i j => ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let x : Vec m := .ofFn fun i => (i.val % 9).toFloat - 4
  let (p, y) := withAddr (.ofFn fun i => (i.val % 5).toFloat)
  let mut y := y
  blas% y := 2 • A * x + 3 • y
  blas% y += 2 • Aᵀ * x
  blas% y += 2 • x
  blas% y := A.unitLower⁻¹ * y
  return BLASTest.addr y.data == p

#guard inPlace 8

/-! ## Updates that no single routine computes -/

/--
error: blas%: no single BLAS routine computes this update of `y`
-/
#guard_msgs in
example (A : Mat 2 2) (x z y : Vec 2) : Vec 2 := blas%(y := A * x - z)

/--
error: blas%: no single BLAS routine computes this update of `y`
-/
#guard_msgs in
example (x z y : Vec 2) : Vec 2 := blas%(y := (2 : Float) • x + (3 : Float) • z)

/--
error: blas%: no single BLAS routine computes a product of three factors
-/
#guard_msgs in
example (A B : Mat 2 2) (x y : Vec 2) : Vec 2 := blas%(y := A * B * x)

/--
error: blas%: no single BLAS routine computes this factor; write it with a separate update first
-/
#guard_msgs in
example (A : Mat 2 2) (x z y : Vec 2) : Vec 2 := blas%(y := A * (x - z))

/--
error: blas%: `y` occurs twice; combine its scalars
-/
#guard_msgs in
example (x y : Vec 2) : Vec 2 := blas%(y := x + y + y)
