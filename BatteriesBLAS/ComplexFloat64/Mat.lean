/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Vec

/-!
# Complex matrices

`Mat m n` is an `m × n` matrix of complex numbers, stored in column-major order in a
`Float64Array` as in Fortran, with the parts of each element interleaved. As in the reference
BLAS, the offset and the leading dimension count elements: element `(i, j)` has its real part at
the index `2 * (off + ld * j + i)` and its imaginary part at the next index.

Column `j` is the contiguous vector `A.col j` of the array, with no copy, and `A[(i, j)]` is its
element `i`, so that the lemmas on vectors apply to the columns.
-/

open ScalarArray

namespace BLAS.ComplexFloat64

/--
An `m × n` matrix of complex numbers, stored in column-major order in a `Float64Array`, from the
element `off`, with the leading dimension `ld`, both counted in elements of two entries each:
column `j` starts at the element `off + ld * j`.
-/
public structure Mat (m n : Nat) where
  /-- The array that holds the parts of the elements. -/
  data : Float64Array
  /-- The position of the first element, in elements. -/
  off : Nat
  /-- The distance between the starts of two consecutive columns, in elements. -/
  ld : Nat
  /-- The columns don't overlap. -/
  le_ld : m ≤ ld
  /-- The last column is in the array. -/
  bound : m = 0 ∨ n = 0 ∨ 2 * (off + ld * (n - 1) + m) ≤ data.size

namespace Mat

variable {m n : Nat}

/-- Column `j < n` of a matrix with rows is in the array. -/
public theorem col_le (A : Mat m n) {j : Nat} (hm : 0 < m) (hj : j < n) :
    2 * (A.off + A.ld * j + m) ≤ A.data.size := by
  have : A.ld * j ≤ A.ld * (n - 1) := Nat.mul_le_mul_left _ (by lia)
  rcases A.bound with h | h | h <;> lia

/-- Column `j` as a contiguous vector, with no copy. -/
@[expose, inline] public def col (A : Mat m n) (j : Nat) (hj : j < n) : Vec m where
  data := A.data
  off := A.off + A.ld * j
  inc := 1
  inc_pos := Or.inl Nat.one_pos
  bound := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inl h
    · exact Or.inr (by have := A.col_le h hj; lia)

@[simp] public theorem data_col (A : Mat m n) (j : Nat) (hj : j < n) :
    (A.col j hj).data = A.data := rfl

@[simp] public theorem off_col (A : Mat m n) (j : Nat) (hj : j < n) :
    (A.col j hj).off = A.off + A.ld * j := rfl

@[simp] public theorem inc_col (A : Mat m n) (j : Nat) (hj : j < n) : (A.col j hj).inc = 1 := rfl

/-- `A[(i, j)]` is the element in row `i` and column `j`: element `i` of `A.col j`. -/
public instance : GetElem (Mat m n) (Nat × Nat) ComplexFloat fun _ p => p.1 < m ∧ p.2 < n where
  getElem A p h := (A.col p.2 h.2)[p.1]'h.1

public theorem getElem_def (A : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    A[(i, j)] = (A.col j h.2)[i]'h.1 := rfl

@[simp] public theorem getElem_col (A : Mat m n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) :
    (A.col j hj)[i] = A[(i, j)] := rfl

/-- A matrix with the same array, offset and leading dimension, but other proofs, is the same. -/
public theorem getElem_congr {A B : Mat m n} (hd : A.data = B.data) (ho : A.off = B.off)
    (hl : A.ld = B.ld) (i j : Nat) (h : i < m ∧ j < n) : A[(i, j)] = B[(i, j)] := by
  cases A; cases B; cases hd; cases ho; cases hl; rfl

/-- The `m × n` matrix of the elements of `x`, column after column, with no copy. -/
@[expose] public def ofVec (x : Vec (m * n)) (h : x.off = 0 ∧ x.inc = 1) : Mat m n where
  data := x.data
  off := 0
  ld := m
  le_ld := Nat.le_refl _
  bound := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact Or.inl hm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inr (Or.inl hn)
    refine Or.inr (Or.inr ?_)
    rcases x.bound with hb | hb
    · exact absurd hb (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hm hn))
    · rw [h.1, h.2] at hb
      have : m * (n - 1) + m = m * n := by
        rw [← Nat.mul_succ]; congr 1; lia
      lia

@[simp] public theorem getElem_ofVec (x : Vec (m * n)) (h : x.off = 0 ∧ x.inc = 1) (i j : Nat)
    (hij : i < m ∧ j < n) :
    (ofVec x h)[(i, j)] = x[m * j + i]'(by
      have : m * j + m ≤ m * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hij.2
      lia) := by
  simp only [getElem_def, Vec.getElem_def, col, ofVec, h.1, h.2]
  congr 1 <;> congr 1 <;> lia

/-- The matrix with the elements `f i j`, stored contiguously with the leading dimension `m`. -/
public def ofFn (f : Fin m → Fin n → ComplexFloat) : Mat m n :=
  ofVec (.ofFn fun k => f ⟨k.val % m, Nat.mod_lt _ (Nat.pos_of_mul_pos_right k.pos)⟩
    ⟨k.val / m, Nat.div_lt_of_lt_mul k.isLt⟩) ⟨Vec.off_ofFn _, Vec.inc_ofFn _⟩

@[simp] public theorem getElem_ofFn (f : Fin m → Fin n → ComplexFloat) (i j : Nat)
    (h : i < m ∧ j < n) : (ofFn f)[(i, j)] = f ⟨i, h.1⟩ ⟨j, h.2⟩ := by
  simp only [ofFn, getElem_ofVec, Vec.getElem_ofFn]
  have h₁ : (m * j + i) % m = i := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h.1
  have h₂ : (m * j + i) / m = j := by
    rw [Nat.mul_add_div (by lia), Nat.div_eq_of_lt h.1, Nat.add_zero]
  simp [h₁, h₂]

/--
The matrix of the `m × n` elements of `a` from the element `off` with the leading dimension `ld`,
both counted in elements, if they are in `a` and `m ≤ ld`.
-/
public def ofLd? (a : Float64Array) (off ld : Nat) : Option (Mat m n) :=
  if h : m ≤ ld ∧ (m = 0 ∨ n = 0 ∨ 2 * (off + ld * (n - 1) + m) ≤ a.size) then
    some ⟨a, off, ld, h.1, h.2⟩
  else none

/-- The elements, column after column. -/
public def toList (A : Mat m n) : List ComplexFloat :=
  (List.ofFn fun j : Fin n => List.ofFn fun i : Fin m => A[(i.val, j.val)]).flatten

end Mat

end BLAS.ComplexFloat64
