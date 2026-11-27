/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Herm3

/-!
# Complex symmetric Level 3

The complex symmetric routines: `symm` (`C := α * A * B + β * C`) and `symmRight`
(`C := α * B * A + β * C`) for a symmetric `A`, `syrk` (`C := α * A * Aᵀ + β * C`) and `syrkT`
(`C := α * Aᵀ * A + β * C`), and `syr2k` (`C := α * A * Bᵀ + α * B * Aᵀ + β * C`) and `syr2kT`
(`C := α * Aᵀ * B + α * Bᵀ * A + β * C`), on the upper or the lower triangle of the symmetric
matrices, as `zsymm`, `zsyrk` and `zsyr2k` in the reference BLAS (`master`), with the same
operations in the same order. Unlike the Hermitian routines, nothing is conjugated, `α` and `β`
are complex, and the diagonal is updated as the rest of the triangle.

Each routine runs a step per column of `C`, in increasing order, and each step updates the column
in place when the array of `C` is not shared, by the loops of the reference BLAS.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.ComplexFloat64

namespace Mat

variable {m n k : Nat}

/-! ## `symm` -/

/-- Element `(i, j)` of the symmetric matrix stored in the triangle `uplo` of `A`. -/
@[expose] public def symAt (uplo : Float64.Uplo) (A : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    ComplexFloat :=
  if InTri uplo i j then A[(i, j)] else A[(j, i)]

/--
The sum `0 + mul B[0, j] A[0, i] + …` of `symm` over the rows `l` in the triangle of column `i` of
`A`, other than the diagonal: `l < i` in the upper triangle and `l > i` in the lower one, in
increasing order.
-/
@[expose] public def symmDot (uplo : Float64.Uplo) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (hi : i < m) (hj : j < n) : ComplexFloat :=
  if uplo = .upper then
    Vec.accWith id id (· + ·) zero ((B.col j hj).slice 0 i (by lia))
      ((A.col i hi).slice 0 i (by lia))
  else
    Vec.accWith id id (· + ·) zero ((B.col j hj).slice (i + 1) (m - (i + 1))
      (by lia)) ((A.col i hi).slice (i + 1) (m - (i + 1)) (by lia))

/--
The step of `symm` for row `i` of column `j` of `C`: with `t₁ = mul α B[i, j]`, it adds
`mul t₁ A[l, i]` to the elements `l` of the column in the triangle of column `i` of `A`, and then
sets element `i` to `hemmAt β (mul t₁ A[i, i]) (mul α (symmDot uplo A B i j))` of its value, as
`zsymm` with `SIDE = 'L'`.
-/
public def symmStep (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) (C : Mat m n) : Mat m n :=
  let t₁ := mul α B[(i, j)]
  let C :=
    if uplo = .upper then axpyColSlice t₁ A i hi C j hj 0 i (by lia)
    else axpyColSlice t₁ A i hi C j hj (i + 1) (m - (i + 1)) (by lia)
  C.setAt i j ⟨hi, hj⟩
    (hemmAt β (mul t₁ A[(i, i)]) (mul α (symmDot uplo A B i j hi hj)) C[(i, j)])

/-- The step `symmStep` at element `l` of column `j`, from its old value `v`. -/
@[expose] public def symmStepAt (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m)
    (B : Mat m n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) (l : Nat) (hl : l < m)
    (v : ComplexFloat) : ComplexFloat :=
  if l = i then
    hemmAt β (mul (mul α B[(i, j)]) A[(i, i)]) (mul α (symmDot uplo A B i j hi hj)) v
  else if InTri uplo l i then v + mul (mul α B[(i, j)]) A[(l, i)]
  else v

private theorem getElem_symmStep (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m)
    (B : Mat m n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) (C : Mat m n) (l j' : Nat)
    (h : l < m ∧ j' < n) :
    (symmStep uplo α β A B j hj i hi C)[(l, j')] =
      if j' = j then symmStepAt uplo α β A B j hj i hi l h.1 C[(l, j')] else C[(l, j')] := by
  unfold symmStep symmStepAt
  rw [getElem_setAt]
  cases uplo
  rotate_left
  · simp only [reduceCtorEq, ↓reduceIte, InTri, false_and, true_and, false_or]
    rw [getElem_axpyColSlice, getElem_axpyColSlice]
    by_cases e : j' = j
    · subst e
      by_cases e' : l = i
      · subst e'; simp [show ¬(l + 1 ≤ l) by lia]
      · have h1 : (i + 1 ≤ l ∧ l < i + 1 + (m - (i + 1))) = (i < l) := by apply propext; lia
        simp [e', h1]
    · simp [e]
  · simp only [↓reduceIte, InTri, true_and]
    rw [getElem_axpyColSlice, getElem_axpyColSlice]
    by_cases e : j' = j
    · subst e
      by_cases e' : l = i
      · subst e'; simp
      · simp [e']
    · simp [e]

/-- Column `j` of `symm`: the steps `symmStep` for each row, in the order of `hemmRow`. -/
public def symmCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  Nat.fold m (fun s hs C => symmStep uplo α β A B j hj (hemmRow uplo m s) (hemmRow_lt uplo hs) C) C

private theorem getElem_symmCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m)
    (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) (l j' : Nat) (h : l < m ∧ j' < n) :
    (symmCol uplo α β A B C j hj)[(l, j')] =
      if j' = j then
        Nat.fold m (fun s hs v => symmStepAt uplo α β A B j hj (hemmRow uplo m s)
          (hemmRow_lt uplo hs) l h.1 v) C[(l, j')]
      else C[(l, j')] := by
  unfold symmCol
  rw [getElem_fold_of_pointwise
    (fun s hs C => symmStep uplo α β A B j hj (hemmRow uplo m s) (hemmRow_lt uplo hs) C)
    (fun s hs l j' h v => if j' = j then symmStepAt uplo α β A B j hj (hemmRow uplo m s)
      (hemmRow_lt uplo hs) l h.1 v else v)
    (fun _ _ _ _ _ _ => getElem_symmStep ..) C l j' h m (Nat.le_refl _)]
  by_cases e : j' = j
  · simp [e]
  · simp only [e, ↓reduceIte, fold_id]

/--
`symm uplo α A B β C` is `α * A * B + β * C` for the symmetric matrix `A` stored in its upper
triangle (`.upper`) or its lower triangle (`.lower`), as `zsymm` with `SIDE = 'L'`: it returns `C`
when `α = 0` and `β = 1`, scales `C` by `β` (`betaMul`) when `α = 0`, and otherwise runs
`symmCol` for each column in increasing order.
-/
@[expose] public def symm (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (β : ComplexFloat) (C : Mat m n) : Mat m n :=
  if isZero α && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => betaCol β C j hj) C
  else Nat.fold n (fun j hj C => symmCol uplo α β A B C j hj) C

/--
Element `(i, j)` of `symm uplo α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise the
fold of the steps `symmStepAt` over the rows in the order of `hemmRow`, from `C[i, j]`.
-/
public theorem getElem_symm (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (β : ComplexFloat) (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symm uplo α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold m (fun s hs v => symmStepAt uplo α β A B j h.2 (hemmRow uplo m s)
        (hemmRow_lt uplo hs) i h.1 v) C[(i, j)] := by
  unfold symm
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp only [ha, hb, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [getElem_fold_col (fun j hj C => betaCol β C j hj) (fun i j _ c => betaMul β c)
        (fun _ _ _ _ _ _ => getElem_betaCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]
  · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => symmCol uplo α β A B C j hj)
      (fun i j hij c => Nat.fold m (fun s hs v => symmStepAt uplo α β A B j hij.2
        (hemmRow uplo m s) (hemmRow_lt uplo hs) i hij.1 v) c)
      (fun _ _ _ _ _ _ => getElem_symmCol ..) C i j h n (Nat.le_refl _)]
    simp [h.2]

/-! ## `symmRight` -/

/--
The first value of element `c` of column `j` of `symmRight`, with `b = B[i, j]` and
`a = A[j, j]`: `mul (mul α a) b` when `β = 0`, and `mul β c + mul (mul α a) b` otherwise.
-/
@[expose] public def symmRightInit (α β a c b : ComplexFloat) : ComplexFloat :=
  if isZero β then mul (mul α a) b else mul β c + mul (mul α a) b

/--
Column `j` of `symmRight`: each element `c` becomes `symmRightInit α β A[j, j] c B[i, j]`, and
then gets `mul (mul α (symAt uplo A l j)) B[i, l]` for each column `l ≠ j` of `B`, in increasing
order, as `zsymm` with `SIDE = 'R'`.
-/
public def symmRightCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat n n) (B : Mat m n)
    (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  let a := A[(j, j)]
  let C := zipCol (fun c b => symmRightInit α β a c b) B j hj C j hj
  Nat.fold n (fun l hl C => if l = j then C
    else axpyColSlice (mul α (symAt uplo A l j ⟨hl, hj⟩)) B l hl C j hj 0 m (by lia)) C

private theorem getElem_symmRightCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat n n)
    (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (symmRightCol uplo α β A B C j hj)[(i, j')] =
      if j' = j then
        Nat.fold n (fun l hl v => if l = j then v
          else v + mul (mul α (symAt uplo A l j ⟨hl, hj⟩)) B[(i, l)])
          (symmRightInit α β A[(j, j)] C[(i, j')] B[(i, j)])
      else C[(i, j')] := by
  unfold symmRightCol
  rw [getElem_fold_of_pointwise
    (fun l hl C => if l = j then C
      else axpyColSlice (mul α (symAt uplo A l j ⟨hl, hj⟩)) B l hl C j hj 0 m (by lia))
    (fun l hl i j' h v => if j' = j then (if l = j then v
      else v + mul (mul α (symAt uplo A l j ⟨hl, hj⟩)) B[(i, l)]) else v)
    (fun l hl C i j' h => by
      by_cases e : l = j
      · simp [e]
      · simp only [e, ↓reduceIte, getElem_axpyColSlice, Nat.zero_le, Nat.zero_add, h.1,
          and_true])
    _ i j' h n (Nat.le_refl _)]
  rw [getElem_zipCol]
  by_cases e : j' = j
  · subst e; simp
  · simp [e, fold_id]

/--
`symmRight uplo α A B β C` is `α * B * A + β * C` for the symmetric matrix `A` stored in its upper
triangle (`.upper`) or its lower triangle (`.lower`), as `zsymm` with `SIDE = 'R'`: it returns `C`
when `α = 0` and `β = 1`, scales `C` by `β` (`betaMul`) when `α = 0`, and otherwise runs
`symmRightCol` for each column in increasing order.
-/
@[expose] public def symmRight (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n n)
    (B : Mat m n) (β : ComplexFloat) (C : Mat m n) : Mat m n :=
  if isZero α && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => betaCol β C j hj) C
  else Nat.fold n (fun j hj C => symmRightCol uplo α β A B C j hj) C

/--
Element `(i, j)` of `symmRight uplo α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise
`symmRightInit α β A[j, j] C[i, j] B[i, j]` plus `mul (mul α (symAt uplo A l j)) B[i, l]` for
each `l ≠ j`, in increasing order, from the left.
-/
public theorem getElem_symmRight (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n n)
    (B : Mat m n) (β : ComplexFloat) (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symmRight uplo α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold n (fun l hl v => if l = j then v
          else v + mul (mul α (symAt uplo A l j ⟨hl, h.2⟩)) B[(i, l)])
          (symmRightInit α β A[(j, j)] C[(i, j)] B[(i, j)]) := by
  unfold symmRight
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp only [ha, hb, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [getElem_fold_col (fun j hj C => betaCol β C j hj) (fun i j _ c => betaMul β c)
        (fun _ _ _ _ _ _ => getElem_betaCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]
  · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => symmRightCol uplo α β A B C j hj)
      (fun i j hij c => Nat.fold n (fun l hl v => if l = j then v
          else v + mul (mul α (symAt uplo A l j ⟨hl, hij.2⟩)) B[(i, l)])
          (symmRightInit α β A[(j, j)] c B[(i, j)]))
      (fun _ _ _ _ _ _ => getElem_symmRightCol ..) C i j h n (Nat.le_refl _)]
    simp [h.2]

/-! ## `syrk` and `syr2k` -/

/--
The first row of the triangle of column `j`, with the diagonal: `0` in the upper triangle and `j`
in the lower one.
-/
@[expose] public def triLo (uplo : Float64.Uplo) (j : Nat) : Nat :=
  if uplo = .upper then 0 else j

/--
The number of rows of the triangle of column `j` of an `n × n` matrix, with the diagonal: `j + 1`
in the upper triangle and `n - j` in the lower one.
-/
@[expose] public def triLen (uplo : Float64.Uplo) (n j : Nat) : Nat :=
  if uplo = .upper then j + 1 else n - j

public theorem triLo_add_triLen (uplo : Float64.Uplo) {n j : Nat} (hj : j < n) :
    triLo uplo j + triLen uplo n j ≤ n := by
  unfold triLo triLen; split <;> lia

/-- Row `i` is in the triangle of column `j`, with the diagonal, exactly when it is in the rows
`triLo`, …, `triLo + triLen - 1`. -/
public theorem mem_tri (uplo : Float64.Uplo) {n i j : Nat} (hi : i < n) :
    (triLo uplo j ≤ i ∧ i < triLo uplo j + triLen uplo n j) = (i = j ∨ InTri uplo i j) := by
  apply propext
  unfold triLo triLen InTri
  cases uplo <;> simp only [↓reduceIte, reduceCtorEq, true_and, false_and, or_false, false_or] <;>
    lia

/--
The scaling of element `(i, j)` of `C`, from its value `c`, by `β` in `zsyrk` and `zsyr2k`:
`betaMul β c` in the triangle, with the diagonal, and `c` outside.
-/
@[expose] public def syrkInitAt (uplo : Float64.Uplo) (β : ComplexFloat) (i j : Nat)
    (c : ComplexFloat) : ComplexFloat :=
  if i = j ∨ InTri uplo i j then betaMul β c else c

/-- Column `j` of `C` scaled as `syrkInitAt` says, in the triangle. -/
public def syrkInitCol (uplo : Float64.Uplo) (β : ComplexFloat) (C : Mat n n) (j : Nat)
    (hj : j < n) : Mat n n :=
  if isOne β then C
  else mapColSlice (betaMul β) C j hj (triLo uplo j) (triLen uplo n j) (triLo_add_triLen uplo hj)

private theorem getElem_syrkInitCol (uplo : Float64.Uplo) (β : ComplexFloat) (C : Mat n n)
    (j : Nat) (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (syrkInitCol uplo β C j hj)[(i, j')] =
      if j' = j then syrkInitAt uplo β i j C[(i, j')] else C[(i, j')] := by
  unfold syrkInitCol syrkInitAt
  by_cases hb : isOne β
  · simp [hb, betaMul]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, getElem_mapColSlice, mem_tri uplo h.1]
    by_cases e : j' = j <;> simp [e]

/--
Step `l` of column `j` of `syrk` at element `(i, j)`, from its value `v`: unchanged when
`A[j, l] = 0`, and otherwise `v + mul (mul α A[j, l]) A[i, l]` in the triangle, with the diagonal,
as `zsyrk` with `TRANS = 'N'`.
-/
@[expose] public def syrkStepAt (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k) (j : Nat)
    (l : Nat) (hl : l < k) (i : Nat) (hi : i < n) (hj : j < n) (v : ComplexFloat) :
    ComplexFloat :=
  if isZero A[(j, l)] then v
  else if i = j ∨ InTri uplo i j then v + mul (mul α A[(j, l)]) A[(i, l)]
  else v

/-- Step `l` of column `j` of `syrk`, as `syrkStepAt` says. -/
public def syrkStep (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k) (j : Nat) (hj : j < n)
    (l : Nat) (hl : l < k) (C : Mat n n) : Mat n n :=
  if isZero A[(j, l)] then C
  else axpyColSlice (mul α A[(j, l)]) A l hl C j hj (triLo uplo j) (triLen uplo n j)
    (triLo_add_triLen uplo hj)

private theorem getElem_syrkStep (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k) (j : Nat)
    (hj : j < n) (l : Nat) (hl : l < k) (C : Mat n n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (syrkStep uplo α A j hj l hl C)[(i, j')] =
      if j' = j then syrkStepAt uplo α A j l hl i h.1 hj C[(i, j')] else C[(i, j')] := by
  unfold syrkStep syrkStepAt
  by_cases hz : isZero A[(j, l)]
  · simp [hz]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, getElem_axpyColSlice, mem_tri uplo h.1]
    by_cases e : j' = j <;> simp [e]

/-- Column `j` of `syrk`: `syrkInitCol`, then the steps `syrkStep` for each `l`. -/
public def syrkCol (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k) (β : ComplexFloat)
    (C : Mat n n) (j : Nat) (hj : j < n) : Mat n n :=
  Nat.fold k (fun l hl C => syrkStep uplo α A j hj l hl C) (syrkInitCol uplo β C j hj)

private theorem getElem_syrkCol (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k)
    (β : ComplexFloat) (C : Mat n n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (syrkCol uplo α A β C j hj)[(i, j')] =
      if j' = j then
        Nat.fold k (fun l hl v => syrkStepAt uplo α A j l hl i h.1 hj v)
          (syrkInitAt uplo β i j C[(i, j')])
      else C[(i, j')] := by
  unfold syrkCol
  rw [getElem_fold_of_pointwise (fun l hl C => syrkStep uplo α A j hj l hl C)
    (fun l hl i j' h v => if j' = j then syrkStepAt uplo α A j l hl i h.1 hj v else v)
    (fun _ _ _ _ _ _ => getElem_syrkStep ..) _ i j' h k (Nat.le_refl _), getElem_syrkInitCol]
  by_cases e : j' = j
  · simp [e]
  · simp [e, fold_id]

/--
`syrk uplo α A β C` is `α * A * Aᵀ + β * C`, on the upper triangle of `C` (`.upper`) or its lower
triangle (`.lower`), as `zsyrk` with `TRANS = 'N'`: it returns `C` when `α = 0` or `k = 0`, and
`β = 1`; it scales the triangle as `syrkInitAt` says when `α = 0`; and otherwise runs `syrkCol`
for each column in increasing order. The other triangle is unchanged.
-/
@[expose] public def syrk (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k)
    (β : ComplexFloat) (C : Mat n n) : Mat n n :=
  if (isZero α || k == 0) && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => syrkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => syrkCol uplo α A β C j hj) C

/--
Element `(i, j)` of `syrk uplo α A β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`syrkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise the fold of the steps `syrkStepAt`
over `l = 0, …, k - 1` from it.
-/
public theorem getElem_syrk (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n k)
    (β : ComplexFloat) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (syrk uplo α A β C)[(i, j)] =
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then syrkInitAt uplo β i j C[(i, j)]
      else Nat.fold k (fun l hl v => syrkStepAt uplo α A j l hl i h.1 h.2 v)
        (syrkInitAt uplo β i j C[(i, j)]) := by
  unfold syrk
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => syrkInitCol uplo β C j hj)
        (fun i j _ c => syrkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_syrkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => syrkCol uplo α A β C j hj)
        (fun i j hij c => Nat.fold k (fun l hl v => syrkStepAt uplo α A j l hl i hij.1 hij.2 v)
          (syrkInitAt uplo β i j c)) (fun _ _ _ _ _ _ => getElem_syrkCol ..) C i j h n
        (Nat.le_refl _)]
      simp [h.2]

/--
The value of `syrkT` at an element `c` of the triangle, with `t = colSum id A A i j`:
`mul α t` when `β = 0`, and `mul α t + mul β c` otherwise.
-/
@[expose] public def syrkTAt (α β t c : ComplexFloat) : ComplexFloat :=
  if isZero β then mul α t else mul α t + mul β c

/--
`syrkT uplo α A β C` is `α * Aᵀ * A + β * C`, on the upper triangle of `C` (`.upper`) or its lower
triangle (`.lower`), as `zsyrk` with `TRANS = 'T'`: it returns `C` when `α = 0` or `k = 0`, and
`β = 1`; it scales the triangle as `syrkInitAt` says when `α = 0`; and otherwise sets each element
of the triangle, with the diagonal, to `syrkTAt`.
-/
@[expose] public def syrkT (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat k n)
    (β : ComplexFloat) (C : Mat n n) : Mat n n :=
  if (isZero α || k == 0) && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => syrkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => setTriCol uplo
    (fun i hi c => syrkTAt α β (colSum id A A i j hi hj) c)
    (fun c => syrkTAt α β (colSum id A A j j hj hj) c) C j hj) C

/--
Element `(i, j)` of `syrkT uplo α A β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`syrkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise `syrkTAt` with the sum
`colSum id A A i j` in the triangle, with the diagonal, and `C[i, j]` outside.
-/
public theorem getElem_syrkT (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat k n)
    (β : ComplexFloat) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (syrkT uplo α A β C)[(i, j)] =
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then syrkInitAt uplo β i j C[(i, j)]
      else if i = j ∨ InTri uplo i j then syrkTAt α β (colSum id A A i j h.1 h.2) C[(i, j)]
      else C[(i, j)] := by
  unfold syrkT
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => syrkInitCol uplo β C j hj)
        (fun i j _ c => syrkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_syrkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => setTriCol uplo
          (fun i hi c => syrkTAt α β (colSum id A A i j hi hj) c)
          (fun c => syrkTAt α β (colSum id A A j j hj hj) c) C j hj)
        (fun i j hij c => if i = j then syrkTAt α β (colSum id A A j j hij.2 hij.2) c
          else if InTri uplo i j then syrkTAt α β (colSum id A A i j hij.1 hij.2) c
          else c) (fun _ _ _ _ _ _ => getElem_setTriCol ..) C i j h n (Nat.le_refl _)]
      by_cases e : i = j
      · subst e; simp [h.2]
      · simp [h.2, e]

/--
Step `l` of column `j` of `syr2k` at element `(i, j)`, from its value `v`: unchanged when
`A[j, l] = 0` and `B[j, l] = 0`, and otherwise, with `t₁ = mul α B[j, l]` and
`t₂ = mul α A[j, l]`, `v + mul A[i, l] t₁ + mul B[i, l] t₂` in the triangle, with the diagonal, as
`zsyr2k` with `TRANS = 'N'`.
-/
@[expose] public def syr2kStepAt (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (j : Nat) (l : Nat) (hl : l < k) (i : Nat) (hi : i < n) (hj : j < n) (v : ComplexFloat) :
    ComplexFloat :=
  if isZero A[(j, l)] && isZero B[(j, l)] then v
  else if i = j ∨ InTri uplo i j then
    v + mul A[(i, l)] (mul α B[(j, l)]) + mul B[(i, l)] (mul α A[(j, l)])
  else v

/-- Step `l` of column `j` of `syr2k`, as `syr2kStepAt` says. -/
public def syr2kStep (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k) (j : Nat)
    (hj : j < n) (l : Nat) (hl : l < k) (C : Mat n n) : Mat n n :=
  if isZero A[(j, l)] && isZero B[(j, l)] then C
  else
    let h := triLo_add_triLen uplo hj
    axpyRColSlice (mul α A[(j, l)]) B l hl
      (axpyRColSlice (mul α B[(j, l)]) A l hl C j hj (triLo uplo j) (triLen uplo n j) h)
      j hj (triLo uplo j) (triLen uplo n j) h

private theorem getElem_syr2kStep (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (j : Nat) (hj : j < n) (l : Nat) (hl : l < k) (C : Mat n n) (i j' : Nat)
    (h : i < n ∧ j' < n) :
    (syr2kStep uplo α A B j hj l hl C)[(i, j')] =
      if j' = j then syr2kStepAt uplo α A B j l hl i h.1 hj C[(i, j')] else C[(i, j')] := by
  unfold syr2kStep syr2kStepAt
  by_cases hz : isZero A[(j, l)] && isZero B[(j, l)]
  · simp [hz]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, getElem_axpyRColSlice, mem_tri uplo h.1]
    by_cases e : j' = j
    · subst e
      by_cases ht : i = j' ∨ InTri uplo i j' <;> simp [ht]
    · simp [e]

/-- Column `j` of `syr2k`: `syrkInitCol`, then the steps `syr2kStep` for each `l`. -/
public def syr2kCol (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k) (β : ComplexFloat)
    (C : Mat n n) (j : Nat) (hj : j < n) : Mat n n :=
  Nat.fold k (fun l hl C => syr2kStep uplo α A B j hj l hl C) (syrkInitCol uplo β C j hj)

private theorem getElem_syr2kCol (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (β : ComplexFloat) (C : Mat n n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (syr2kCol uplo α A B β C j hj)[(i, j')] =
      if j' = j then
        Nat.fold k (fun l hl v => syr2kStepAt uplo α A B j l hl i h.1 hj v)
          (syrkInitAt uplo β i j C[(i, j')])
      else C[(i, j')] := by
  unfold syr2kCol
  rw [getElem_fold_of_pointwise (fun l hl C => syr2kStep uplo α A B j hj l hl C)
    (fun l hl i j' h v => if j' = j then syr2kStepAt uplo α A B j l hl i h.1 hj v else v)
    (fun _ _ _ _ _ _ => getElem_syr2kStep ..) _ i j' h k (Nat.le_refl _), getElem_syrkInitCol]
  by_cases e : j' = j
  · simp [e]
  · simp [e, fold_id]

/--
`syr2k uplo α A B β C` is `α * A * Bᵀ + α * B * Aᵀ + β * C`, on the upper triangle of `C`
(`.upper`) or its lower triangle (`.lower`), as `zsyr2k` with `TRANS = 'N'`: it returns `C` when
`α = 0` or `k = 0`, and `β = 1`; it scales the triangle as `syrkInitAt` says when `α = 0`; and
otherwise runs `syr2kCol` for each column in increasing order. The other triangle is unchanged.
-/
@[expose] public def syr2k (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (β : ComplexFloat) (C : Mat n n) : Mat n n :=
  if (isZero α || k == 0) && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => syrkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => syr2kCol uplo α A B β C j hj) C

/--
Element `(i, j)` of `syr2k uplo α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`syrkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise the fold of the steps `syr2kStepAt`
over `l = 0, …, k - 1` from it.
-/
public theorem getElem_syr2k (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (β : ComplexFloat) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (syr2k uplo α A B β C)[(i, j)] =
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then syrkInitAt uplo β i j C[(i, j)]
      else Nat.fold k (fun l hl v => syr2kStepAt uplo α A B j l hl i h.1 h.2 v)
        (syrkInitAt uplo β i j C[(i, j)]) := by
  unfold syr2k
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => syrkInitCol uplo β C j hj)
        (fun i j _ c => syrkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_syrkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => syr2kCol uplo α A B β C j hj)
        (fun i j hij c => Nat.fold k (fun l hl v => syr2kStepAt uplo α A B j l hl i hij.1 hij.2 v)
          (syrkInitAt uplo β i j c)) (fun _ _ _ _ _ _ => getElem_syr2kCol ..) C i j h n
        (Nat.le_refl _)]
      simp [h.2]

/--
The value of `syr2kT` at an element `c` of the triangle, with the sums `t₁ = colSum id A B i j`
and `t₂ = colSum id B A i j`: `mul α t₁ + mul α t₂` when `β = 0`, and
`mul β c + mul α t₁ + mul α t₂` otherwise.
-/
@[expose] public def syr2kTAt (α β t₁ t₂ c : ComplexFloat) : ComplexFloat :=
  if isZero β then mul α t₁ + mul α t₂ else mul β c + mul α t₁ + mul α t₂

/--
`syr2kT uplo α A B β C` is `α * Aᵀ * B + α * Bᵀ * A + β * C`, on the upper triangle of `C`
(`.upper`) or its lower triangle (`.lower`), as `zsyr2k` with `TRANS = 'T'`: it returns `C` when
`α = 0` or `k = 0`, and `β = 1`; it scales the triangle as `syrkInitAt` says when `α = 0`; and
otherwise sets each element of the triangle, with the diagonal, to `syr2kTAt`.
-/
@[expose] public def syr2kT (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat k n)
    (β : ComplexFloat) (C : Mat n n) : Mat n n :=
  if (isZero α || k == 0) && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => syrkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => setTriCol uplo
    (fun i hi c => syr2kTAt α β (colSum id A B i j hi hj) (colSum id B A i j hi hj) c)
    (fun c => syr2kTAt α β (colSum id A B j j hj hj) (colSum id B A j j hj hj) c) C j hj) C

/--
Element `(i, j)` of `syr2kT uplo α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`syrkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise `syr2kTAt` with the sums
`colSum id A B i j` and `colSum id B A i j` in the triangle, with the diagonal, and `C[i, j]`
outside.
-/
public theorem getElem_syr2kT (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat k n)
    (β : ComplexFloat) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (syr2kT uplo α A B β C)[(i, j)] =
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then syrkInitAt uplo β i j C[(i, j)]
      else if i = j ∨ InTri uplo i j then
        syr2kTAt α β (colSum id A B i j h.1 h.2) (colSum id B A i j h.1 h.2) C[(i, j)]
      else C[(i, j)] := by
  unfold syr2kT
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => syrkInitCol uplo β C j hj)
        (fun i j _ c => syrkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_syrkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => setTriCol uplo
          (fun i hi c => syr2kTAt α β (colSum id A B i j hi hj) (colSum id B A i j hi hj) c)
          (fun c => syr2kTAt α β (colSum id A B j j hj hj) (colSum id B A j j hj hj) c) C j hj)
        (fun i j hij c => if i = j then
            syr2kTAt α β (colSum id A B j j hij.2 hij.2) (colSum id B A j j hij.2 hij.2) c
          else if InTri uplo i j then
            syr2kTAt α β (colSum id A B i j hij.1 hij.2) (colSum id B A i j hij.1 hij.2) c
          else c) (fun _ _ _ _ _ _ => getElem_setTriCol ..) C i j h n (Nat.le_refl _)]
      by_cases e : i = j
      · subst e; simp [h.2]
      · simp [h.2, e]

end Mat

end BLAS.ComplexFloat64
