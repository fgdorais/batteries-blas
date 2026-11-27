/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Gemm

/-!
# Hermitian Level 3

The Hermitian routines on complex matrices: `hemm` (`C := α * A * B + β * C`) and `hemmRight`
(`C := α * B * A + β * C`) for a Hermitian `A`, `herk` (`C := α * A * Aᴴ + β * C`) and `herkC`
(`C := α * Aᴴ * A + β * C`) for real `α` and `β`, and `her2k`
(`C := α * A * Bᴴ + conj α * B * Aᴴ + β * C`) and `her2kC`
(`C := α * Aᴴ * B + conj α * Bᴴ * A + β * C`) for a real `β`, on the upper or the lower triangle
of the Hermitian matrices, as `zhemm`, `zherk` and `zher2k` in the reference BLAS (`master`), with
the same operations in the same order.

Each routine runs a step per column of `C`, in increasing order, and each step updates the column
in place when the array of `C` is not shared, by the loops of the reference BLAS.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.ComplexFloat64

namespace Mat

variable {m n k : Nat}

/-- A fold whose steps change nothing. -/
public theorem fold_id {α : Type} (K : Nat) (a : α) : Nat.fold K (fun _ _ v => v) a = a := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.fold_succ, ih]

/-! ## Updates of a slice of a column -/

/-- `C` with `g` applied to the elements of the rows `lo, …, lo + len - 1` of column `j`. -/
public def mapColSlice (g : ComplexFloat → ComplexFloat) (C : Mat m n) (j : Nat) (hj : j < n)
    (lo len : Nat) (h : lo + len ≤ m) : Mat m n :=
  C.withColSlice j hj lo len h
    (fun s => s.data.modifyStride2 s.reStride s.imStride len (fun u v => (g ⟨u, v⟩).re)
      (fun u v => (g ⟨u, v⟩).im) s.fits_re s.fits_im)
    (fun _ => by simp)

public theorem getElem_mapColSlice (g : ComplexFloat → ComplexFloat) (C : Mat m n) (j : Nat)
    (hj : j < n) (lo len : Nat) (h : lo + len ≤ m) (i j' : Nat) (hij : i < m ∧ j' < n) :
    (mapColSlice g C j hj lo len h)[(i, j')] =
      if j' = j ∧ lo ≤ i ∧ i < lo + len then g C[(i, j')] else C[(i, j')] := by
  unfold mapColSlice
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (modifyStride2_eq ..)]

/--
`C` with `mul t A[i, l]` added to each element `i` of the rows `lo, …, lo + len - 1` of column `j`,
as `axpyData t`.
-/
public def axpyColSlice (t : ComplexFloat) (A : Mat m k) (l : Nat) (hl : l < k) (C : Mat m n)
    (j : Nat) (hj : j < n) (lo len : Nat) (h : lo + len ≤ m) : Mat m n :=
  C.withColSlice j hj lo len h (fun s => Vec.axpyData t ((A.col l hl).slice lo len h) s)
    (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])

public theorem getElem_axpyColSlice (t : ComplexFloat) (A : Mat m k) (l : Nat) (hl : l < k)
    (C : Mat m n) (j : Nat) (hj : j < n) (lo len : Nat) (h : lo + len ≤ m) (i j' : Nat)
    (hij : i < m ∧ j' < n) :
    (axpyColSlice t A l hl C j hj lo len h)[(i, j')] =
      if j' = j ∧ lo ≤ i ∧ i < lo + len then C[(i, j')] + mul t A[(i, l)] else C[(i, j')] := by
  unfold axpyColSlice
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.axpyData_eq ..)]
  split
  · simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col]
    have e : lo + (i - lo) = i := by lia
    simp only [e]
    rfl
  · rfl

/--
`C` with `mul A[i, l] t` added to each element `i` of the rows `lo, …, lo + len - 1` of column `j`,
as `axpyRData t`.
-/
public def axpyRColSlice (t : ComplexFloat) (A : Mat m k) (l : Nat) (hl : l < k) (C : Mat m n)
    (j : Nat) (hj : j < n) (lo len : Nat) (h : lo + len ≤ m) : Mat m n :=
  C.withColSlice j hj lo len h (fun s => Vec.axpyRData t ((A.col l hl).slice lo len h) s)
    (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])

public theorem getElem_axpyRColSlice (t : ComplexFloat) (A : Mat m k) (l : Nat) (hl : l < k)
    (C : Mat m n) (j : Nat) (hj : j < n) (lo len : Nat) (h : lo + len ≤ m) (i j' : Nat)
    (hij : i < m ∧ j' < n) :
    (axpyRColSlice t A l hl C j hj lo len h)[(i, j')] =
      if j' = j ∧ lo ≤ i ∧ i < lo + len then C[(i, j')] + mul A[(i, l)] t else C[(i, j')] := by
  unfold axpyRColSlice
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.axpyRData_eq ..)]
  split
  · simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col]
    have e : lo + (i - lo) = i := by lia
    simp only [e]
    rfl
  · rfl

/-- `C` with each element `c` of column `j` replaced by `f c B[i, l]`, in one loop. -/
public def zipCol (f : ComplexFloat → ComplexFloat → ComplexFloat) (B : Mat m k) (l : Nat)
    (hl : l < k) (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  C.withColSlice j hj 0 m (by lia)
    (fun s => Vec.zipWithData (fun c b => (f c b).re) (fun c b => (f c b).im) (B.col l hl) s)
    (fun s => by rw [Vec.zipWithData_eq, size_modifyAt2])

public theorem getElem_zipCol (f : ComplexFloat → ComplexFloat → ComplexFloat) (B : Mat m k)
    (l : Nat) (hl : l < k) (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat)
    (hij : i < m ∧ j' < n) :
    (zipCol f B l hl C j hj)[(i, j')] =
      if j' = j then f C[(i, j')] B[(i, l)] else C[(i, j')] := by
  unfold zipCol
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  by_cases e : j' = j
  · simp only [e, Nat.zero_le, Nat.zero_add, hij.1, and_self, ↓reduceIte, Nat.sub_zero, Vec.get0,
      ↓reduceDIte, getElem_col]
  · simp [e]

/-! ## `hemm` -/

/-- Element `(i, j)` of the Hermitian matrix stored in the triangle `uplo` of `A`, for `i ≠ j`. -/
@[expose] public def hermAt (uplo : Float64.Uplo) (A : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    ComplexFloat :=
  if InTri uplo i j then A[(i, j)] else A[(j, i)].conj

/--
The sum `0 + mul B[0, j] (conj A[0, i]) + …` of `hemm` over the rows `l` in the triangle of
column `i` of `A`, other than the diagonal: `l < i` in the upper triangle and `l > i` in the lower
one, in increasing order.
-/
@[expose] public def hemmDot (uplo : Float64.Uplo) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (hi : i < m) (hj : j < n) : ComplexFloat :=
  if uplo = .upper then
    Vec.accWith id ComplexFloat.conj (· + ·) zero ((B.col j hj).slice 0 i (by lia))
      ((A.col i hi).slice 0 i (by lia))
  else
    Vec.accWith id ComplexFloat.conj (· + ·) zero ((B.col j hj).slice (i + 1) (m - (i + 1))
      (by lia)) ((A.col i hi).slice (i + 1) (m - (i + 1)) (by lia))

/--
The new value of the element `(i, i)` of a step of `hemm` from its old value `c`: `d + s` when
`β = 0`, and `mul β c + d + s` otherwise.
-/
@[expose] public def hemmAt (β d s c : ComplexFloat) : ComplexFloat :=
  if isZero β then d + s else mul β c + d + s

/--
The row of step `s` of `hemm`: `s` in the upper triangle, from the first row, and `m - 1 - s` in
the lower one, from the last row.
-/
@[expose] public def hemmRow (uplo : Float64.Uplo) (m s : Nat) : Nat :=
  if uplo = .upper then s else m - 1 - s

public theorem hemmRow_lt (uplo : Float64.Uplo) {m s : Nat} (h : s < m) : hemmRow uplo m s < m := by
  unfold hemmRow; split <;> lia

/--
The step of `hemm` for row `i` of column `j` of `C`: with `t₁ = mul α B[i, j]`, it adds
`mul t₁ A[l, i]` to the elements `l` of the column in the triangle of column `i` of `A`, and then
sets element `i` to `hemmAt β (mulr t₁ A[i, i].re) (mul α (hemmDot uplo A B i j))` of its value, as
`zhemm` with `SIDE = 'L'`.
-/
public def hemmStep (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) (C : Mat m n) : Mat m n :=
  let t₁ := mul α B[(i, j)]
  let C :=
    if uplo = .upper then axpyColSlice t₁ A i hi C j hj 0 i (by lia)
    else axpyColSlice t₁ A i hi C j hj (i + 1) (m - (i + 1)) (by lia)
  C.setAt i j ⟨hi, hj⟩
    (hemmAt β (mulr t₁ A[(i, i)].re) (mul α (hemmDot uplo A B i j hi hj)) C[(i, j)])

/-- The step `hemmStep` at element `l` of column `j`, from its old value `v`. -/
@[expose] public def hemmStepAt (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m)
    (B : Mat m n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) (l : Nat) (hl : l < m)
    (v : ComplexFloat) : ComplexFloat :=
  if l = i then
    hemmAt β (mulr (mul α B[(i, j)]) A[(i, i)].re) (mul α (hemmDot uplo A B i j hi hj)) v
  else if InTri uplo l i then v + mul (mul α B[(i, j)]) A[(l, i)]
  else v

private theorem getElem_hemmStep (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m)
    (B : Mat m n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < m) (C : Mat m n) (l j' : Nat)
    (h : l < m ∧ j' < n) :
    (hemmStep uplo α β A B j hj i hi C)[(l, j')] =
      if j' = j then hemmStepAt uplo α β A B j hj i hi l h.1 C[(l, j')] else C[(l, j')] := by
  unfold hemmStep hemmStepAt
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

/-- Column `j` of `hemm`: the steps `hemmStep` for each row, in the order of `hemmRow`. -/
public def hemmCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  Nat.fold m (fun s hs C => hemmStep uplo α β A B j hj (hemmRow uplo m s) (hemmRow_lt uplo hs) C) C

private theorem getElem_hemmCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat m m)
    (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) (l j' : Nat) (h : l < m ∧ j' < n) :
    (hemmCol uplo α β A B C j hj)[(l, j')] =
      if j' = j then
        Nat.fold m (fun s hs v => hemmStepAt uplo α β A B j hj (hemmRow uplo m s)
          (hemmRow_lt uplo hs) l h.1 v) C[(l, j')]
      else C[(l, j')] := by
  unfold hemmCol
  rw [getElem_fold_of_pointwise
    (fun s hs C => hemmStep uplo α β A B j hj (hemmRow uplo m s) (hemmRow_lt uplo hs) C)
    (fun s hs l j' h v => if j' = j then hemmStepAt uplo α β A B j hj (hemmRow uplo m s)
      (hemmRow_lt uplo hs) l h.1 v else v)
    (fun _ _ _ _ _ _ => getElem_hemmStep ..) C l j' h m (Nat.le_refl _)]
  by_cases e : j' = j
  · simp [e]
  · simp only [e, ↓reduceIte, fold_id]

/--
`hemm uplo α A B β C` is `α * A * B + β * C` for the Hermitian matrix `A` stored in its upper
triangle (`.upper`) or its lower triangle (`.lower`), as `zhemm` with `SIDE = 'L'`: it returns `C`
when `α = 0` and `β = 1`, scales `C` by `β` (`betaMul`) when `α = 0`, and otherwise runs
`hemmCol` for each column in increasing order. It reads only the real part of the diagonal of `A`.
-/
@[expose] public def hemm (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (β : ComplexFloat) (C : Mat m n) : Mat m n :=
  if isZero α && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => betaCol β C j hj) C
  else Nat.fold n (fun j hj C => hemmCol uplo α β A B C j hj) C

/--
Element `(i, j)` of `hemm uplo α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise the
fold of the steps `hemmStepAt` over the rows in the order of `hemmRow`, from `C[i, j]`.
-/
public theorem getElem_hemm (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat m m) (B : Mat m n)
    (β : ComplexFloat) (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (hemm uplo α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold m (fun s hs v => hemmStepAt uplo α β A B j h.2 (hemmRow uplo m s)
        (hemmRow_lt uplo hs) i h.1 v) C[(i, j)] := by
  unfold hemm
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp only [ha, hb, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [getElem_fold_col (fun j hj C => betaCol β C j hj) (fun i j _ c => betaMul β c)
        (fun _ _ _ _ _ _ => getElem_betaCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]
  · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => hemmCol uplo α β A B C j hj)
      (fun i j hij c => Nat.fold m (fun s hs v => hemmStepAt uplo α β A B j hij.2
        (hemmRow uplo m s) (hemmRow_lt uplo hs) i hij.1 v) c)
      (fun _ _ _ _ _ _ => getElem_hemmCol ..) C i j h n (Nat.le_refl _)]
    simp [h.2]

/-! ## `hemmRight` -/

/--
The first value of element `c` of column `j` of `hemmRight`, with `b = B[i, j]`:
`mul t₁ b` when `β = 0`, and `mul β c + mul t₁ b` otherwise, where `t₁ = mulr α A[j, j].re`.
-/
@[expose] public def hemmRightInit (α β : ComplexFloat) (a : Float) (c b : ComplexFloat) :
    ComplexFloat :=
  if isZero β then mul (mulr α a) b else mul β c + mul (mulr α a) b

/--
Column `j` of `hemmRight`: each element `c` becomes `hemmRightInit α β A[j, j].re c B[i, j]`, and
then gets `mul (mul α (hermAt uplo A l j)) B[i, l]` for each column `l ≠ j` of `B`, in increasing
order, as `zhemm` with `SIDE = 'R'`.
-/
public def hemmRightCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat n n) (B : Mat m n)
    (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  let a := A[(j, j)].re
  let C := zipCol (fun c b => hemmRightInit α β a c b) B j hj C j hj
  Nat.fold n (fun l hl C => if l = j then C
    else axpyColSlice (mul α (hermAt uplo A l j ⟨hl, hj⟩)) B l hl C j hj 0 m (by lia)) C

private theorem getElem_hemmRightCol (uplo : Float64.Uplo) (α β : ComplexFloat) (A : Mat n n)
    (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (hemmRightCol uplo α β A B C j hj)[(i, j')] =
      if j' = j then
        Nat.fold n (fun l hl v => if l = j then v
          else v + mul (mul α (hermAt uplo A l j ⟨hl, hj⟩)) B[(i, l)])
          (hemmRightInit α β A[(j, j)].re C[(i, j')] B[(i, j)])
      else C[(i, j')] := by
  unfold hemmRightCol
  rw [getElem_fold_of_pointwise
    (fun l hl C => if l = j then C
      else axpyColSlice (mul α (hermAt uplo A l j ⟨hl, hj⟩)) B l hl C j hj 0 m (by lia))
    (fun l hl i j' h v => if j' = j then (if l = j then v
      else v + mul (mul α (hermAt uplo A l j ⟨hl, hj⟩)) B[(i, l)]) else v)
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
`hemmRight uplo α A B β C` is `α * B * A + β * C` for the Hermitian matrix `A` stored in its upper
triangle (`.upper`) or its lower triangle (`.lower`), as `zhemm` with `SIDE = 'R'`: it returns `C`
when `α = 0` and `β = 1`, scales `C` by `β` (`betaMul`) when `α = 0`, and otherwise runs
`hemmRightCol` for each column in increasing order. It reads only the real part of the diagonal
of `A`.
-/
@[expose] public def hemmRight (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n n)
    (B : Mat m n) (β : ComplexFloat) (C : Mat m n) : Mat m n :=
  if isZero α && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => betaCol β C j hj) C
  else Nat.fold n (fun j hj C => hemmRightCol uplo α β A B C j hj) C

/--
Element `(i, j)` of `hemmRight uplo α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise
`hemmRightInit α β A[j, j].re C[i, j] B[i, j]` plus `mul (mul α (hermAt uplo A l j)) B[i, l]` for
each `l ≠ j`, in increasing order, from the left.
-/
public theorem getElem_hemmRight (uplo : Float64.Uplo) (α : ComplexFloat) (A : Mat n n)
    (B : Mat m n) (β : ComplexFloat) (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (hemmRight uplo α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold n (fun l hl v => if l = j then v
          else v + mul (mul α (hermAt uplo A l j ⟨hl, h.2⟩)) B[(i, l)])
          (hemmRightInit α β A[(j, j)].re C[(i, j)] B[(i, j)]) := by
  unfold hemmRight
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp only [ha, hb, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [getElem_fold_col (fun j hj C => betaCol β C j hj) (fun i j _ c => betaMul β c)
        (fun _ _ _ _ _ _ => getElem_betaCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]
  · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => hemmRightCol uplo α β A B C j hj)
      (fun i j hij c => Nat.fold n (fun l hl v => if l = j then v
          else v + mul (mul α (hermAt uplo A l j ⟨hl, hij.2⟩)) B[(i, l)])
          (hemmRightInit α β A[(j, j)].re c B[(i, j)]))
      (fun _ _ _ _ _ _ => getElem_hemmRightCol ..) C i j h n (Nat.le_refl _)]
    simp [h.2]

/-! ## `herk` and `her2k` -/

/--
The scaling of element `(i, j)` of `C`, from its value `c`, by a real `β` in `zherk` and `zher2k`:
in the triangle, zeros when `β = 0`, and otherwise `mul (ofReal β) c` off the diagonal (unchanged
when `β = 1`) and `ofReal (β * c.re)` on it (`ofReal c.re` when `β = 1`); `c` outside.
-/
@[expose] public def herkInitAt (uplo : Float64.Uplo) (β : Float) (i j : Nat)
    (c : ComplexFloat) : ComplexFloat :=
  if i = j then (if β == 0 then zero else if β == 1 then ofReal c.re else ofReal (β * c.re))
  else if InTri uplo i j then (if β == 0 then zero else if β == 1 then c else mul (ofReal β) c)
  else c

/-- Column `j` of `C` scaled as `herkInitAt` says, in the triangle. -/
public def herkInitCol (uplo : Float64.Uplo) (β : Float) (C : Mat n n) (j : Nat) (hj : j < n) :
    Mat n n :=
  if β == 0 then
    if uplo = .upper then mapColSlice (fun _ => zero) C j hj 0 (j + 1) (by lia)
    else mapColSlice (fun _ => zero) C j hj j (n - j) (by lia)
  else if β == 1 then C.setAt j j ⟨hj, hj⟩ (ofReal C[(j, j)].re)
  else
    let C :=
      if uplo = .upper then mapColSlice (mul (ofReal β)) C j hj 0 j (by lia)
      else mapColSlice (mul (ofReal β)) C j hj (j + 1) (n - (j + 1)) (by lia)
    C.setAt j j ⟨hj, hj⟩ (ofReal (β * C[(j, j)].re))

private theorem getElem_herkInitCol (uplo : Float64.Uplo) (β : Float) (C : Mat n n) (j : Nat)
    (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (herkInitCol uplo β C j hj)[(i, j')] =
      if j' = j then herkInitAt uplo β i j C[(i, j')] else C[(i, j')] := by
  unfold herkInitCol herkInitAt
  by_cases e : j' = j
  · subst e
    by_cases h0 : β == 0
    · cases uplo
      · simp only [h0, ↓reduceIte, getElem_mapColSlice, true_and, InTri]
        by_cases e' : i = j'
        · subst e'; simp
        · by_cases hl : i < j'
          · simp [e', hl, show i < j' + 1 by lia]
          · simp [e', hl, show ¬ i < j' + 1 by lia]
      · simp only [h0, reduceCtorEq, ↓reduceIte, getElem_mapColSlice, true_and, InTri]
        by_cases e' : i = j'
        · subst e'; simp [show i < i + (n - i) by lia]
        · by_cases hl : j' < i
          · simp [e', hl, show j' ≤ i by lia, show i < j' + (n - j') by lia]
          · simp [e', hl, show ¬ j' ≤ i by lia]
    · by_cases h1 : β == 1
      · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, getElem_setAt, and_true]
        by_cases e' : i = j'
        · subst e'; simp
        · simp only [e', ↓reduceIte, ite_self]
      · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, getElem_setAt, and_true]
        cases uplo
        · simp only [↓reduceIte, getElem_mapColSlice, true_and, InTri, Nat.zero_le, Nat.zero_add]
          by_cases e' : i = j'
          · subst e'; simp
          · by_cases hl : i < j'
            · simp [e', hl]
            · simp [e', hl]
        · simp only [reduceCtorEq, ↓reduceIte, getElem_mapColSlice, true_and, InTri]
          by_cases e' : i = j'
          · subst e'; simp [show ¬ (i + 1 ≤ i) by lia]
          · by_cases hl : j' < i
            · simp [e', hl, show j' + 1 ≤ i by lia, show i < j' + 1 + (n - (j' + 1)) by lia]
            · simp [e', hl, show ¬ j' + 1 ≤ i by lia]
  · have hne : ¬ (i = j ∧ j' = j) := fun h => e h.2
    by_cases h0 : β == 0
    · cases uplo <;> simp [h0, e, getElem_mapColSlice]
    · by_cases h1 : β == 1
      · simp [h0, h1, e, getElem_setAt]
      · cases uplo <;> simp [h0, h1, e, getElem_setAt, getElem_mapColSlice]

/--
Step `l` of column `j` of `herk` at element `(i, j)`, from its value `v`: unchanged when
`A[j, l] = 0`, and otherwise, with `t = mul (ofReal α) (conj A[j, l])`, `v + mul t A[i, l]` in the
triangle and `ofReal (v.re + (mul t A[j, l]).re)` on the diagonal, as `zherk` with `TRANS = 'N'`.
-/
@[expose] public def herkStepAt (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (j : Nat)
    (hj : j < n) (l : Nat) (hl : l < k) (i : Nat) (hi : i < n) (v : ComplexFloat) :
    ComplexFloat :=
  if isZero A[(j, l)] then v
  else
    let t := mul (ofReal α) A[(j, l)].conj
    if i = j then ofReal (v.re + (mul t A[(j, l)]).re)
    else if InTri uplo i j then v + mul t A[(i, l)]
    else v

/-- Step `l` of column `j` of `herk`, as `herkStepAt` says. -/
public def herkStep (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (j : Nat) (hj : j < n)
    (l : Nat) (hl : l < k) (C : Mat n n) : Mat n n :=
  if isZero A[(j, l)] then C
  else
    let t := mul (ofReal α) A[(j, l)].conj
    let C :=
      if uplo = .upper then axpyColSlice t A l hl C j hj 0 j (by lia)
      else axpyColSlice t A l hl C j hj (j + 1) (n - (j + 1)) (by lia)
    C.setAt j j ⟨hj, hj⟩ (ofReal (C[(j, j)].re + (mul t A[(j, l)]).re))

private theorem getElem_herkStep (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (j : Nat)
    (hj : j < n) (l : Nat) (hl : l < k) (C : Mat n n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (herkStep uplo α A j hj l hl C)[(i, j')] =
      if j' = j then herkStepAt uplo α A j hj l hl i h.1 C[(i, j')] else C[(i, j')] := by
  unfold herkStep herkStepAt
  by_cases hz : isZero A[(j, l)]
  · simp [hz]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, getElem_setAt]
    by_cases e : j' = j
    · subst e
      cases uplo
      · simp only [↓reduceIte, getElem_axpyColSlice, true_and, InTri, Nat.zero_le, Nat.zero_add,
          and_true]
        by_cases e' : i = j'
        · subst e'; simp
        · simp [e']
      · simp only [reduceCtorEq, ↓reduceIte, getElem_axpyColSlice, true_and, InTri, and_true,
          false_and, false_or]
        by_cases e' : i = j'
        · subst e'; simp [show ¬ (i + 1 ≤ i) by lia]
        · by_cases hl' : j' < i
          · simp [e', hl', show j' + 1 ≤ i by lia, show i < j' + 1 + (n - (j' + 1)) by lia]
          · simp [e', hl', show ¬ j' + 1 ≤ i by lia]
    · cases uplo <;> simp [e, getElem_axpyColSlice]

/-- Column `j` of `herk`: `herkInitCol`, then the steps `herkStep` for each `l`. -/
public def herkCol (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (β : Float) (C : Mat n n)
    (j : Nat) (hj : j < n) : Mat n n :=
  Nat.fold k (fun l hl C => herkStep uplo α A j hj l hl C) (herkInitCol uplo β C j hj)

private theorem getElem_herkCol (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (β : Float)
    (C : Mat n n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (herkCol uplo α A β C j hj)[(i, j')] =
      if j' = j then
        Nat.fold k (fun l hl v => herkStepAt uplo α A j hj l hl i h.1 v)
          (herkInitAt uplo β i j C[(i, j')])
      else C[(i, j')] := by
  unfold herkCol
  rw [getElem_fold_of_pointwise (fun l hl C => herkStep uplo α A j hj l hl C)
    (fun l hl i j' h v => if j' = j then herkStepAt uplo α A j hj l hl i h.1 v else v)
    (fun _ _ _ _ _ _ => getElem_herkStep ..) _ i j' h k (Nat.le_refl _), getElem_herkInitCol]
  by_cases e : j' = j
  · simp [e]
  · simp [e, fold_id]

/--
`herk uplo α A β C` is `α * A * Aᴴ + β * C` for real `α` and `β`, on the upper triangle of `C`
(`.upper`) or its lower triangle (`.lower`), as `zherk` with `TRANS = 'N'`: it returns `C` when
`α = 0` or `k = 0`, and `β = 1`; it scales the triangle as `herkInitAt` says when `α = 0`; and
otherwise runs `herkCol` for each column in increasing order. The other triangle is unchanged, and
the diagonal of the result is real.
-/
@[expose] public def herk (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (β : Float)
    (C : Mat n n) : Mat n n :=
  if (α == 0 || k == 0) && β == 1 then C
  else if α == 0 then Nat.fold n (fun j hj C => herkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => herkCol uplo α A β C j hj) C

/--
Element `(i, j)` of `herk uplo α A β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`herkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise the fold of the steps `herkStepAt`
over `l = 0, …, k - 1` from it.
-/
public theorem getElem_herk (uplo : Float64.Uplo) (α : Float) (A : Mat n k) (β : Float)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (herk uplo α A β C)[(i, j)] =
      if (α == 0 || k == 0) && β == 1 then C[(i, j)]
      else if α == 0 then herkInitAt uplo β i j C[(i, j)]
      else Nat.fold k (fun l hl v => herkStepAt uplo α A j h.2 l hl i h.1 v)
        (herkInitAt uplo β i j C[(i, j)]) := by
  unfold herk
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => herkInitCol uplo β C j hj)
        (fun i j _ c => herkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_herkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => herkCol uplo α A β C j hj)
        (fun i j hij c => Nat.fold k (fun l hl v => herkStepAt uplo α A j hij.2 l hl i hij.1 v)
          (herkInitAt uplo β i j c)) (fun _ _ _ _ _ _ => getElem_herkCol ..) C i j h n
        (Nat.le_refl _)]
      simp [h.2]

/--
Column `j` of `C` with element `(i, j)` set to `f i c` for each `i` in the triangle other than the
diagonal, and the diagonal element set to `fd c`, where `c` is the old value.
-/
@[specialize] public def setTriCol (uplo : Float64.Uplo)
    (f : (i : Nat) → i < n → ComplexFloat → ComplexFloat) (fd : ComplexFloat → ComplexFloat)
    (C : Mat n n) (j : Nat) (hj : j < n) : Mat n n :=
  Nat.fold n (fun i hi C =>
    if i = j then C.setAt j j ⟨hj, hj⟩ (fd C[(j, j)])
    else if InTri uplo i j then C.setAt i j ⟨hi, hj⟩ (f i hi C[(i, j)])
    else C) C

public theorem getElem_setTriCol (uplo : Float64.Uplo)
    (f : (i : Nat) → i < n → ComplexFloat → ComplexFloat) (fd : ComplexFloat → ComplexFloat)
    (C : Mat n n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (setTriCol uplo f fd C j hj)[(i, j')] =
      if j' = j then
        (if i = j then fd C[(i, j')] else if InTri uplo i j then f i h.1 C[(i, j')] else C[(i, j')])
      else C[(i, j')] := by
  unfold setTriCol
  rw [getElem_fold_of_pointwise (fun i hi C =>
    if i = j then C.setAt j j ⟨hj, hj⟩ (fd C[(j, j)])
    else if InTri uplo i j then C.setAt i j ⟨hi, hj⟩ (f i hi C[(i, j)])
    else C)
    (fun i' hi' i j' h v => if j' = j ∧ i = i' then
      (if i' = j then fd v else if InTri uplo i' j then f i' hi' v else v) else v)
    (fun i' hi' B i j' h => by
      by_cases e : i' = j
      · subst e
        simp only [↓reduceIte, getElem_setAt]
        by_cases e2 : i = i' ∧ j' = i'
        · obtain ⟨rfl, rfl⟩ := e2; simp
        · have : ¬ (j' = i' ∧ i = i') := fun ⟨a, b⟩ => e2 ⟨b, a⟩
          simp only [e2, this, ↓reduceIte]
      · simp only [e, ↓reduceIte]
        by_cases ht : InTri uplo i' j
        · simp only [ht, ↓reduceIte, getElem_setAt]
          by_cases e2 : i = i' ∧ j' = j
          · obtain ⟨rfl, rfl⟩ := e2; simp
          · have : ¬ (j' = j ∧ i = i') := fun ⟨a, b⟩ => e2 ⟨b, a⟩
            simp only [e2, this, ↓reduceIte]
        · simp only [ht, ↓reduceIte]
          by_cases e2 : j' = j ∧ i = i'
          · simp [e2]
          · simp [e2])
    C i j' h n (Nat.le_refl _)]
  have key : ∀ K (hK : K ≤ n) (v : ComplexFloat), Nat.fold K (fun i' hi' w =>
      if j' = j ∧ i = i' then
        (if i' = j then fd w else if InTri uplo i' j then f i' (by lia) w else w) else w) v =
      if j' = j ∧ i < K then
        (if i = j then fd v else if InTri uplo i j then f i h.1 v else v) else v := by
    intro K hK v
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.fold_succ, ih (by lia)]
      by_cases e : j' = j ∧ i = K
      · obtain ⟨rfl, rfl⟩ := e
        simp
      · by_cases e' : j' = j
        · have : i ≠ K := fun h => e ⟨e', h⟩
          have h2 : (i < K + 1) = (i < K) := by apply propext; lia
          simp [e', this, h2]
        · simp [e']
  rw [key n (Nat.le_refl _)]
  simp [h.1]

/-- The sum `0 + mul (p A[0, i]) B[0, j] + … + mul (p A[k - 1, i]) B[k - 1, j]`, from the left. -/
@[inline, expose] public def colSum (p : ComplexFloat → ComplexFloat) (A B : Mat k n)
    (i j : Nat) (hi : i < n) (hj : j < n) : ComplexFloat :=
  Vec.accWith p id (· + ·) zero (A.col i hi) (B.col j hj)

public theorem colSum_eq (p : ComplexFloat → ComplexFloat) (A B : Mat k n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    colSum p A B i j hi hj = Nat.fold k (fun l hl s => s + mul (p A[(l, i)]) B[(l, j)]) zero := by
  simp [colSum, Vec.accWith_eq]

/--
The value of `herkC` at an element `c` of the triangle other than the diagonal, with
`t = colSum conj A A i j`: `mul (ofReal α) t`, plus `mul (ofReal β) c` unless `β = 0`.
-/
@[expose] public def herkCAt (α β : Float) (t c : ComplexFloat) : ComplexFloat :=
  if β == 0 then mul (ofReal α) t else mul (ofReal α) t + mul (ofReal β) c

/--
The value of `herkC` on the diagonal, from `c`, with `r = (colSum conj A A j j).re`:
`ofReal (α * r)`, plus `β * c.re` in the real part unless `β = 0`.
-/
@[expose] public def herkCDiag (α β r : Float) (c : ComplexFloat) : ComplexFloat :=
  if β == 0 then ofReal (α * r) else ofReal (α * r + β * c.re)

/--
`herkC uplo α A β C` is `α * Aᴴ * A + β * C` for real `α` and `β`, on the upper triangle of `C`
(`.upper`) or its lower triangle (`.lower`), as `zherk` with `TRANS = 'C'`: it returns `C` when
`α = 0` or `k = 0`, and `β = 1`; it scales the triangle as `herkInitAt` says when `α = 0`; and
otherwise sets each element of the triangle to `herkCAt`, or `herkCDiag` on the diagonal.
-/
@[expose] public def herkC (uplo : Float64.Uplo) (α : Float) (A : Mat k n) (β : Float)
    (C : Mat n n) : Mat n n :=
  if (α == 0 || k == 0) && β == 1 then C
  else if α == 0 then Nat.fold n (fun j hj C => herkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => setTriCol uplo
    (fun i hi c => herkCAt α β (colSum ComplexFloat.conj A A i j hi hj) c)
    (fun c => herkCDiag α β (colSum ComplexFloat.conj A A j j hj hj).re c) C j hj) C

/--
Element `(i, j)` of `herkC uplo α A β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`herkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise `herkCDiag` on the diagonal and
`herkCAt` in the triangle, with the sums `colSum conj A A i j`, and `C[i, j]` outside.
-/
public theorem getElem_herkC (uplo : Float64.Uplo) (α : Float) (A : Mat k n) (β : Float)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (herkC uplo α A β C)[(i, j)] =
      if (α == 0 || k == 0) && β == 1 then C[(i, j)]
      else if α == 0 then herkInitAt uplo β i j C[(i, j)]
      else if i = j then herkCDiag α β (colSum ComplexFloat.conj A A j j h.2 h.2).re C[(i, j)]
      else if InTri uplo i j then herkCAt α β (colSum ComplexFloat.conj A A i j h.1 h.2) C[(i, j)]
      else C[(i, j)] := by
  unfold herkC
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => herkInitCol uplo β C j hj)
        (fun i j _ c => herkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_herkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => setTriCol uplo
          (fun i hi c => herkCAt α β (colSum ComplexFloat.conj A A i j hi hj) c)
          (fun c => herkCDiag α β (colSum ComplexFloat.conj A A j j hj hj).re c) C j hj)
        (fun i j hij c => if i = j then herkCDiag α β (colSum ComplexFloat.conj A A j j hij.2
            hij.2).re c
          else if InTri uplo i j then herkCAt α β (colSum ComplexFloat.conj A A i j hij.1 hij.2) c
          else c) (fun _ _ _ _ _ _ => getElem_setTriCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]

/--
Step `l` of column `j` of `her2k` at element `(i, j)`, from its value `v`: unchanged when
`A[j, l] = 0` and `B[j, l] = 0`, and otherwise, with `t₁ = mul α (conj B[j, l])` and
`t₂ = conj (mul α A[j, l])`, `v + mul A[i, l] t₁ + mul B[i, l] t₂` in the triangle and
`ofReal (v.re + (mul A[j, l] t₁ + mul B[j, l] t₂).re)` on the diagonal, as `zher2k` with
`TRANS = 'N'`.
-/
@[expose] public def her2kStepAt (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (j : Nat) (hj : j < n) (l : Nat) (hl : l < k) (i : Nat) (hi : i < n) (v : ComplexFloat) :
    ComplexFloat :=
  if isZero A[(j, l)] && isZero B[(j, l)] then v
  else
    let t₁ := mul α B[(j, l)].conj
    let t₂ := (mul α A[(j, l)]).conj
    if i = j then ofReal (v.re + (mul A[(j, l)] t₁ + mul B[(j, l)] t₂).re)
    else if InTri uplo i j then v + mul A[(i, l)] t₁ + mul B[(i, l)] t₂
    else v

/-- Step `l` of column `j` of `her2k`, as `her2kStepAt` says. -/
public def her2kStep (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k) (j : Nat)
    (hj : j < n) (l : Nat) (hl : l < k) (C : Mat n n) : Mat n n :=
  if isZero A[(j, l)] && isZero B[(j, l)] then C
  else
    let t₁ := mul α B[(j, l)].conj
    let t₂ := (mul α A[(j, l)]).conj
    let C :=
      if uplo = .upper then
        axpyRColSlice t₂ B l hl (axpyRColSlice t₁ A l hl C j hj 0 j (by lia)) j hj 0 j (by lia)
      else
        axpyRColSlice t₂ B l hl (axpyRColSlice t₁ A l hl C j hj (j + 1) (n - (j + 1)) (by lia))
          j hj (j + 1) (n - (j + 1)) (by lia)
    C.setAt j j ⟨hj, hj⟩ (ofReal (C[(j, j)].re + (mul A[(j, l)] t₁ + mul B[(j, l)] t₂).re))

private theorem getElem_her2kStep (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (j : Nat) (hj : j < n) (l : Nat) (hl : l < k) (C : Mat n n) (i j' : Nat)
    (h : i < n ∧ j' < n) :
    (her2kStep uplo α A B j hj l hl C)[(i, j')] =
      if j' = j then her2kStepAt uplo α A B j hj l hl i h.1 C[(i, j')] else C[(i, j')] := by
  unfold her2kStep her2kStepAt
  by_cases hz : isZero A[(j, l)] && isZero B[(j, l)]
  · simp [hz]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, getElem_setAt]
    by_cases e : j' = j
    · subst e
      cases uplo
      · simp only [↓reduceIte, getElem_axpyRColSlice, true_and, InTri, Nat.zero_le, Nat.zero_add,
          and_true]
        by_cases e' : i = j'
        · subst e'; simp
        · by_cases hl' : i < j'
          · simp [e', hl']
          · simp [e', hl']
      · simp only [reduceCtorEq, ↓reduceIte, getElem_axpyRColSlice, true_and, InTri, and_true,
          false_and, false_or]
        by_cases e' : i = j'
        · subst e'; simp [show ¬ (i + 1 ≤ i) by lia]
        · by_cases hl' : j' < i
          · simp [e', hl', show j' + 1 ≤ i by lia, show i < j' + 1 + (n - (j' + 1)) by lia]
          · simp [e', hl', show ¬ j' + 1 ≤ i by lia]
    · cases uplo <;> simp [e, getElem_axpyRColSlice]

/-- Column `j` of `her2k`: `herkInitCol`, then the steps `her2kStep` for each `l`. -/
public def her2kCol (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k) (β : Float)
    (C : Mat n n) (j : Nat) (hj : j < n) : Mat n n :=
  Nat.fold k (fun l hl C => her2kStep uplo α A B j hj l hl C) (herkInitCol uplo β C j hj)

private theorem getElem_her2kCol (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (β : Float) (C : Mat n n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (her2kCol uplo α A B β C j hj)[(i, j')] =
      if j' = j then
        Nat.fold k (fun l hl v => her2kStepAt uplo α A B j hj l hl i h.1 v)
          (herkInitAt uplo β i j C[(i, j')])
      else C[(i, j')] := by
  unfold her2kCol
  rw [getElem_fold_of_pointwise (fun l hl C => her2kStep uplo α A B j hj l hl C)
    (fun l hl i j' h v => if j' = j then her2kStepAt uplo α A B j hj l hl i h.1 v else v)
    (fun _ _ _ _ _ _ => getElem_her2kStep ..) _ i j' h k (Nat.le_refl _), getElem_herkInitCol]
  by_cases e : j' = j
  · simp [e]
  · simp [e, fold_id]

/--
`her2k uplo α A B β C` is `α * A * Bᴴ + conj α * B * Aᴴ + β * C` for a real `β`, on the upper
triangle of `C` (`.upper`) or its lower triangle (`.lower`), as `zher2k` with `TRANS = 'N'`: it
returns `C` when `α = 0` or `k = 0`, and `β = 1`; it scales the triangle as `herkInitAt` says when
`α = 0`; and otherwise runs `her2kCol` for each column in increasing order. The other triangle is
unchanged, and the diagonal of the result is real.
-/
@[expose] public def her2k (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k) (β : Float)
    (C : Mat n n) : Mat n n :=
  if (isZero α || k == 0) && β == 1 then C
  else if isZero α then Nat.fold n (fun j hj C => herkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => her2kCol uplo α A B β C j hj) C

/--
Element `(i, j)` of `her2k uplo α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`herkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise the fold of the steps `her2kStepAt`
over `l = 0, …, k - 1` from it.
-/
public theorem getElem_her2k (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat n k)
    (β : Float) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (her2k uplo α A B β C)[(i, j)] =
      if (isZero α || k == 0) && β == 1 then C[(i, j)]
      else if isZero α then herkInitAt uplo β i j C[(i, j)]
      else Nat.fold k (fun l hl v => her2kStepAt uplo α A B j h.2 l hl i h.1 v)
        (herkInitAt uplo β i j C[(i, j)]) := by
  unfold her2k
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => herkInitCol uplo β C j hj)
        (fun i j _ c => herkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_herkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => her2kCol uplo α A B β C j hj)
        (fun i j hij c => Nat.fold k (fun l hl v => her2kStepAt uplo α A B j hij.2 l hl i hij.1 v)
          (herkInitAt uplo β i j c)) (fun _ _ _ _ _ _ => getElem_her2kCol ..) C i j h n
        (Nat.le_refl _)]
      simp [h.2]

/--
The value of `her2kC` at an element `c` of the triangle other than the diagonal, with the sums
`t₁ = colSum conj A B i j` and `t₂ = colSum conj B A i j`: `mul α t₁ + mul (conj α) t₂` when
`β = 0`, and `mul (ofReal β) c + mul α t₁ + mul (conj α) t₂` otherwise.
-/
@[expose] public def her2kCAt (α : ComplexFloat) (β : Float) (t₁ t₂ c : ComplexFloat) :
    ComplexFloat :=
  if β == 0 then mul α t₁ + mul α.conj t₂ else mul (ofReal β) c + mul α t₁ + mul α.conj t₂

/--
The value of `her2kC` on the diagonal, from `c`: the real part of `mul α t₁ + mul (conj α) t₂`,
plus `β * c.re` before it unless `β = 0`.
-/
@[expose] public def her2kCDiag (α : ComplexFloat) (β : Float) (t₁ t₂ c : ComplexFloat) :
    ComplexFloat :=
  if β == 0 then ofReal (mul α t₁ + mul α.conj t₂).re
  else ofReal (β * c.re + (mul α t₁ + mul α.conj t₂).re)

/--
`her2kC uplo α A B β C` is `α * Aᴴ * B + conj α * Bᴴ * A + β * C` for a real `β`, on the upper
triangle of `C` (`.upper`) or its lower triangle (`.lower`), as `zher2k` with `TRANS = 'C'`: it
returns `C` when `α = 0` or `k = 0`, and `β = 1`; it scales the triangle as `herkInitAt` says when
`α = 0`; and otherwise sets each element of the triangle to `her2kCAt`, or `her2kCDiag` on the
diagonal.
-/
@[expose] public def her2kC (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat k n) (β : Float)
    (C : Mat n n) : Mat n n :=
  if (isZero α || k == 0) && β == 1 then C
  else if isZero α then Nat.fold n (fun j hj C => herkInitCol uplo β C j hj) C
  else Nat.fold n (fun j hj C => setTriCol uplo
    (fun i hi c => her2kCAt α β (colSum ComplexFloat.conj A B i j hi hj)
      (colSum ComplexFloat.conj B A i j hi hj) c)
    (fun c => her2kCDiag α β (colSum ComplexFloat.conj A B j j hj hj)
      (colSum ComplexFloat.conj B A j j hj hj) c) C j hj) C

/--
Element `(i, j)` of `her2kC uplo α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`herkInitAt uplo β i j C[i, j]` when `α = 0`; and otherwise `her2kCDiag` on the diagonal and
`her2kCAt` in the triangle, with the sums `colSum conj A B i j` and `colSum conj B A i j`, and
`C[i, j]` outside.
-/
public theorem getElem_her2kC (uplo : Float64.Uplo) (α : ComplexFloat) (A B : Mat k n)
    (β : Float) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (her2kC uplo α A B β C)[(i, j)] =
      if (isZero α || k == 0) && β == 1 then C[(i, j)]
      else if isZero α then herkInitAt uplo β i j C[(i, j)]
      else if i = j then her2kCDiag α β (colSum ComplexFloat.conj A B j j h.2 h.2)
        (colSum ComplexFloat.conj B A j j h.2 h.2) C[(i, j)]
      else if InTri uplo i j then her2kCAt α β (colSum ComplexFloat.conj A B i j h.1 h.2)
        (colSum ComplexFloat.conj B A i j h.1 h.2) C[(i, j)]
      else C[(i, j)] := by
  unfold her2kC
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => herkInitCol uplo β C j hj)
        (fun i j _ c => herkInitAt uplo β i j c) (fun _ _ _ _ _ _ => getElem_herkInitCol ..) C i j
        h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => setTriCol uplo
          (fun i hi c => her2kCAt α β (colSum ComplexFloat.conj A B i j hi hj)
            (colSum ComplexFloat.conj B A i j hi hj) c)
          (fun c => her2kCDiag α β (colSum ComplexFloat.conj A B j j hj hj)
            (colSum ComplexFloat.conj B A j j hj hj) c) C j hj)
        (fun i j hij c => if i = j then her2kCDiag α β (colSum ComplexFloat.conj A B j j hij.2
            hij.2) (colSum ComplexFloat.conj B A j j hij.2 hij.2) c
          else if InTri uplo i j then her2kCAt α β (colSum ComplexFloat.conj A B i j hij.1 hij.2)
            (colSum ComplexFloat.conj B A i j hij.1 hij.2) c
          else c) (fun _ _ _ _ _ _ => getElem_setTriCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]

end Mat

end BLAS.ComplexFloat64
