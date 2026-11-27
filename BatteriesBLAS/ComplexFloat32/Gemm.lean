/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Tri

/-!
# Complex matrix products

The products `gemm` (`C := α * A * B + β * C`) of complex matrices, with each of `A` and `B` as it
is (`N`), transposed (`T`) or conjugated and transposed (`C`), as `cgemm` in the reference BLAS
(`master`), with the same operations in the same order: `gemm` is `N` on both, and `gemmXY` is
`X` on `A` and `Y` on `B`, for instance `gemmCT` computes `α * Aᴴ * Bᵀ + β * C`.

When `A` is as it is, each column `j` of `C` is scaled by `β`, and then gets `mul α b` times
column `l` of `A` for each `l` in increasing order, where `b` is element `l` of column `j` of the
second factor. Otherwise each element `(i, j)` of `C` becomes `mul α t`, plus `mul β C[i, j]`
unless `β = 0`, where `t` is the sum from `0` of the products of the elements of column `i` of the
first factor with those of column `j` of the second. Each step updates `C` in place when its array
is not shared.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.ComplexFloat32

namespace Mat

variable {m n k : Nat}

/-! ## Rows -/

/-- Row `i` of `A` as a vector with the stride `A.ld`, with no copy. -/
@[expose] public def row (A : Mat m n) (i : Nat) (hi : i < m) : Vec n where
  data := A.data
  off := A.off + i
  inc := A.ld
  inc_pos := Or.inl (by have := A.le_ld; lia)
  bound := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · right
      have := A.col_le (by lia) (by lia : n - 1 < n)
      have e : 2 * A.ld * (n - 1) = 2 * (A.ld * (n - 1)) := Nat.mul_assoc ..
      lia

@[simp] public theorem getElem_row (A : Mat m n) (i : Nat) (hi : i < m) (j : Nat) (hj : j < n) :
    (A.row i hi)[j] = A[(i, j)] := by
  simp only [Vec.getElem_def, getElem_def, row, col]
  have e : 2 * A.ld * j = 2 * (A.ld * j) := Nat.mul_assoc ..
  congr 1 <;> congr 1 <;> lia

/-! ## Column steps -/

/--
`C` with column `j` scaled by `β` as `betaScal` does: unchanged when `β = 1`, zeros when `β = 0`,
and `mul β` of each element otherwise.
-/
public def betaCol (β : ComplexFloat32) (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  if isOne β then C
  else if isZero β then
    C.withColSlice j hj 0 m (by lia)
      (fun s => s.data.modifyStride2 s.reStride s.imStride m (fun _ _ => 0) (fun _ _ => 0)
        s.fits_re s.fits_im)
      (fun _ => by simp)
  else
    C.withColSlice j hj 0 m (by lia)
      (fun s => s.data.modifyStride2 s.reStride s.imStride m (fun u v => mulRe β ⟨u, v⟩)
        (fun u v => mulIm β ⟨u, v⟩) s.fits_re s.fits_im)
      (fun _ => by simp)

public theorem getElem_betaCol (β : ComplexFloat32) (C : Mat m n) (j : Nat) (hj : j < n)
    (i j' : Nat) (h : i < m ∧ j' < n) :
    (betaCol β C j hj)[(i, j')] = if j' = j then betaMul β C[(i, j')] else C[(i, j')] := by
  unfold betaCol betaMul
  by_cases h1 : isOne β
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : isZero β
    · simp only [h0, ↓reduceIte]
      rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (modifyStride2_eq ..)]
      by_cases e : j' = j
      · simp [e, h.1]; rfl
      · simp [e]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (modifyStride2_eq ..)]
      by_cases e : j' = j
      · simp [e, h.1, mulRe_eq, mulIm_eq]
      · simp [e]

/-- `C` with `mul t x[i]` added to each element `i` of column `j`, as `axpyN t x`. -/
public def axpyCol (t : ComplexFloat32) (x : Vec m) (C : Mat m n) (j : Nat) (hj : j < n) :
    Mat m n :=
  C.withColSlice j hj 0 m (by lia) (fun s => Vec.axpyData t x s)
    (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])

public theorem getElem_axpyCol (t : ComplexFloat32) (x : Vec m) (C : Mat m n) (j : Nat)
    (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (axpyCol t x C j hj)[(i, j')] = if j' = j then C[(i, j')] + mul t x[i] else C[(i, j')] := by
  unfold axpyCol
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.axpyData_eq ..)]
  by_cases e : j' = j
  · simp only [e, Nat.zero_le, Nat.zero_add, h.1, and_self, ↓reduceIte, Nat.sub_zero, Vec.get0,
      ↓reduceDIte]
    rfl
  · simp [e]

/-- `C` with element `(i, j)` set to `z`. -/
public def setAt (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) (z : ComplexFloat32) : Mat m n :=
  C.withColSlice j h.2 i 1 (by lia)
    (fun s => s.data.modifyStride2 s.reStride s.imStride 1 (fun _ _ => z.re) (fun _ _ => z.im)
      s.fits_re s.fits_im)
    (fun _ => by simp)

public theorem getElem_setAt (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) (z : ComplexFloat32)
    (i' j' : Nat) (h' : i' < m ∧ j' < n) :
    (setAt C i j h z)[(i', j')] = if i' = i ∧ j' = j then z else C[(i', j')] := by
  unfold setAt
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (modifyStride2_eq ..)]
  by_cases e : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := e
    simp
  · have : ¬(j' = j ∧ i ≤ i' ∧ i' < i + 1) := fun ⟨h1, h2, h3⟩ => e ⟨by lia, h1⟩
    simp only [this, ↓reduceIte, e]

/-! ## The two kernels -/

/--
Column `j` of `gemmN`: scaled by `β`, and then with `mul (mul α (b l j)) A[i, l]` added to each
element `i`, for each `l` in increasing order.
-/
public def gemmNCol (α : ComplexFloat32) (A : Mat m k)
    (b : (l : Nat) → l < k → (j : Nat) → j < n → ComplexFloat32) (β : ComplexFloat32) (C : Mat m n)
    (j : Nat) (hj : j < n) : Mat m n :=
  Nat.fold k (fun l hl C => axpyCol (mul α (b l hl j hj)) (A.col l hl) C j hj) (betaCol β C j hj)

private theorem getElem_fold_axpyCol (α : ComplexFloat32) (A : Mat m k)
    (b : (l : Nat) → l < k → (j : Nat) → j < n → ComplexFloat32) (C : Mat m n) (j : Nat)
    (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    ∀ k' (hk : k' ≤ k),
      (Nat.fold k' (fun l hl C => axpyCol (mul α (b l (by lia) j hj)) (A.col l (by lia)) C j hj)
        C)[(i, j')] =
        if j' = j then
          Nat.fold k' (fun l hl s => s + mul (mul α (b l (by lia) j hj)) (A[(i, l)]'⟨h.1, by lia⟩))
            C[(i, j')]
        else C[(i, j')]
  | 0, _ => by simp
  | k' + 1, hk => by
    rw [Nat.fold_succ, getElem_axpyCol, getElem_fold_axpyCol α A b C j hj i j' h k' (by lia)]
    by_cases e : j' = j
    · simp [e, Nat.fold_succ]
    · simp [e]

public theorem getElem_gemmNCol (α : ComplexFloat32) (A : Mat m k)
    (b : (l : Nat) → l < k → (j : Nat) → j < n → ComplexFloat32) (β : ComplexFloat32) (C : Mat m n)
    (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (gemmNCol α A b β C j hj)[(i, j')] =
      if j' = j then
        Nat.fold k (fun l hl s => s + mul (mul α (b l hl j hj)) (A[(i, l)]'⟨h.1, hl⟩))
          (betaMul β C[(i, j')])
      else C[(i, j')] := by
  unfold gemmNCol
  rw [getElem_fold_axpyCol α A b _ j hj i j' h k (Nat.le_refl _), getElem_betaCol]
  by_cases e : j' = j <;> simp [e]

/--
The product with `A` as it is: `C := α * A * B' + β * C`, where element `(l, j)` of `B'` is
`b l j`, with the operations of `cgemm` with `TRANSA = 'N'`: it scales each column of `C` by `β`
when `α = 0`, and otherwise runs `gemmNCol` for each column in increasing order.
-/
@[expose] public def gemmN (α : ComplexFloat32) (A : Mat m k)
    (b : (l : Nat) → l < k → (j : Nat) → j < n → ComplexFloat32) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  if isZero α then
    if isOne β then C else Nat.fold n (fun j hj C => betaCol β C j hj) C
  else Nat.fold n (fun j hj C => gemmNCol α A b β C j hj) C

/-- A fold of steps that each change one column, the column of the step, from the original. -/
private theorem getElem_fold_col (g : (j : Nat) → j < n → Mat m n → Mat m n)
    (φ : (i j : Nat) → i < m ∧ j < n → ComplexFloat32 → ComplexFloat32)
    (hg : ∀ j hj (B : Mat m n) i j' (hij : i < m ∧ j' < n),
      (g j hj B)[(i, j')] = if j' = j then φ i j ⟨hij.1, hj⟩ B[(i, j')] else B[(i, j')])
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    ∀ k' (hk : k' ≤ n), (Nat.fold k' (fun j hj B => g j (by lia) B) C)[(i, j)] =
      if j < k' then φ i j h C[(i, j)] else C[(i, j)]
  | 0, _ => by simp
  | k' + 1, hk => by
    rw [Nat.fold_succ, hg, getElem_fold_col g φ hg C i j h k' (by lia)]
    by_cases e : j = k'
    · subst e; simp
    · have : (j < k' + 1) = (j < k') := by apply propext; lia
      simp only [e, this, ↓reduceIte]

public theorem getElem_gemmN (α : ComplexFloat32) (A : Mat m k)
    (b : (l : Nat) → l < k → (j : Nat) → j < n → ComplexFloat32) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmN α A b β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold k (fun l hl s => s + mul (mul α (b l hl j h.2)) (A[(i, l)]'⟨h.1, hl⟩))
        (betaMul β C[(i, j)]) := by
  unfold gemmN
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    by_cases hb : isOne β
    · simp [hb, betaMul]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [getElem_fold_col (fun j hj C => betaCol β C j hj) (fun i j _ c => betaMul β c)
        (fun _ _ _ _ _ _ => getElem_betaCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => gemmNCol α A b β C j hj)
      (fun i j hij c => Nat.fold k (fun l hl s =>
        s + mul (mul α (b l hl j hij.2)) (A[(i, l)]'⟨hij.1, hl⟩)) (betaMul β c))
      (fun _ _ _ _ _ _ => getElem_gemmNCol ..) C i j h n (Nat.le_refl _)]
    simp [h.2]

/--
The value of `gemmT` at an element `c` of `C`: `mul α t`, plus `mul β c` unless `β = 0`, where
`t` is `t = 0 + mul (p x[0]) (q y[0]) + … + mul (p x[k - 1]) (q y[k - 1])`, from the left.
-/
@[inline, expose] public def gemmTAt (p q : ComplexFloat32 → ComplexFloat32) (α : ComplexFloat32)
    (x y : Vec k) (β : ComplexFloat32) (c : ComplexFloat32) : ComplexFloat32 :=
  let t := Vec.accWith p q (· + ·) zero x y
  if isZero β then mul α t else mul α t + mul β c

/-- Column `j` of `gemmT`: `gemmTAt` at each element, in increasing order of the rows. -/
@[specialize] public def gemmTCol (p q : ComplexFloat32 → ComplexFloat32) (α : ComplexFloat32)
    (A : Mat k m) (y : Vec k) (β : ComplexFloat32) (C : Mat m n) (j : Nat) (hj : j < n) :
    Mat m n :=
  Nat.fold m (fun i hi C => C.setAt i j ⟨hi, hj⟩
    (gemmTAt p q α (A.col i hi) y β (C[(i, j)]'⟨hi, hj⟩))) C

private theorem getElem_fold_setAt (p q : ComplexFloat32 → ComplexFloat32) (α : ComplexFloat32)
    (A : Mat k m) (y : Vec k) (β : ComplexFloat32) (C : Mat m n) (j : Nat) (hj : j < n)
    (i j' : Nat) (h : i < m ∧ j' < n) :
    ∀ m' (hm : m' ≤ m),
      (Nat.fold m' (fun i hi C => C.setAt i j ⟨by lia, hj⟩
        (gemmTAt p q α (A.col i (by lia)) y β (C[(i, j)]'⟨by lia, hj⟩))) C)[(i, j')] =
        if j' = j ∧ i < m' then gemmTAt p q α (A.col i h.1) y β C[(i, j')] else C[(i, j')]
  | 0, _ => by simp
  | m' + 1, hm => by
    rw [Nat.fold_succ, getElem_setAt]
    by_cases e : i = m' ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := e
      simp only [and_self, ↓reduceIte, Nat.lt_add_one]
      rw [getElem_fold_setAt p q α A y β C j' hj i j' h i (by lia)]
      simp
    · rw [getElem_fold_setAt p q α A y β C j hj i j' h m' (by lia)]
      simp only [e, ↓reduceIte]
      have : (j' = j ∧ i < m' + 1) = (j' = j ∧ i < m') := by
        apply propext; constructor
        · intro ⟨h1, h2⟩; exact ⟨h1, by
            by_cases e' : i = m'
            · exact absurd ⟨e', h1⟩ e
            · lia⟩
        · intro ⟨h1, h2⟩; exact ⟨h1, by lia⟩
      simp only [this]

public theorem getElem_gemmTCol (p q : ComplexFloat32 → ComplexFloat32) (α : ComplexFloat32)
    (A : Mat k m) (y : Vec k) (β : ComplexFloat32) (C : Mat m n) (j : Nat) (hj : j < n)
    (i j' : Nat) (h : i < m ∧ j' < n) :
    (gemmTCol p q α A y β C j hj)[(i, j')] =
      if j' = j then gemmTAt p q α (A.col i h.1) y β C[(i, j')] else C[(i, j')] := by
  unfold gemmTCol
  rw [getElem_fold_setAt p q α A y β C j hj i j' h m (Nat.le_refl _)]
  simp [h.1]

/--
The product with `A` transposed: `C := α * A' * B' + β * C`, where row `i` of `A'` is `p` of
column `i` of `A`, and column `j` of `B'` is `q` of `y j`, with the operations of `cgemm` with
`TRANSA = 'T'` or `'C'`: it returns `C` when `α = 0` or `k = 0`, and `β = 1`; it scales `C` by
`β` when `α = 0`; and otherwise runs `gemmTCol` for each column in increasing order.
-/
@[inline, expose] public def gemmT (p q : ComplexFloat32 → ComplexFloat32) (α : ComplexFloat32)
    (A : Mat k m) (y : (j : Nat) → j < n → Vec k) (β : ComplexFloat32) (C : Mat m n) : Mat m n :=
  if (isZero α || k == 0) && isOne β then C
  else if isZero α then Nat.fold n (fun j hj C => betaCol β C j hj) C
  else Nat.fold n (fun j hj C => gemmTCol p q α A (y j hj) β C j hj) C

/--
The sum `0 + mul (p A[0, i]) (q (y j)[0]) + … + mul (p A[k - 1, i]) (q (y j)[k - 1])` of
`gemmT`, from the left.
-/
@[expose] public def gemmTSum (p q : ComplexFloat32 → ComplexFloat32) (A : Mat k m)
    (y : (j : Nat) → j < n → Vec k) (i j : Nat) (h : i < m ∧ j < n) : ComplexFloat32 :=
  Nat.fold k (fun l hl s => s + mul (p (A[(l, i)]'⟨hl, h.1⟩)) (q (y j h.2)[l])) zero

public theorem getElem_gemmT (p q : ComplexFloat32 → ComplexFloat32) (α : ComplexFloat32)
    (A : Mat k m) (y : (j : Nat) → j < n → Vec k) (β : ComplexFloat32) (C : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (gemmT p q α A y β C)[(i, j)] =
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α (gemmTSum p q A y i j h)
      else mul α (gemmTSum p q A y i j h) + mul β C[(i, j)] := by
  unfold gemmT
  split
  · rfl
  · split
    · rw [getElem_fold_col (fun j hj C => betaCol β C j hj) (fun i j _ c => betaMul β c)
        (fun _ _ _ _ _ _ => getElem_betaCol ..) C i j h n (Nat.le_refl _)]
      simp [h.2]
    · rw [getElem_fold_col (fun j hj C => gemmTCol p q α A (y j hj) β C j hj)
        (fun i j hij c => gemmTAt p q α (A.col i hij.1) (y j hij.2) β c)
        (fun _ _ _ _ _ _ => getElem_gemmTCol ..) C i j h n (Nat.le_refl _)]
      simp only [h.2, ↓reduceIte, gemmTAt, Vec.accWith_eq, Vec.opC_add, getElem_col, gemmTSum]

/-! ## `gemm` and its variants -/

/--
`gemm α A B β C` is `α * A * B + β * C`, as `cgemm` with `TRANSA = 'N'` and `TRANSB = 'N'`.
-/
@[expose] public def gemm (α : ComplexFloat32) (A : Mat m k) (B : Mat k n) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmN α A (fun l hl j hj => B[(l, j)]) β C

/--
Element `(i, j)` of `gemm α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise
`betaMul β C[i, j] + mul (mul α b₀) A[i, 0] + … + mul (mul α bₖ₋₁) A[i, k - 1]`, from the
left, where `bₗ = B[l, j]`.
-/
public theorem getElem_gemm (α : ComplexFloat32) (A : Mat m k) (B : Mat k n) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemm α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold k (fun l hl s => s + mul (mul α B[(l, j)]) A[(i, l)])
        (betaMul β C[(i, j)]) :=
  getElem_gemmN ..

/--
`gemmNT α A B β C` is `α * A * Bᵀ + β * C`, as `cgemm` with `TRANSA = 'N'` and `TRANSB = 'T'`.
-/
@[expose] public def gemmNT (α : ComplexFloat32) (A : Mat m k) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmN α A (fun l hl j hj => B[(j, l)]) β C

/--
Element `(i, j)` of `gemmNT α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise
`betaMul β C[i, j] + mul (mul α b₀) A[i, 0] + … + mul (mul α bₖ₋₁) A[i, k - 1]`, from the
left, where `bₗ = B[j, l]`.
-/
public theorem getElem_gemmNT (α : ComplexFloat32) (A : Mat m k) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmNT α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold k (fun l hl s => s + mul (mul α B[(j, l)]) A[(i, l)])
        (betaMul β C[(i, j)]) :=
  getElem_gemmN ..

/--
`gemmNC α A B β C` is `α * A * Bᴴ + β * C`, as `cgemm` with `TRANSA = 'N'` and `TRANSB = 'C'`.
-/
@[expose] public def gemmNC (α : ComplexFloat32) (A : Mat m k) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmN α A (fun l hl j hj => B[(j, l)].conj) β C

/--
Element `(i, j)` of `gemmNC α A B β C`: `betaMul β C[i, j]` when `α = 0`, and otherwise
`betaMul β C[i, j] + mul (mul α b₀) A[i, 0] + … + mul (mul α bₖ₋₁) A[i, k - 1]`, from the
left, where `bₗ = conj B[j, l]`.
-/
public theorem getElem_gemmNC (α : ComplexFloat32) (A : Mat m k) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmNC α A B β C)[(i, j)] =
      if isZero α then betaMul β C[(i, j)]
      else Nat.fold k (fun l hl s => s + mul (mul α B[(j, l)].conj) A[(i, l)])
        (betaMul β C[(i, j)]) :=
  getElem_gemmN ..

/--
`gemmTN α A B β C` is `α * Aᵀ * B + β * C`, as `cgemm` with `TRANSA = 'T'` and `TRANSB = 'N'`.
-/
@[expose] public def gemmTN (α : ComplexFloat32) (A : Mat k m) (B : Mat k n) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmT id id α A (fun j hj => B.col j hj) β C

/--
Element `(i, j)` of `gemmTN α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`betaMul β C[i, j]` when `α = 0`; and otherwise `mul α t`, plus `mul β C[i, j]` unless `β = 0`,
where `t = 0 + mul A[l, i] B[l, j] + …`, over `l = 0, …, k - 1`, from the left.
-/
public theorem getElem_gemmTN (α : ComplexFloat32) (A : Mat k m) (B : Mat k n) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmTN α A B β C)[(i, j)] =
      let t := Nat.fold k (fun l hl s => s + mul A[(l, i)] B[(l, j)]) zero
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α t else mul α t + mul β C[(i, j)] := by
  simp [gemmTN, getElem_gemmT, gemmTSum]

/--
`gemmTT α A B β C` is `α * Aᵀ * Bᵀ + β * C`, as `cgemm` with `TRANSA = 'T'` and `TRANSB = 'T'`.
-/
@[expose] public def gemmTT (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmT id id α A (fun j hj => B.row j hj) β C

/--
Element `(i, j)` of `gemmTT α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`betaMul β C[i, j]` when `α = 0`; and otherwise `mul α t`, plus `mul β C[i, j]` unless `β = 0`,
where `t = 0 + mul A[l, i] B[j, l] + …`, over `l = 0, …, k - 1`, from the left.
-/
public theorem getElem_gemmTT (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmTT α A B β C)[(i, j)] =
      let t := Nat.fold k (fun l hl s => s + mul A[(l, i)] B[(j, l)]) zero
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α t else mul α t + mul β C[(i, j)] := by
  simp [gemmTT, getElem_gemmT, gemmTSum]

/--
`gemmTC α A B β C` is `α * Aᵀ * Bᴴ + β * C`, as `cgemm` with `TRANSA = 'T'` and `TRANSB = 'C'`.
-/
@[expose] public def gemmTC (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmT id ComplexFloat32.conj α A (fun j hj => B.row j hj) β C

/--
Element `(i, j)` of `gemmTC α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`betaMul β C[i, j]` when `α = 0`; and otherwise `mul α t`, plus `mul β C[i, j]` unless `β = 0`,
where `t = 0 + mul A[l, i] (conj B[j, l]) + …`, over `l = 0, …, k - 1`, from the left.
-/
public theorem getElem_gemmTC (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmTC α A B β C)[(i, j)] =
      let t := Nat.fold k (fun l hl s => s + mul A[(l, i)] B[(j, l)].conj) zero
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α t else mul α t + mul β C[(i, j)] := by
  simp [gemmTC, getElem_gemmT, gemmTSum]

/--
`gemmCN α A B β C` is `α * Aᴴ * B + β * C`, as `cgemm` with `TRANSA = 'C'` and `TRANSB = 'N'`.
-/
@[expose] public def gemmCN (α : ComplexFloat32) (A : Mat k m) (B : Mat k n) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmT ComplexFloat32.conj id α A (fun j hj => B.col j hj) β C

/--
Element `(i, j)` of `gemmCN α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`betaMul β C[i, j]` when `α = 0`; and otherwise `mul α t`, plus `mul β C[i, j]` unless `β = 0`,
where `t = 0 + mul (conj A[l, i]) B[l, j] + …`, over `l = 0, …, k - 1`, from the left.
-/
public theorem getElem_gemmCN (α : ComplexFloat32) (A : Mat k m) (B : Mat k n) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmCN α A B β C)[(i, j)] =
      let t := Nat.fold k (fun l hl s => s + mul A[(l, i)].conj B[(l, j)]) zero
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α t else mul α t + mul β C[(i, j)] := by
  simp [gemmCN, getElem_gemmT, gemmTSum]

/--
`gemmCT α A B β C` is `α * Aᴴ * Bᵀ + β * C`, as `cgemm` with `TRANSA = 'C'` and `TRANSB = 'T'`.
-/
@[expose] public def gemmCT (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  gemmT ComplexFloat32.conj id α A (fun j hj => B.row j hj) β C

/--
Element `(i, j)` of `gemmCT α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`betaMul β C[i, j]` when `α = 0`; and otherwise `mul α t`, plus `mul β C[i, j]` unless `β = 0`,
where `t = 0 + mul (conj A[l, i]) B[j, l] + …`, over `l = 0, …, k - 1`, from the left.
-/
public theorem getElem_gemmCT (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmCT α A B β C)[(i, j)] =
      let t := Nat.fold k (fun l hl s => s + mul A[(l, i)].conj B[(j, l)]) zero
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α t else mul α t + mul β C[(i, j)] := by
  simp [gemmCT, getElem_gemmT, gemmTSum]

/--
`gemmCC α A B β C` is `α * Aᴴ * Bᴴ + β * C`, as `cgemm` with `TRANSA = 'C'` and `TRANSB = 'C'`.
-/
@[expose] public def gemmCC (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) : Mat m n :=
  -- The second `conj` is written out: with `ComplexFloat32.conj` for both, the compiler makes one
  -- closure of the two and calls it on each element, 4× slower.
  gemmT ComplexFloat32.conj (fun z => ⟨z.re, -z.im⟩) α A (fun j hj => B.row j hj) β C

/--
Element `(i, j)` of `gemmCC α A B β C`: `C[i, j]` when `α = 0` or `k = 0`, and `β = 1`;
`betaMul β C[i, j]` when `α = 0`; and otherwise `mul α t`, plus `mul β C[i, j]` unless `β = 0`,
where `t = 0 + mul (conj A[l, i]) (conj B[j, l]) + …`, over `l = 0, …, k - 1`, from the left.
-/
public theorem getElem_gemmCC (α : ComplexFloat32) (A : Mat k m) (B : Mat n k) (β : ComplexFloat32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmCC α A B β C)[(i, j)] =
      let t := Nat.fold k (fun l hl s => s + mul A[(l, i)].conj B[(j, l)].conj) zero
      if (isZero α || k == 0) && isOne β then C[(i, j)]
      else if isZero α then betaMul β C[(i, j)]
      else if isZero β then mul α t else mul α t + mul β C[(i, j)] := by
  simp [gemmCC, getElem_gemmT, gemmTSum, ComplexFloat32.conj]

end Mat

end BLAS.ComplexFloat32
