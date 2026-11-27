/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Level2
public import BatteriesBLAS.Float32.Trsv

/-!
# Hermitian Level 2

The Hermitian routines on complex matrices: the product `hemv` (`y := α * A * x + β * y`) and the
rank-one and rank-two updates `her` (`A := α * x * xᴴ + A`, with a real `α`) and `her2`
(`A := α * x * yᴴ + conj α * y * xᴴ + A`), on the upper or the lower triangle of `A`, as `chemv`,
`cher` and `cher2` in the reference BLAS (`master`), with the same operations in the same order.

They work on parts of vectors and of columns: `Vec.slice` is a part of a vector, with no copy,
and `Vec.withSlice` and `Mat.withColSlice` run an update on a part of a vector or of a column of a
matrix, in place when the array is not shared, leaving the rest unchanged.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.ComplexFloat32

namespace Vec

variable {n : Nat}

/-- An element at an index equal to another is the same element. -/
public theorem getElem_eq_of_eq (x : Vec n) {i j : Nat} (e : i = j) (hi : i < n) :
    x[i] = x[j]'(e ▸ hi) := by
  subst e; rfl

/-- The `len` elements of `x` from element `k`, as a vector, with no copy. -/
@[expose] public def slice (x : Vec n) (k len : Nat) (h : k + len ≤ n) : Vec len where
  data := x.data
  off := x.off + x.inc * k
  inc := x.inc
  inc_pos := by
    rcases x.inc_pos with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by lia)
  bound := by
    rcases Nat.eq_zero_or_pos len with hl | hl
    · exact Or.inl hl
    · right
      rcases x.bound with hb | hb
      · lia
      · have h1 : x.inc * (k + (len - 1)) ≤ x.inc * (n - 1) := Nat.mul_le_mul_left _ (by lia)
        rw [Nat.mul_add] at h1
        have e1 : 2 * x.inc * (len - 1) = 2 * (x.inc * (len - 1)) := Nat.mul_assoc ..
        have e2 : 2 * x.inc * (n - 1) = 2 * (x.inc * (n - 1)) := Nat.mul_assoc ..
        lia

@[simp] public theorem data_slice (x : Vec n) (k len : Nat) (h : k + len ≤ n) :
    (x.slice k len h).data = x.data := rfl

@[simp] public theorem off_slice (x : Vec n) (k len : Nat) (h : k + len ≤ n) :
    (x.slice k len h).off = x.off + x.inc * k := rfl

@[simp] public theorem inc_slice (x : Vec n) (k len : Nat) (h : k + len ≤ n) :
    (x.slice k len h).inc = x.inc := rfl

@[simp] public theorem getElem_slice (x : Vec n) (k len : Nat) (h : k + len ≤ n) (i : Nat)
    (hi : i < len) : (x.slice k len h)[i] = x[k + i] := by
  simp only [getElem_def, slice]
  have e : 2 * (x.off + x.inc * k) + 2 * x.inc * i = 2 * x.off + 2 * x.inc * (k + i) := by
    simp only [Nat.mul_assoc, Nat.mul_add]; lia
  congr 1 <;> simp only [e, Nat.add_right_comm _ 1]

/--
`x` with its array replaced by `f` of the slice of `len` elements from element `k`, an update of
that slice that leaves the other entries of the array unchanged. The slice holds the array of `x`
alone, so that `f` can update it in place.
-/
@[inline] public def withSlice (x : Vec n) (k len : Nat) (h : k + len ≤ n)
    (f : Vec len → Float32Array) (hf : ∀ s, (f s).size = s.data.size) : Vec n :=
  match x with
  | ⟨d, off, inc, hp, hb⟩ =>
    ⟨f (slice ⟨d, off, inc, hp, hb⟩ k len h), off, inc, hp, by rw [hf]; exact hb⟩

/--
The elements of `withSlice`, when `f` maps the parts of the elements of the slice by `F` and
`G`: element `i` of the slice is `⟨F (i - k) x[i].re x[i].im, G (i - k) x[i].re x[i].im⟩`, and the
others are unchanged.
-/
public theorem getElem_withSlice (x : Vec n) (k len : Nat) (h : k + len ≤ n)
    (f : Vec len → Float32Array) (hf : ∀ s, (f s).size = s.data.size)
    (F G : Nat → Float32 → Float32 → Float32)
    (hd : f (x.slice k len h) = (x.slice k len h).data.modifyAt2 (x.slice k len h).reStride.idx
      (x.slice k len h).imStride.idx 0 len F G) (i : Nat) (hi : i < n) :
    (x.withSlice k len h f hf)[i] =
      if k ≤ i ∧ i < k + len then ⟨F (i - k) x[i].re x[i].im, G (i - k) x[i].re x[i].im⟩
      else x[i] := by
  obtain ⟨d, off, inc, hp, hb⟩ := x
  split
  · rename_i hr
    have hik : i - k < len := by lia
    have e1 := ((withSlice ⟨d, off, inc, hp, hb⟩ k len h f hf).getElem_slice k len h (i - k)
      hik).trans (getElem_eq_of_eq _ (by lia : k + (i - k) = i) _)
    rw [← e1]
    refine (getElem_of_data_eq_modifyAt2 (v := (withSlice ⟨d, off, inc, hp, hb⟩ k len h f hf).slice
      k len h) (w := slice ⟨d, off, inc, hp, hb⟩ k len h) F G hd rfl rfl (i - k) hik).trans ?_
    rw [getElem_slice, getElem_eq_of_eq _ (by lia : k + (i - k) = i)]
  · rename_i hr
    have key : ∀ k', k' < len → inc * k + inc * k' ≠ inc * i := by
      intro k' hk' e
      rcases hp with hp | hp
      · have : k + k' = i := Nat.eq_of_mul_eq_mul_left hp (by rw [Nat.mul_add]; exact e)
        exact hr ⟨by lia, by lia⟩
      · exact hr ⟨by lia, by lia⟩
    simp only [getElem_def, withSlice, hd]
    congr 1
    · refine getElem_data_modifyAt2_of_ne _ F G (fun k' hk' => ?_) _
      have := key k' hk'
      simp only [idx_reStride, idx_imStride, off_slice, inc_slice, Nat.mul_assoc]
      constructor <;> lia
    · refine getElem_data_modifyAt2_of_ne _ F G (fun k' hk' => ?_) _
      have := key k' hk'
      simp only [idx_reStride, idx_imStride, off_slice, inc_slice, Nat.mul_assoc]
      constructor <;> lia

/-- `x` with element `i` set to `z`, in place when the array of `x` is not shared. -/
@[inline] public def set (x : Vec n) (i : Nat) (hi : i < n) (z : ComplexFloat32) : Vec n :=
  x.withSlice i 1 (by lia)
    (fun s => s.data.modifyStride2 s.reStride s.imStride 1 (fun _ _ => z.re) (fun _ _ => z.im)
      s.fits_re s.fits_im)
    (fun _ => by simp)

@[simp] public theorem getElem_set (x : Vec n) (i : Nat) (hi : i < n) (z : ComplexFloat32) (j : Nat)
    (hj : j < n) : (x.set i hi z)[j] = if j = i then z else x[j] := by
  unfold set
  rw [getElem_withSlice x i 1 _ _ _ (fun _ _ _ => z.re) (fun _ _ _ => z.im) (modifyStride2_eq ..)]
  by_cases e : j = i
  · simp only [e, Nat.le_refl, Nat.lt_add_one, and_self, ↓reduceIte]
  · simp only [e, ↓reduceIte, ite_eq_right_iff, and_imp]
    intro h1 h2; lia

/--
`Nat.fold` of updates of a vector that each map element `i` by `φ j i`, from its old value, gives
element `i` as the fold of the `φ j i` over the steps `j`.
-/
public theorem getElem_fold_of_pointwise {m : Nat} (g : (j : Nat) → j < m → Vec n → Vec n)
    (φ : (j : Nat) → j < m → (i : Nat) → i < n → ComplexFloat32 → ComplexFloat32)
    (hg : ∀ j hj (y : Vec n) i hi, (g j hj y)[i] = φ j hj i hi y[i]) (y : Vec n) (i : Nat)
    (hi : i < n) :
    ∀ k (hk : k ≤ m), (Nat.fold k (fun j hj y => g j (by lia) y) y)[i] =
      Nat.fold k (fun j hj s => φ j (by lia) i hi s) y[i]
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Nat.fold_succ, Nat.fold_succ, hg, getElem_fold_of_pointwise g φ hg y i hi k (by lia)]

end Vec

namespace Mat

variable {m n : Nat}

/-- The column `j` of `A`, with its slice of `len` rows from row `k` replaced by `f` of it. -/
@[inline] public def withColSlice (A : Mat m n) (j : Nat) (hj : j < n) (k len : Nat)
    (h : k + len ≤ m) (f : Vec len → Float32Array) (hf : ∀ s, (f s).size = s.data.size) :
    Mat m n :=
  match A with
  | ⟨d, off, ld, hle, hb⟩ =>
    ⟨f ((Mat.col ⟨d, off, ld, hle, hb⟩ j hj).slice k len h), off, ld, hle, by rw [hf]; exact hb⟩

/-- Two elements of different columns are at different indices. -/
private theorem index_ne' (A : Mat m n) {i k j j' : Nat} (hj : j ≠ j') (hi : i < m)
    (hk : k < m) : A.off + A.ld * j + i ≠ A.off + A.ld * j' + k := by
  intro e
  have hl := A.le_ld
  have e' : A.ld * j + i = A.ld * j' + k := by lia
  have h1 : (A.ld * j + i) / A.ld = j := by
    rw [Nat.mul_add_div (by lia), Nat.div_eq_of_lt (by lia), Nat.add_zero]
  have h2 : (A.ld * j' + k) / A.ld = j' := by
    rw [Nat.mul_add_div (by lia), Nat.div_eq_of_lt (by lia), Nat.add_zero]
  exact hj (by rw [← h1, ← h2, e'])

/--
The elements of `withColSlice`, when `f` maps the parts of the elements of the slice by `F` and
`G`: element `(i, j)` of the slice is `⟨F (i - k) A[i, j].re A[i, j].im, G (i - k) …⟩`, and the
others are unchanged.
-/
public theorem getElem_withColSlice (A : Mat m n) (j : Nat) (hj : j < n) (k len : Nat)
    (h : k + len ≤ m) (f : Vec len → Float32Array) (hf : ∀ s, (f s).size = s.data.size)
    (F G : Nat → Float32 → Float32 → Float32)
    (hd : f ((A.col j hj).slice k len h) = ((A.col j hj).slice k len h).data.modifyAt2
      ((A.col j hj).slice k len h).reStride.idx ((A.col j hj).slice k len h).imStride.idx 0 len
      F G) (i j' : Nat) (hij : i < m ∧ j' < n) :
    (A.withColSlice j hj k len h f hf)[(i, j')] =
      if j' = j ∧ k ≤ i ∧ i < k + len then
        ⟨F (i - k) (A[(i, j')]'hij).re (A[(i, j')]'hij).im,
          G (i - k) (A[(i, j')]'hij).re (A[(i, j')]'hij).im⟩
      else A[(i, j')] := by
  obtain ⟨d, off, ld, hle, hb⟩ := A
  by_cases e : j' = j
  · subst e
    have := Vec.getElem_withSlice (Mat.col ⟨d, off, ld, hle, hb⟩ j' hj) k len h f hf F G hd i
      hij.1
    simp only [true_and]
    exact this
  · simp only [e, false_and, ↓reduceIte]
    have hne : ∀ k', k' < len → off + ld * j + (k + k') ≠ off + ld * j' + i := fun k' hk' =>
      index_ne' ⟨d, off, ld, hle, hb⟩ (Ne.symm e) (by lia) hij.1
    simp only [getElem_def, Vec.getElem_def, data_col, off_col, inc_col, withColSlice]
    simp only [hd]
    congr 1
    · refine Vec.getElem_data_modifyAt2_of_ne (Mat.col ⟨d, off, ld, hle, hb⟩ j hj |>.slice k len h)
        F G (fun k' hk' => ?_) _
      have := hne k' hk'
      simp only [Vec.idx_reStride, Vec.idx_imStride, Vec.off_slice, Vec.inc_slice, off_col,
        inc_col]
      constructor <;> lia
    · refine Vec.getElem_data_modifyAt2_of_ne (Mat.col ⟨d, off, ld, hle, hb⟩ j hj |>.slice k len h)
        F G (fun k' hk' => ?_) _
      have := hne k' hk'
      simp only [Vec.idx_reStride, Vec.idx_imStride, Vec.off_slice, Vec.inc_slice, off_col,
        inc_col]
      constructor <;> lia

/--
`Nat.fold` of updates of a matrix that each map element `(i, j')` by `φ j i j'`, from its old
value, gives element `(i, j')` as the fold of the `φ j i j'` over the steps `j`.
-/
public theorem getElem_fold_of_pointwise {K : Nat} (g : (j : Nat) → j < K → Mat m n → Mat m n)
    (φ : (j : Nat) → j < K → (i j' : Nat) → i < m ∧ j' < n → ComplexFloat32 → ComplexFloat32)
    (hg : ∀ j hj (B : Mat m n) i j' hij, (g j hj B)[(i, j')] = φ j hj i j' hij B[(i, j')])
    (A : Mat m n) (i j' : Nat) (hij : i < m ∧ j' < n) :
    ∀ k (hk : k ≤ K), (Nat.fold k (fun j hj B => g j (by lia) B) A)[(i, j')] =
      Nat.fold k (fun j hj s => φ j (by lia) i j' hij s) A[(i, j')]
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Nat.fold_succ, Nat.fold_succ, hg, getElem_fold_of_pointwise g φ hg A i j' hij k (by lia)]

/-- A fold whose only step that changes its value is the step `j`. -/
private theorem fold_ite_eq {α : Type} {K : Nat} (j : Nat) (ψ : (l : Nat) → l < K → α → α)
    (s : α) : ∀ k (hk : k ≤ K), Nat.fold k (fun l hl t => if l = j then ψ l (by lia) t else t) s =
      if h : j < k then ψ j (by lia) s else s
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Nat.fold_succ, fold_ite_eq j ψ s k (by lia)]
    by_cases e : k = j
    · subst e; simp
    · have : (j < k + 1) = (j < k) := by apply propext; lia
      simp only [e, this, ↓reduceIte]

/-- Whether row `i` is in the triangle of column `j` other than the diagonal. -/
@[expose] public def InTri (uplo : Float32.Uplo) (i j : Nat) : Prop :=
  (uplo = .upper ∧ i < j) ∨ (uplo = .lower ∧ j < i)

public instance (uplo : Float32.Uplo) (i j : Nat) : Decidable (InTri uplo i j) := by
  unfold InTri; infer_instance

/-! ## `hemv` -/

/-- The `dotc` of the part of column `j` in the triangle, without the diagonal, with `x`. -/
@[expose] public def hemvDot (uplo : Float32.Uplo) (A : Mat n n) (x : Vec n) (j : Nat)
    (hj : j < n) :
    ComplexFloat32 :=
  if uplo = .upper then Vec.dotc ((A.col j hj).slice 0 j (by lia)) (x.slice 0 j (by lia))
  else Vec.dotc ((A.col j hj).slice (j + 1) (n - (j + 1)) (by lia))
    (x.slice (j + 1) (n - (j + 1)) (by lia))

/--
The step `j` of `hemv` at element `i` of `y`, from its value `s`: with `t₁ = mul α x[j]`, it adds
`mul t₁ A[i, j]` when `i` is in the triangle of column `j`, and on the diagonal it gives
`s + mulr t₁ A[j, j].re + mul α (hemvDot uplo A x j)`, as `chemv`.
-/
@[expose] public def hemvStep (uplo : Float32.Uplo) (α : ComplexFloat32) (A : Mat n n) (x : Vec n)
    (j : Nat) (hj : j < n) (i : Nat) (hi : i < n) (s : ComplexFloat32) : ComplexFloat32 :=
  if i = j then s + mulr (mul α x[j]) A[(j, j)].re + mul α (hemvDot uplo A x j hj)
  else if InTri uplo i j then s + mul (mul α x[j]) A[(i, j)]
  else s

/-- The step `j` of `hemv`, on `y`. -/
public def hemvCol (uplo : Float32.Uplo) (α : ComplexFloat32) (A : Mat n n) (x : Vec n) (j : Nat)
    (hj : j < n) (y : Vec n) : Vec n :=
  let t₁ := mul α x[j]
  let y :=
    if uplo = .upper then
      y.withSlice 0 j (by lia) (fun s => Vec.axpyData t₁ ((A.col j hj).slice 0 j (by lia)) s)
        (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])
    else
      y.withSlice (j + 1) (n - (j + 1)) (by lia)
        (fun s => Vec.axpyData t₁ ((A.col j hj).slice (j + 1) (n - (j + 1)) (by lia)) s)
        (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])
  y.set j hj (y[j] + mulr t₁ A[(j, j)].re + mul α (hemvDot uplo A x j hj))

private theorem getElem_hemvCol (uplo : Float32.Uplo) (α : ComplexFloat32) (A : Mat n n) (x : Vec n)
    (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (hemvCol uplo α A x j hj y)[i] = hemvStep uplo α A x j hj i hi y[i] := by
  have hw : ∀ (lo len : Nat) (h : lo + len ≤ n) (l : Nat) (hl : l < n),
      (y.withSlice lo len h (fun s => Vec.axpyData (mul α x[j]) ((A.col j hj).slice lo len
        (by lia)) s) (fun s => by rw [Vec.axpyData_eq, size_modifyAt2]))[l] =
        if lo ≤ l ∧ l < lo + len then y[l] + mul (mul α x[j]) A[(l, j)] else y[l] := by
    intro lo len h l hl
    rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.axpyData_eq ..)]
    split
    · simp only [Vec.get0, show l - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col]
      have e : lo + (l - lo) = l := by lia
      simp only [e]
      rfl
    · rfl
  unfold hemvCol hemvStep
  rw [Vec.getElem_set]
  cases uplo
  rotate_left
  · simp only [reduceCtorEq, ↓reduceIte, InTri, false_and, true_and, false_or]
    rw [hw _ _ _ j hj, hw _ _ _ i hi]
    by_cases e : i = j
    · subst e; simp [show ¬(i + 1 ≤ i) by lia]
    · have h1 : (j + 1 ≤ i ∧ i < j + 1 + (n - (j + 1))) = (j < i) := by apply propext; lia
      simp [e, h1]
  · simp only [↓reduceIte, InTri, true_and]
    rw [hw _ _ _ j hj, hw _ _ _ i hi]
    by_cases e : i = j
    · subst e; simp
    · simp [e]

/--
`hemv uplo α A x β y` is `α * A * x + β * y` for the Hermitian matrix `A` stored in its upper
triangle (`.upper`) or its lower triangle (`.lower`), as `chemv`: it returns `y` when `n = 0`, or
`α = 0` and `β = 1`; it scales `y` by `β` (`betaScal`), returns when `α = 0`, and then runs the
steps `hemvCol` for each column in increasing order. It reads only the real part of the diagonal.
-/
@[expose] public def hemv (uplo : Float32.Uplo) (α : ComplexFloat32) (A : Mat n n) (x : Vec n)
    (β : ComplexFloat32) (y : Vec n) : Vec n :=
  if n = 0 then y
  else if isZero α && isOne β then y
  else
    let y := y.betaScal β
    if isZero α then y else Nat.fold n (fun j hj y => hemvCol uplo α A x j hj y) y

/--
Element `i` of `hemv`: `betaMul β y[i]` when `α = 0`, and otherwise the fold of the steps
`hemvStep` over the columns, from `betaMul β y[i]`.
-/
public theorem getElem_hemv (uplo : Float32.Uplo) (α : ComplexFloat32) (A : Mat n n) (x : Vec n)
    (β : ComplexFloat32) (y : Vec n) (i : Nat) (h : i < n) :
    (hemv uplo α A x β y)[i] =
      if isZero α then betaMul β y[i]
      else Nat.fold n (fun j hj s => hemvStep uplo α A x j hj i h s) (betaMul β y[i]) := by
  unfold hemv
  have hn : n ≠ 0 := by lia
  simp only [hn, ↓reduceIte]
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp [ha, hb]
  · simp only [ha, Bool.false_and, reduceCtorEq, ↓reduceIte]
    rw [Vec.getElem_fold_of_pointwise (fun j hj y => hemvCol uplo α A x j hj y)
      (fun j hj i hi s => hemvStep uplo α A x j hj i hi s)
      (fun j hj y i hi => getElem_hemvCol uplo α A x j hj y i hi) _ i h n (Nat.le_refl _),
      Vec.getElem_betaScal]

/-! ## `her` -/

/--
Element `(i, j)` of `her uplo α x A` from its old value `a`, for `α ≠ 0`: with
`t = mul (ofReal α) x[j].conj`, it adds `mul x[i] t` in the triangle, and on the diagonal it gives
`⟨a.re + (mul x[j] t).re, 0⟩` in the upper triangle and `⟨a.re + (mul t x[j]).re, 0⟩` in the
lower one, as `cher`; a column with `x[j] = 0` keeps its elements, but the imaginary part of its
diagonal is set to `0`.
-/
@[expose] public def herAt (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (i j : Nat) (hi : i < n)
    (hj : j < n) (a : ComplexFloat32) : ComplexFloat32 :=
  let t := mul (ofReal α) x[j].conj
  if isZero x[j] then (if i = j then ⟨a.re, 0⟩ else a)
  else if i = j then ⟨a.re + (if uplo = .upper then mul x[j] t else mul t x[j]).re, 0⟩
  else if InTri uplo i j then a + mul x[i] t
  else a

/-- The diagonal element `a` of column `j` replaced by `⟨g a.re, 0⟩`. -/
@[inline] public def setDiag (A : Mat n n) (j : Nat) (hj : j < n) (g : Float32 → Float32) :
    Mat n n :=
  A.withColSlice j hj j 1 (by lia)
    (fun s => s.data.modifyStride2 s.reStride s.imStride 1 (fun u _ => g u) (fun _ _ => 0)
      s.fits_re s.fits_im) (fun _ => by simp)

private theorem getElem_setDiag (A : Mat n n) (j : Nat) (hj : j < n) (g : Float32 → Float32)
    (i j' : Nat) (h : i < n ∧ j' < n) :
    (A.setDiag j hj g)[(i, j')] =
      if j' = j ∧ i = j then ⟨g A[(i, j')].re, 0⟩ else A[(i, j')] := by
  unfold setDiag
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ (fun _ u _ => g u) (fun _ _ _ => 0)
    (modifyStride2_eq ..)]
  have : (j ≤ i ∧ i < j + 1) = (i = j) := by apply propext; lia
  simp only [this]

/-- The step `j` of `her`, on `A`. -/
public def herCol (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (j : Nat) (hj : j < n)
    (A : Mat n n) : Mat n n :=
  if isZero x[j] then A.setDiag j hj id
  else
    let t := mul (ofReal α) x[j].conj
    if uplo = .upper then
      let A := A.withColSlice j hj 0 j (by lia)
        (fun s => Vec.axpyRData t (x.slice 0 j (by lia)) s)
        (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])
      A.setDiag j hj (· + (mul x[j] t).re)
    else
      let A := A.setDiag j hj (· + (mul t x[j]).re)
      A.withColSlice j hj (j + 1) (n - (j + 1)) (by lia)
        (fun s => Vec.axpyRData t (x.slice (j + 1) (n - (j + 1)) (by lia)) s)
        (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])

/-- The update of a slice of column `j` by `axpyRData t` of the same slice of `v`. -/
private theorem getElem_withColSlice_axpyR (A : Mat n n) (j : Nat) (hj : j < n) (lo len : Nat)
    (h : lo + len ≤ n) (t : ComplexFloat32) (v : Vec n) (i j' : Nat) (hij : i < n ∧ j' < n) :
    (A.withColSlice j hj lo len h (fun s => Vec.axpyRData t (v.slice lo len h) s)
      (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2]))[(i, j')] =
      if j' = j ∧ lo ≤ i ∧ i < lo + len then A[(i, j')] + mul v[i] t else A[(i, j')] := by
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.axpyRData_eq ..)]
  split
  · simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice]
    have e : lo + (i - lo) = i := by lia
    simp only [e]
    rfl
  · rfl

private theorem getElem_herCol (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (j : Nat)
    (hj : j < n) (A : Mat n n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (herCol uplo α x j hj A)[(i, j')] =
      if j = j' then herAt uplo α x i j h.1 hj A[(i, j')] else A[(i, j')] := by
  unfold herCol herAt
  by_cases e : j = j'
  · subst e
    by_cases hz : isZero x[j]
    · simp only [hz, ↓reduceIte, getElem_setDiag, true_and]
      by_cases e' : i = j
      · subst e'; simp
      · simp [e']
    · simp only [hz, reduceCtorEq, ↓reduceIte]
      cases uplo
      rotate_left
      · simp only [reduceCtorEq, ↓reduceIte, getElem_withColSlice_axpyR, getElem_setDiag,
          true_and, InTri, false_and, false_or]
        by_cases e' : i = j
        · subst e'; simp [show ¬(i + 1 ≤ i) by lia]
        · have h1 : (j + 1 ≤ i ∧ i < j + 1 + (n - (j + 1))) = (j < i) := by
            apply propext; lia
          simp [e', h1]
      · simp only [↓reduceIte, getElem_withColSlice_axpyR, getElem_setDiag, true_and, InTri]
        by_cases e' : i = j
        · subst e'; simp
        · simp [e']
  · have e' : ¬j' = j := Ne.symm e
    by_cases hz : isZero x[j]
    · simp [hz, getElem_setDiag, e, e']
    · cases uplo <;> simp [hz, getElem_withColSlice_axpyR, getElem_setDiag, e, e']

/--
`her uplo α x A` is `α * x * xᴴ + A`, for a real `α`, on the upper triangle of `A` (`.upper`) or its
lower triangle (`.lower`), as `cher`: it returns `A` when `n = 0` or `α = 0`, and otherwise runs the
steps `herCol` for each column in increasing order. The other triangle is unchanged.
-/
@[expose] public def her (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (A : Mat n n) : Mat n n :=
  if α == 0 then A else Nat.fold n (fun j hj A => herCol uplo α x j hj A) A

/-- Element `(i, j)` of `her`: `A[i, j]` when `α = 0`, and `herAt uplo α x i j A[i, j]`. -/
public theorem getElem_her (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (A : Mat n n) (i j : Nat)
    (h : i < n ∧ j < n) :
    (her uplo α x A)[(i, j)] =
      if α == 0 then A[(i, j)] else herAt uplo α x i j h.1 h.2 A[(i, j)] := by
  unfold her
  split
  · rfl
  · rw [getElem_fold_of_pointwise (fun l hl B => herCol uplo α x l hl B)
      (fun l hl i j' hij s => if l = j' then herAt uplo α x i l hij.1 hl s else s)
      (fun l hl B i j' hij => getElem_herCol uplo α x l hl B i j' hij) A i j h n (Nat.le_refl _),
      fold_ite_eq j (fun l hl s => herAt uplo α x i l h.1 hl s) _ n (Nat.le_refl _)]
    simp [h.2]

/-! ## `her2` -/

/--
Element `(i, j)` of `her2 uplo α x y A` from its old value `a`, for `α ≠ 0`: with
`t₁ = mul α y[j].conj` and `t₂ = (mul α x[j]).conj`, it adds `mul x[i] t₁` and then `mul y[i] t₂`
in the triangle, and on the diagonal it gives `⟨a.re + (mul x[j] t₁ + mul y[j] t₂).re, 0⟩`, as
`cher2`; a column with `x[j] = 0` and `y[j] = 0` keeps its elements, but the imaginary part of
its diagonal is set to `0`.
-/
@[expose] public def her2At (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (i j : Nat)
    (hi : i < n) (hj : j < n) (a : ComplexFloat32) : ComplexFloat32 :=
  let t₁ := mul α y[j].conj
  let t₂ := (mul α x[j]).conj
  if isZero x[j] && isZero y[j] then (if i = j then ⟨a.re, 0⟩ else a)
  else if i = j then ⟨a.re + (mul x[j] t₁ + mul y[j] t₂).re, 0⟩
  else if InTri uplo i j then a + mul x[i] t₁ + mul y[i] t₂
  else a

/-- The step `j` of `her2`, on `A`. -/
public def her2Col (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (j : Nat) (hj : j < n)
    (A : Mat n n) : Mat n n :=
  if isZero x[j] && isZero y[j] then A.setDiag j hj id
  else
    let t₁ := mul α y[j].conj
    let t₂ := (mul α x[j]).conj
    let w := (mul x[j] t₁ + mul y[j] t₂).re
    if uplo = .upper then
      let A := A.withColSlice j hj 0 j (by lia)
        (fun s => Vec.axpyRData t₁ (x.slice 0 j (by lia)) s)
        (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])
      let A := A.withColSlice j hj 0 j (by lia)
        (fun s => Vec.axpyRData t₂ (y.slice 0 j (by lia)) s)
        (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])
      A.setDiag j hj (· + w)
    else
      let A := A.setDiag j hj (· + w)
      let A := A.withColSlice j hj (j + 1) (n - (j + 1)) (by lia)
        (fun s => Vec.axpyRData t₁ (x.slice (j + 1) (n - (j + 1)) (by lia)) s)
        (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])
      A.withColSlice j hj (j + 1) (n - (j + 1)) (by lia)
        (fun s => Vec.axpyRData t₂ (y.slice (j + 1) (n - (j + 1)) (by lia)) s)
        (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])

private theorem getElem_her2Col (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (j : Nat)
    (hj : j < n) (A : Mat n n) (i j' : Nat) (h : i < n ∧ j' < n) :
    (her2Col uplo α x y j hj A)[(i, j')] =
      if j = j' then her2At uplo α x y i j h.1 hj A[(i, j')] else A[(i, j')] := by
  unfold her2Col her2At
  by_cases e : j = j'
  · subst e
    by_cases hz : isZero x[j] && isZero y[j]
    · simp only [hz, ↓reduceIte, getElem_setDiag, true_and]
      by_cases e' : i = j
      · subst e'; simp
      · simp [e']
    · simp only [hz, reduceCtorEq, ↓reduceIte]
      cases uplo
      rotate_left
      · simp only [reduceCtorEq, ↓reduceIte, getElem_withColSlice_axpyR, getElem_setDiag,
          true_and, InTri, false_and, false_or]
        by_cases e' : i = j
        · subst e'; simp [show ¬(i + 1 ≤ i) by lia]
        · have h1 : (j + 1 ≤ i ∧ i < j + 1 + (n - (j + 1))) = (j < i) := by
            apply propext; lia
          by_cases hji : j < i <;> simp [e', h1, hji]
      · simp only [↓reduceIte, getElem_withColSlice_axpyR, getElem_setDiag, true_and, InTri]
        by_cases e' : i = j
        · subst e'; simp
        · by_cases hji : i < j <;> simp [e', hji]
  · have e' : ¬j' = j := Ne.symm e
    by_cases hz : isZero x[j] && isZero y[j]
    · simp [hz, getElem_setDiag, e, e']
    · cases uplo <;> simp [hz, getElem_withColSlice_axpyR, getElem_setDiag, e, e']

/--
`her2 uplo α x y A` is `α * x * yᴴ + conj α * y * xᴴ + A` on the upper triangle of `A`
(`.upper`) or its lower triangle (`.lower`), as `cher2`: it returns `A` when `α = 0`, and otherwise
runs the steps `her2Col` for each column in increasing order. The other triangle is unchanged.
-/
@[expose] public def her2 (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (A : Mat n n) :
    Mat n n :=
  if isZero α then A else Nat.fold n (fun j hj A => her2Col uplo α x y j hj A) A

/-- Element `(i, j)` of `her2`: `A[i, j]` when `α = 0`, and `her2At uplo α x y i j A[i, j]`. -/
public theorem getElem_her2 (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (A : Mat n n)
    (i j : Nat) (h : i < n ∧ j < n) :
    (her2 uplo α x y A)[(i, j)] =
      if isZero α then A[(i, j)] else her2At uplo α x y i j h.1 h.2 A[(i, j)] := by
  unfold her2
  split
  · rfl
  · rw [getElem_fold_of_pointwise (fun l hl B => her2Col uplo α x y l hl B)
      (fun l hl i j' hij s => if l = j' then her2At uplo α x y i l hij.1 hl s else s)
      (fun l hl B i j' hij => getElem_her2Col uplo α x y l hl B i j' hij) A i j h n
      (Nat.le_refl _),
      fold_ite_eq j (fun l hl s => her2At uplo α x y i l h.1 hl s) _ n (Nat.le_refl _)]
    simp [h.2]

end Mat

end BLAS.ComplexFloat32
