/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Level1
public import BatteriesBLAS.ComplexFloat64.Mat

/-!
# Complex Level 2

Matrix-vector operations on complex matrices: the products `gemv` (`y := α * A * x + β * y`),
`gemvT` (with the transpose of `A`) and `gemvC` (with its conjugate transpose), and the rank-one
updates `geru` (`A := α * x * yᵀ + A`) and `gerc` (`A := α * x * yᴴ + A`).

Each routine computes every element with the operations of `zgemv`, `zgeru` and `zgerc` in the
reference BLAS (`master`), in the same order, with the complex product `mul`. `gemv` adds the
columns of `A` to `y` one at a time, as an `axpy` without the early return; `gemvT` and `gemvC`
compute each element of `y` from a `dotu` or `dotc` of a column of `A` with `x`; `geru` and `gerc`
update `A` one column at a time, in place when its array is not shared, and skip the columns `j`
with `y[j] = 0`, as the reference BLAS does.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.ComplexFloat64

/-- `z = 0`, as `.EQ. ZERO` in Fortran: both parts are zero, of either sign. -/
@[inline, expose] public def isZero (z : ComplexFloat) : Bool := z.re == 0 && z.im == 0

/-- `z = 1`, as `.EQ. ONE` in Fortran. -/
@[inline, expose] public def isOne (z : ComplexFloat) : Bool := z.re == 1 && z.im == 0

/--
`β * v` as the reference BLAS scales `y` in `zgemv`: `v` when `β = 1`, `0` when `β = 0`, without
reading `v`, and `mul β v` otherwise.
-/
@[expose] public def betaMul (β v : ComplexFloat) : ComplexFloat :=
  if isOne β then v else if isZero β then zero else mul β v

namespace Vec

variable {n : Nat}

/--
`axpyN α x y` is `y + mul α x`, as `axpy` computes it but without its early return when `α = 0`,
as in the loops of `zgemv`.
-/
@[expose] public def axpyN (α : ComplexFloat) (x y : Vec n) : Vec n where
  data := axpyData α x y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [axpyData_eq, size_modifyAt2]; exact y.bound

@[simp] public theorem off_axpyN (α : ComplexFloat) (x y : Vec n) : (axpyN α x y).off = y.off :=
  rfl

@[simp] public theorem inc_axpyN (α : ComplexFloat) (x y : Vec n) : (axpyN α x y).inc = y.inc :=
  rfl

@[simp] public theorem getElem_axpyN (α : ComplexFloat) (x y : Vec n) (i : Nat) (h : i < n) :
    (axpyN α x y)[i] = y[i] + mul α x[i] := by
  refine (getElem_of_data_eq_modifyAt2 (v := axpyN α x y) (w := y) _ _ (axpyData_eq α x y) rfl rfl
    i h).trans ?_
  simp [get0, h]
  rfl

/-- The array of `y + mul x α`, with `α` on the right, as in the loops of `zgeru` and `zgerc`. -/
public def axpyRData (α : ComplexFloat) (x y : Vec n) : Float64Array :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2
    let a := y.data
    let o := (2 * y.off).toUSize
    let o1 := (2 * y.off + 1).toUSize
    let c := (2 * y.inc).toUSize
    let xo := (2 * x.off).toUSize
    let xo1 := (2 * x.off + 1).toUSize
    let xc := (2 * x.inc).toUSize
    let ar := α.re
    let ai := α.im
    inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_re_lt hs.2 (by lia)
        have hk1 : (o1 + c * k).toNat < a.size := y.toNat_im_lt hs.2 (by lia)
        let u := a[o + c * k]
        let v := a[o1 + c * k]
        a[o + c * k] := u + mulRe (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia)) ⟨ar, ai⟩
        a[o1 + c * k] := v + mulIm (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia)) ⟨ar, ai⟩
  else y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
    (fun i u _ => u + (mul (x.get0 i) α).re) (fun i _ v => v + (mul (x.get0 i) α).im)

public theorem axpyRData_eq (α : ComplexFloat) (x y : Vec n) :
    axpyRData α x y = y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
      (fun i u _ => u + (mul (x.get0 i) α).re) (fun i _ v => v + (mul (x.get0 i) α).im) := by
  unfold axpyRData
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify2 (ia := y.reStride.idx) (ib := y.imStride.idx)
      (F := fun i u _ => u + (mul (x.get0 i) α).re) (G := fun i _ v => v + (mul (x.get0 i) α).im)
      (hea := y.loop_re hs.2) (heb := y.loop_im hs.2)]
    · simp only [Tail.run_done, y.toNat_toUSize hs.2, USize.toNat_zero]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
  · rfl

/--
`betaScal β y` is `y` with each element `v` replaced by `betaMul β v`, as `zgemv` scales `y`: it
returns `y` when `β = 1`, and writes zeros without reading `y` when `β = 0`.
-/
@[expose] public def betaScal (β : ComplexFloat) (y : Vec n) : Vec n :=
  if isOne β then y
  else if isZero β then
    { data := y.data.modifyStride2 y.reStride y.imStride n (fun _ _ => 0) (fun _ _ => 0)
        y.fits_re y.fits_im
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [size_modifyStride2]; exact y.bound }
  else scal β y

@[simp] public theorem off_betaScal (β : ComplexFloat) (y : Vec n) :
    (betaScal β y).off = y.off := by
  unfold betaScal; split
  · rfl
  · split
    · rfl
    · exact off_scal ..

@[simp] public theorem inc_betaScal (β : ComplexFloat) (y : Vec n) :
    (betaScal β y).inc = y.inc := by
  unfold betaScal; split
  · rfl
  · split
    · rfl
    · exact inc_scal ..

@[simp] public theorem getElem_betaScal (β : ComplexFloat) (y : Vec n) (i : Nat) (h : i < n) :
    (betaScal β y)[i] = betaMul β y[i] := by
  unfold betaScal betaMul
  by_cases h1 : isOne β
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : isZero β
    · simp only [h0, ↓reduceIte]
      exact getElem_of_data_eq_modifyAt2 (v := ⟨_, y.off, y.inc, y.inc_pos, _⟩) (w := y) _ _
        (modifyStride2_eq ..) rfl rfl i h
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, getElem_scal]
      simp only [isOne] at h1
      simp [h1]

/--
An entry of the array of `x` at none of the indices of the elements of `x` is unchanged by a
`modifyAt2` over the elements.
-/
public theorem getElem_data_modifyAt2_of_ne (x : Vec n) (F G : Nat → Float → Float → Float)
    {p : Nat} (hp : ∀ k, k < n → x.reStride.idx k ≠ p ∧ x.imStride.idx k ≠ p)
    (h : p < (x.data.modifyAt2 x.reStride.idx x.imStride.idx 0 n F G).size) :
    (x.data.modifyAt2 x.reStride.idx x.imStride.idx 0 n F G)[p] =
      x.data[p]'(by simpa using h) := by
  have hinj : ∀ (s : Stride) (_ : s.inc = 2 * x.inc), ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n →
      s.idx i = s.idx j → i = j := by
    intro s hs i _ hi j _ hj e
    simp only [Stride.idx, hs] at e
    rcases x.inc_pos with hc | hc
    · have : 2 * x.inc * i = 2 * x.inc * j := by lia
      exact Nat.eq_of_mul_eq_mul_left (by lia) this
    · lia
  have e := modifyAt2_eq x.data F G (hinj _ rfl) (hinj _ rfl)
    (fun i _ _ j _ _ => x.re_ne_im i j)
  simp only [e]
  rw [getElem_modifyAt_of_forall_ne _ _ _ (fun k _ hk => (hp k hk).2) (by simpa using h),
    getElem_modifyAt_of_forall_ne _ _ _ (fun k _ hk => (hp k hk).1) (by simpa using h)]

end Vec

namespace Mat

variable {m n : Nat}

/-! ## `gemv` -/

/-- The loops of `gemv` over the columns: `y := y + mul (mul α x[j]) A[:, j]` for each `j`. -/
public def gemvCols (α : ComplexFloat) (A : Mat m n) (x : Vec n) (y : Vec m) : Vec m :=
  Nat.fold n (fun j hj y => Vec.axpyN (mul α x[j]) (A.col j hj) y) y

private theorem getElem_fold_axpyN (A : Mat m n) (t : (j : Nat) → j < n → ComplexFloat)
    (y : Vec m) (i : Nat) (hi : i < m) :
    ∀ k (hk : k ≤ n),
      (Nat.fold k (fun j hj y => Vec.axpyN (t j (by lia)) (A.col j (by lia)) y) y)[i] =
        Nat.fold k (fun j hj s => s + mul (t j (by lia)) (A[(i, j)]'⟨hi, by lia⟩)) y[i]
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Nat.fold_succ, Nat.fold_succ, Vec.getElem_axpyN, getElem_fold_axpyN A t y i hi k (by lia)]
    rfl

/--
`gemv α A x β y` is `α * A * x + β * y`, as `zgemv` with `TRANS = 'N'`: it returns `y` when
`m = 0`, `n = 0`, or `α = 0` and `β = 1`; it scales `y` by `β` (`betaScal`), returns when `α = 0`,
and then adds `mul α x[j]` times column `j` of `A` for each `j` in increasing order.
-/
@[expose] public def gemv (α : ComplexFloat) (A : Mat m n) (x : Vec n) (β : ComplexFloat)
    (y : Vec m) : Vec m :=
  if m = 0 ∨ n = 0 then y
  else if isZero α && isOne β then y
  else
    let y := y.betaScal β
    if isZero α then y else gemvCols α A x y

/--
Element `i` of `gemv α A x β y`: `y[i]` when `n = 0`, `betaMul β y[i]` when `α = 0`, and
otherwise `betaMul β y[i] + mul (mul α x[0]) A[i, 0] + … + mul (mul α x[n - 1]) A[i, n - 1]`, from
the left.
-/
public theorem getElem_gemv (α : ComplexFloat) (A : Mat m n) (x : Vec n) (β : ComplexFloat)
    (y : Vec m) (i : Nat) (h : i < m) :
    (gemv α A x β y)[i] =
      if n = 0 then y[i]
      else if isZero α then betaMul β y[i]
      else Nat.fold n (fun j hj s => s + mul (mul α x[j]) A[(i, j)]) (betaMul β y[i]) := by
  unfold gemv
  by_cases hn : n = 0
  · simp [hn]
  · have hmn : (m = 0 ∨ n = 0) = False := propext ⟨fun _ => by lia, False.elim⟩
    simp only [hmn, ↓reduceIte]
    simp only [hn, ↓reduceIte]
    by_cases ha : isZero α
    · by_cases hb : isOne β
      · simp [ha, hb, betaMul]
      · simp [ha, hb]
    · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte, gemvCols]
      rw [getElem_fold_axpyN A (fun j hj => mul α x[j]) _ i h n (Nat.le_refl _),
        Vec.getElem_betaScal]

/-! ## `gemvT` and `gemvC` -/

/--
The value of `gemvT` (or of `gemvC` when `conj`) at the index `j` of `y`, from its old value `v`:
`betaMul β v`, plus `mul α t` unless `α = 0`, where `t` is the `dotu` (or `dotc`) of column `j` of
`A` with `x`.
-/
@[expose] public def gemvTAt (conj : Bool) (α : ComplexFloat) (A : Mat m n) (x : Vec m)
    (β : ComplexFloat) (j : Nat) (hj : j < n) (v : ComplexFloat) : ComplexFloat :=
  let v := betaMul β v
  if isZero α then v
  else v + mul α (if conj then Vec.dotc (A.col j hj) x else Vec.dotu (A.col j hj) x)

/-- `gemvTAt` at the index `j`, or `v` out of bounds, for the models. -/
@[expose] public def gemvTAt0 (conj : Bool) (α : ComplexFloat) (A : Mat m n) (x : Vec m)
    (β : ComplexFloat) (j : Nat) (v : ComplexFloat) : ComplexFloat :=
  if hj : j < n then gemvTAt conj α A x β j hj v else v

/-- The array of `gemvT` and `gemvC`. -/
public def gemvTData (conj : Bool) (α : ComplexFloat) (A : Mat m n) (x : Vec m)
    (β : ComplexFloat) (y : Vec n) : Float64Array :=
  if hs : y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs
    let a := y.data
    let o := (2 * y.off).toUSize
    let o1 := (2 * y.off + 1).toUSize
    let c := (2 * y.inc).toUSize
    inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_re_lt hs (by lia)
        have hk1 : (o1 + c * k).toNat < a.size := y.toNat_im_lt hs (by lia)
        let u := a[o + c * k]
        let v := a[o1 + c * k]
        let w := gemvTAt conj α A x β k.toNat (by lia) ⟨u, v⟩
        a[o + c * k] := w.re
        a[o1 + c * k] := w.im
  else y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
    (fun j u v => (gemvTAt0 conj α A x β j ⟨u, v⟩).re)
    (fun j u v => (gemvTAt0 conj α A x β j ⟨u, v⟩).im)

public theorem gemvTData_eq (conj : Bool) (α : ComplexFloat) (A : Mat m n) (x : Vec m)
    (β : ComplexFloat) (y : Vec n) :
    gemvTData conj α A x β y = y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
      (fun j u v => (gemvTAt0 conj α A x β j ⟨u, v⟩).re)
      (fun j u v => (gemvTAt0 conj α A x β j ⟨u, v⟩).im) := by
  unfold gemvTData
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify2 (ia := y.reStride.idx) (ib := y.imStride.idx)
      (F := fun j u v => (gemvTAt0 conj α A x β j ⟨u, v⟩).re)
      (G := fun j u v => (gemvTAt0 conj α A x β j ⟨u, v⟩).im)
      (hea := y.loop_re hs) (heb := y.loop_im hs)]
    · simp only [Tail.run_done, y.toNat_toUSize hs, USize.toNat_zero]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs] at hj
      simp [gemvTAt0, hj]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs] at hj
      simp [gemvTAt0, hj]
  · rfl

/-- `gemvT` and `gemvC`, by `conj`, with the quick returns of the reference BLAS. -/
@[expose] public def gemvTWith (conj : Bool) (α : ComplexFloat) (A : Mat m n) (x : Vec m)
    (β : ComplexFloat) (y : Vec n) : Vec n :=
  if m = 0 ∨ n = 0 then y
  else if isZero α && isOne β then y
  else
    { data := gemvTData conj α A x β y
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [gemvTData_eq, size_modifyAt2]; exact y.bound }

public theorem getElem_gemvTWith (conj : Bool) (α : ComplexFloat) (A : Mat m n) (x : Vec m)
    (β : ComplexFloat) (y : Vec n) (j : Nat) (h : j < n) :
    (gemvTWith conj α A x β y)[j] = if m = 0 then y[j] else gemvTAt conj α A x β j h y[j] := by
  unfold gemvTWith
  by_cases hm : m = 0
  · simp [hm]
  · have hmn : (m = 0 ∨ n = 0) = False := propext ⟨fun _ => by lia, False.elim⟩
    simp only [hmn, ↓reduceIte]
    simp only [hm, ↓reduceIte]
    by_cases hq : isZero α && isOne β
    · simp only [hq, ↓reduceIte]
      simp only [Bool.and_eq_true] at hq
      simp [gemvTAt, betaMul, hq.1, hq.2]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      refine (Vec.getElem_of_data_eq_modifyAt2 (v := ⟨_, y.off, y.inc, y.inc_pos, _⟩) (w := y) _ _
        (gemvTData_eq conj α A x β y) rfl rfl j h).trans ?_
      simp [gemvTAt0, h]
      rfl

/--
`gemvT α A x β y` is `α * Aᵀ * x + β * y`, as `zgemv` with `TRANS = 'T'`. Element `j` is `y[j]`
when `m = 0`, and otherwise `betaMul β y[j]`, plus `mul α (dotu A[:, j] x)` unless `α = 0`.
-/
@[expose] public def gemvT (α : ComplexFloat) (A : Mat m n) (x : Vec m) (β : ComplexFloat)
    (y : Vec n) : Vec n :=
  gemvTWith false α A x β y

public theorem getElem_gemvT (α : ComplexFloat) (A : Mat m n) (x : Vec m) (β : ComplexFloat)
    (y : Vec n) (j : Nat) (h : j < n) :
    (gemvT α A x β y)[j] =
      if m = 0 then y[j]
      else if isZero α then betaMul β y[j]
      else betaMul β y[j] + mul α (Vec.dotu (A.col j h) x) := by
  simp [gemvT, getElem_gemvTWith, gemvTAt]

/--
`gemvC α A x β y` is `α * Aᴴ * x + β * y`, as `zgemv` with `TRANS = 'C'`. Element `j` is `y[j]`
when `m = 0`, and otherwise `betaMul β y[j]`, plus `mul α (dotc A[:, j] x)` unless `α = 0`.
-/
@[expose] public def gemvC (α : ComplexFloat) (A : Mat m n) (x : Vec m) (β : ComplexFloat)
    (y : Vec n) : Vec n :=
  gemvTWith true α A x β y

public theorem getElem_gemvC (α : ComplexFloat) (A : Mat m n) (x : Vec m) (β : ComplexFloat)
    (y : Vec n) (j : Nat) (h : j < n) :
    (gemvC α A x β y)[j] =
      if m = 0 then y[j]
      else if isZero α then betaMul β y[j]
      else betaMul β y[j] + mul α (Vec.dotc (A.col j h) x) := by
  simp [gemvC, getElem_gemvTWith, gemvTAt]

/-! ## `geru` and `gerc` -/

/--
Column `j` of `A` with `mul x[i] t` added to each element `i`, in place when the array of `A` is
not shared.
-/
public def gerCol (t : ComplexFloat) (x : Vec m) (A : Mat m n) (j : Nat) (hj : j < n) :
    Mat m n :=
  match A with
  | ⟨d, off, ld, hle, hb⟩ =>
    let c := Mat.col ⟨d, off, ld, hle, hb⟩ j hj
    ⟨Vec.axpyRData t x c, off, ld, hle, by rw [Vec.axpyRData_eq, size_modifyAt2]; exact hb⟩

@[simp] public theorem off_gerCol (t : ComplexFloat) (x : Vec m) (A : Mat m n) (j : Nat)
    (hj : j < n) : (gerCol t x A j hj).off = A.off := by
  cases A; rfl

@[simp] public theorem ld_gerCol (t : ComplexFloat) (x : Vec m) (A : Mat m n) (j : Nat)
    (hj : j < n) : (gerCol t x A j hj).ld = A.ld := by
  cases A; rfl

public theorem data_gerCol (t : ComplexFloat) (x : Vec m) (A : Mat m n) (j : Nat) (hj : j < n) :
    (gerCol t x A j hj).data = (A.col j hj).data.modifyAt2 (A.col j hj).reStride.idx
      (A.col j hj).imStride.idx 0 m (fun i u _ => u + (mul (x.get0 i) t).re)
      (fun i _ v => v + (mul (x.get0 i) t).im) := by
  cases A; exact Vec.axpyRData_eq ..

/-- Two elements of different columns are at different indices. -/
private theorem index_ne (A : Mat m n) {i k j j' : Nat} (hj : j ≠ j') (hi : i < m) (hk : k < m) :
    A.off + A.ld * j + i ≠ A.off + A.ld * j' + k := by
  intro e
  have hl := A.le_ld
  have e' : A.ld * j + i = A.ld * j' + k := by lia
  have h1 : (A.ld * j + i) / A.ld = j := by
    rw [Nat.mul_add_div (by lia), Nat.div_eq_of_lt (by lia), Nat.add_zero]
  have h2 : (A.ld * j' + k) / A.ld = j' := by
    rw [Nat.mul_add_div (by lia), Nat.div_eq_of_lt (by lia), Nat.add_zero]
  exact hj (by rw [← h1, ← h2, e'])

public theorem getElem_gerCol (t : ComplexFloat) (x : Vec m) (A : Mat m n) (j : Nat) (hj : j < n)
    (i j' : Nat) (h : i < m ∧ j' < n) :
    (gerCol t x A j hj)[(i, j')] = if j' = j then A[(i, j')] + mul x[i] t else A[(i, j')] := by
  obtain ⟨d, off, ld, hle, hb⟩ := A
  by_cases e : j' = j
  · subst e
    simp only [↓reduceIte]
    refine (Vec.getElem_of_data_eq_modifyAt2 (v := (gerCol t x ⟨d, off, ld, hle, hb⟩ j' hj).col j'
      hj) (w := Mat.col ⟨d, off, ld, hle, hb⟩ j' hj) _ _ (Vec.axpyRData_eq ..) rfl rfl i
      h.1).trans ?_
    simp [Vec.get0, h.1]
    rfl
  · simp only [e, ↓reduceIte]
    have hne : ∀ k, k < m → off + ld * j + k ≠ off + ld * j' + i := fun k hk =>
      index_ne ⟨d, off, ld, hle, hb⟩ (Ne.symm e) hk h.1
    simp only [getElem_def, Vec.getElem_def, data_col, off_col, inc_col, off_gerCol, ld_gerCol,
      data_gerCol]
    congr 1
    · exact Vec.getElem_data_modifyAt2_of_ne (Mat.col ⟨d, off, ld, hle, hb⟩ j hj) _ _
        (fun k hk => by
          have := hne k hk
          simp only [Vec.idx_reStride, Vec.idx_imStride, off_col, inc_col]
          constructor <;> lia) _
    · exact Vec.getElem_data_modifyAt2_of_ne (Mat.col ⟨d, off, ld, hle, hb⟩ j hj) _ _
        (fun k hk => by
          have := hne k hk
          simp only [Vec.idx_reStride, Vec.idx_imStride, off_col, inc_col]
          constructor <;> lia) _

/-- `geru` and `gerc`, by the multiplier `t j` of column `j`. -/
public def gerWith (α : ComplexFloat) (x : Vec m) (y : Vec n)
    (t : (j : Nat) → j < n → ComplexFloat) (A : Mat m n) : Mat m n :=
  if isZero α then A
  else Nat.fold n (fun j hj A => if isZero y[j] then A else gerCol (t j hj) x A j hj) A

private theorem getElem_fold_gerCol (x : Vec m) (y : Vec n)
    (t : (j : Nat) → j < n → ComplexFloat) (A : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    ∀ k (hk : k ≤ n),
      (Nat.fold k (fun l hl A => if isZero y[l] then A else gerCol (t l (by lia)) x A l (by lia))
        A)[(i, j)] =
        if j < k ∧ isZero y[j] = false then A[(i, j)] + mul x[i] (t j h.2) else A[(i, j)]
  | 0, _ => by simp
  | k + 1, hk => by
    rw [Nat.fold_succ]
    have ih := getElem_fold_gerCol x y t A i j h k (by lia)
    split
    · rename_i hz
      rw [ih]
      by_cases e : j = k
      · subst e; simp [hz]
      · have : (j < k + 1) = (j < k) := by apply propext; lia
        simp only [this]
    · rename_i hz
      rw [getElem_gerCol, ih]
      by_cases e : j = k
      · subst e; simp_all
      · have : (j < k + 1) = (j < k) := by apply propext; lia
        simp [e, this]

/--
`geru α x y A` is `α * x * yᵀ + A`, as `zgeru`: it returns `A` when `α = 0`, and adds
`mul x[i] (mul α y[j])` to each element `(i, j)` of the columns `j` with `y[j] ≠ 0`.
-/
@[expose] public def geru (α : ComplexFloat) (x : Vec m) (y : Vec n) (A : Mat m n) : Mat m n :=
  gerWith α x y (fun j _ => mul α y[j]) A

public theorem getElem_geru (α : ComplexFloat) (x : Vec m) (y : Vec n) (A : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (geru α x y A)[(i, j)] =
      if isZero α || isZero y[j] then A[(i, j)] else A[(i, j)] + mul x[i] (mul α y[j]) := by
  unfold geru gerWith
  by_cases ha : isZero α
  · simp [ha]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    have hf := getElem_fold_gerCol x y (fun j _ => mul α y[j]) A i j h n (Nat.le_refl _)
    rw [hf]
    cases isZero y[j] <;> simp [h.2]

/--
`gerc α x y A` is `α * x * yᴴ + A`, as `zgerc`: it returns `A` when `α = 0`, and adds
`mul x[i] (mul α y[j].conj)` to each element `(i, j)` of the columns `j` with `y[j] ≠ 0`.
-/
@[expose] public def gerc (α : ComplexFloat) (x : Vec m) (y : Vec n) (A : Mat m n) : Mat m n :=
  gerWith α x y (fun j _ => mul α y[j].conj) A

public theorem getElem_gerc (α : ComplexFloat) (x : Vec m) (y : Vec n) (A : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (gerc α x y A)[(i, j)] =
      if isZero α || isZero y[j] then A[(i, j)]
      else A[(i, j)] + mul x[i] (mul α y[j].conj) := by
  unfold gerc gerWith
  by_cases ha : isZero α
  · simp [ha]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    have hf := getElem_fold_gerCol x y (fun j _ => mul α y[j].conj) A i j h n (Nat.le_refl _)
    rw [hf]
    cases isZero y[j] <;> simp [h.2]

end Mat

end BLAS.ComplexFloat64
