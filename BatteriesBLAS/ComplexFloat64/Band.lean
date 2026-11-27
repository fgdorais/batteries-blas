/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Tri

/-!
# Complex band matrix-vector products and solves

A band matrix is stored as in the reference BLAS, as for the real band routines. An `m × n`
matrix with `kl` subdiagonals and `ku` superdiagonals is a matrix `A : Mat (kl + ku + 1) n`. Column
`j` of `A` holds the band of column `j`: the element in row `i` of the band matrix is in row
`ku + i - j` of `A`, for `j - ku ≤ i ≤ j + kl` and `i < m`.

A Hermitian or triangular band matrix of order `n` with `k` off-diagonals is stored as
`A : Mat (k + 1) n`. In the upper triangle (`.upper`) the element `(i, j)` is in row `k + i - j`,
for `j - k ≤ i ≤ j`, so the diagonal is row `k`. In the lower triangle (`.lower`) it is in row
`i - j`, for `j ≤ i ≤ j + k`, so the diagonal is row `0`.

The routines read no other element of `A`. They are `gbmv`, `gbmvT` and `gbmvC` (`zgbmv`), `hbmv`
(`zhbmv`), `tbmv`, `tbmvT` and `tbmvC` (`ztbmv`), and `tbsv`, `tbsvT` and `tbsvC` (`ztbsv`). Each
runs the loops of the reference BLAS (`master`, which has no zero skips in `ztbmv` and `ztbsv`),
with the same operations in the same order.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.ComplexFloat64

namespace Mat

variable {m n r : Nat}

/-! ## Updates of a vector by a slice of a column -/

/--
`y` with the elements `lo ≤ i < lo + len` updated by `+ mul t A[ar + (i - lo), j]`, in place: an
`axpy` of a slice of column `j` of `A` into a slice of `y`.
-/
@[inline] public def addColAt (A : Mat r n) (j : Nat) (hj : j < n) (ar lo len : Nat)
    (ha : ar + len ≤ r) (h : lo + len ≤ m) (t : ComplexFloat) (y : Vec m) : Vec m :=
  y.withSlice lo len h (fun s => Vec.axpyData t ((A.col j hj).slice ar len ha) s)
    (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])

public theorem getElem_addColAt (A : Mat r n) (j : Nat) (hj : j < n) (ar lo len : Nat)
    (ha : ar + len ≤ r) (h : lo + len ≤ m) (t : ComplexFloat) (y : Vec m) (i : Nat) (hi : i < m) :
    (A.addColAt j hj ar lo len ha h t y)[i] =
      if hl : lo ≤ i ∧ i < lo + len then y[i] + mul t (A[(ar + (i - lo), j)]'⟨by lia, hj⟩)
      else y[i] := by
  unfold addColAt
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.axpyData_eq ..)]
  by_cases hl : lo ≤ i ∧ i < lo + len
  · simp only [hl, and_self, ↓reduceIte, ↓reduceDIte]
    simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col]
    rfl
  · simp only [hl, ↓reduceIte, ↓reduceDIte]

/-- `y` with the elements `lo ≤ i < lo + len` updated by `- mul t A[ar + (i - lo), j]`, in place. -/
@[inline] public def subColAt (A : Mat r n) (j : Nat) (hj : j < n) (ar lo len : Nat)
    (ha : ar + len ≤ r) (h : lo + len ≤ m) (t : ComplexFloat) (y : Vec m) : Vec m :=
  y.withSlice lo len h
    (fun s => Vec.zipWithData (fun v a => v.re - mulRe t a) (fun v a => v.im - mulIm t a)
      ((A.col j hj).slice ar len ha) s)
    (fun s => by rw [Vec.size_zipWithData])

public theorem getElem_subColAt (A : Mat r n) (j : Nat) (hj : j < n) (ar lo len : Nat)
    (ha : ar + len ≤ r) (h : lo + len ≤ m) (t : ComplexFloat) (y : Vec m) (i : Nat) (hi : i < m) :
    (A.subColAt j hj ar lo len ha h t y)[i] =
      if hl : lo ≤ i ∧ i < lo + len then y[i] - mul t (A[(ar + (i - lo), j)]'⟨by lia, hj⟩)
      else y[i] := by
  unfold subColAt
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  by_cases hl : lo ≤ i ∧ i < lo + len
  · simp only [hl, and_self, ↓reduceIte, ↓reduceDIte]
    simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col,
      mulRe_eq, mulIm_eq]
    rfl
  · simp only [hl, ↓reduceIte, ↓reduceDIte]

/-- A fold whose only step that changes its value is the step `j`. -/
private theorem fold_only {α : Type} {K : Nat} (j : Nat) (hj : j < K)
    (ψ : (l : Nat) → l < K → α → α) (s : α) :
    Nat.fold K (fun l hl t => if j = l then ψ l hl t else t) s = ψ j hj s := by
  have key : ∀ k (hk : k ≤ K), Nat.fold k (fun l hl t => if j = l then ψ l (by lia) t else t) s =
      if h : j < k then ψ j (by lia) s else s := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.fold_succ, ih (by lia)]
      by_cases e : j = k
      · subst e; simp
      · have : (j < k + 1) = (j < k) := by apply propext; lia
        simp only [e, this, ↓reduceIte]
  rw [key K (Nat.le_refl _)]; simp only [hj, ↓reduceDIte]

/-! ## General band storage -/

/-- The first row `j - ku` of the band in column `j`, or `m` past the last row. -/
@[expose, inline] public def gbLo (m ku j : Nat) : Nat := min (j - ku) m

/-- The number of rows of the band in column `j`, of an `m × n` matrix. -/
@[expose, inline] public def gbLen (m kl ku j : Nat) : Nat := min m (j + kl + 1) - gbLo m ku j

/-- The row of the storage of the first row of the band in column `j`. -/
@[expose, inline] public def gbAr (m ku j : Nat) : Nat := ku + gbLo m ku j - j

/-- Whether element `(i, j)` is in the band with `kl` subdiagonals and `ku` superdiagonals. -/
@[expose] public def InBand (kl ku i j : Nat) : Prop := j ≤ i + ku ∧ i ≤ j + kl

public instance (kl ku i j : Nat) : Decidable (InBand kl ku i j) := by
  unfold InBand; infer_instance

public theorem gbLo_add_gbLen (m kl ku j : Nat) : gbLo m ku j + gbLen m kl ku j ≤ m := by
  simp only [gbLo, gbLen]; grind

public theorem gbAr_add_gbLen (m kl ku j : Nat) : gbAr m ku j + gbLen m kl ku j ≤ kl + ku + 1 := by
  simp only [gbAr, gbLen, gbLo]; grind

public theorem mem_gb (m kl ku i j : Nat) (hi : i < m) :
    (gbLo m ku j ≤ i ∧ i < gbLo m ku j + gbLen m kl ku j) ↔ InBand kl ku i j := by
  simp only [gbLo, gbLen, InBand]; grind

public theorem gbAr_add_sub (m kl ku i j : Nat) (hi : i < m) (h : InBand kl ku i j) :
    gbAr m ku j + (i - gbLo m ku j) = ku + i - j := by
  simp only [gbAr, gbLo, InBand] at *; grind

/-! ## `gbmv` -/

/-- The step of `gbmv` for column `j`: add `mul α x[j]` times the band of column `j` to `y`. -/
@[inline] public def gbmvCol (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n)
    (x : Vec n) (j : Nat) (hj : j < n) (y : Vec m) : Vec m :=
  A.addColAt j hj (gbAr m ku j) (gbLo m ku j) (gbLen m kl ku j) (gbAr_add_gbLen ..)
    (gbLo_add_gbLen ..) (mul α x[j]) y

/--
The step `j` of `gbmv` at element `i` of `y`, from its value `s`: it adds
`mul (mul α x[j]) A[ku + i - j, j]` when `(i, j)` is in the band.
-/
@[expose] public def gbmvStep (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n)
    (x : Vec n) (j : Nat) (hj : j < n) (i : Nat) (s : ComplexFloat) : ComplexFloat :=
  if h : InBand kl ku i j then
    s + mul (mul α x[j]) (A[(ku + i - j, j)]'⟨by simp only [InBand] at h; lia, hj⟩)
  else s

private theorem getElem_gbmvCol (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n)
    (x : Vec n) (j : Nat) (hj : j < n) (y : Vec m) (i : Nat) (hi : i < m) :
    (gbmvCol kl ku α A x j hj y)[i] = gbmvStep kl ku α A x j hj i y[i] := by
  rw [gbmvCol, getElem_addColAt, gbmvStep]
  by_cases h : InBand kl ku i j
  · simp only [(mem_gb m kl ku i j hi).2 h, h, and_self, ↓reduceDIte]
    simp only [gbAr_add_sub m kl ku i j hi h]
  · have h' : ¬(gbLo m ku j ≤ i ∧ i < gbLo m ku j + gbLen m kl ku j) :=
      fun h' => h ((mem_gb m kl ku i j hi).1 h')
    simp only [h', h, ↓reduceDIte]

/--
`gbmv kl ku α A x β y` is `α * A * x + β * y` for the `m × n` band matrix `A`, as `zgbmv` with
`TRANS = 'N'`: it returns `y` when `m = 0`, `n = 0`, or `α = 0` and `β = 1`; it scales `y` by `β`
(`betaScal`), returns when `α = 0`, and then adds `mul α x[j]` times the band of column `j` for
each `j` in increasing order.
-/
@[expose] public def gbmv (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : ComplexFloat) (y : Vec m) : Vec m :=
  if m = 0 ∨ n = 0 then y
  else if isZero α && isOne β then y
  else
    let y := y.betaScal β
    if isZero α then y else Nat.fold n (fun j hj y => gbmvCol kl ku α A x j hj y) y

/--
Element `i` of `gbmv kl ku α A x β y`: `y[i]` when `n = 0`, `betaMul β y[i]` when `α = 0`, and
otherwise `betaMul β y[i]` plus the terms `mul (mul α x[j]) A[ku + i - j, j]` for the columns `j`
of the band of row `i`, in increasing order (`gbmvStep`).
-/
public theorem getElem_gbmv (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : ComplexFloat) (y : Vec m) (i : Nat) (h : i < m) :
    (gbmv kl ku α A x β y)[i] =
      if n = 0 then y[i]
      else if isZero α then betaMul β y[i]
      else Nat.fold n (fun j hj s => gbmvStep kl ku α A x j hj i s) (betaMul β y[i]) := by
  unfold gbmv
  by_cases hn : n = 0
  · simp [hn]
  · have hmn : (m = 0 ∨ n = 0) = False := propext ⟨fun _ => by lia, False.elim⟩
    simp only [hmn, ↓reduceIte]
    simp only [hn, ↓reduceIte]
    by_cases ha : isZero α
    · by_cases hb : isOne β
      · simp [ha, hb, betaMul]
      · simp [ha, hb]
    · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [Vec.getElem_fold_of_pointwise (fun j hj y => gbmvCol kl ku α A x j hj y)
        (fun j hj i _ s => gbmvStep kl ku α A x j hj i s)
        (fun j hj y i hi => getElem_gbmvCol kl ku α A x j hj y i hi) _ i h n (Nat.le_refl _),
        Vec.getElem_betaScal]

/-! ## `gbmvT` and `gbmvC` -/

/--
The sum of `gbmvT` (or `gbmvC`) for element `j`: the terms `mul (p A[ku + i - j, j]) x[i]` for
the rows `i` of the band of column `j`, in increasing order, from `0`.
-/
@[inline] public def gbmvTDot (p : ComplexFloat → ComplexFloat) (kl ku : Nat)
    (A : Mat (kl + ku + 1) n) (x : Vec m) (j : Nat) (hj : j < n) : ComplexFloat :=
  Vec.acc p (· + ·) zero ((A.col j hj).slice (gbAr m ku j) (gbLen m kl ku j) (gbAr_add_gbLen ..))
    (x.slice (gbLo m ku j) (gbLen m kl ku j) (gbLo_add_gbLen ..))

/--
`gbmvTDot` is the sum of the terms `mul (p A[gbAr m ku j + l, j]) x[j - ku + l]`, for the rows
`j - ku + l` of the band of column `j`.
-/
public theorem gbmvTDot_eq (p : ComplexFloat → ComplexFloat) (kl ku : Nat)
    (A : Mat (kl + ku + 1) n) (x : Vec m) (j : Nat) (hj : j < n) :
    gbmvTDot p kl ku A x j hj = Nat.fold (gbLen m kl ku j) (fun l hl s =>
      s + mul (p (A[(gbAr m ku j + l, j)]'⟨by have := gbAr_add_gbLen m kl ku j; lia, hj⟩))
        (x[gbLo m ku j + l]'(by have := gbLo_add_gbLen m kl ku j; lia))) zero := by
  simp only [gbmvTDot, Vec.acc_eq, Vec.opC_add, Vec.getElem_slice, getElem_col]

/--
The value of `gbmvTWith p` at element `j` of `y`, from its old value `v`: `betaMul β v`, plus
`mul α (gbmvTDot p kl ku A x j)` unless `α = 0`.
-/
@[inline] public def gbmvTAt (p : ComplexFloat → ComplexFloat) (kl ku : Nat)
    (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec m) (β : ComplexFloat) (j : Nat)
    (hj : j < n) (v : ComplexFloat) : ComplexFloat :=
  let v := betaMul β v
  if isZero α then v else v + mul α (gbmvTDot p kl ku A x j hj)

/--
`gbmvTWith p kl ku α A x β y` is `α * (p A)ᵀ * x + β * y`, where `p A` maps each element of the
band matrix `A` by `p`, as `zgbmv` with `TRANS = 'T'` (`p = id`) or `'C'` (`p = conj`): it
returns `y` when `m = 0`, `n = 0`, or `α = 0` and `β = 1`, and otherwise sets each element `j` of
`y` to `gbmvTAt`.
-/
@[expose, specialize] public def gbmvTWith (p : ComplexFloat → ComplexFloat) (kl ku : Nat)
    (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec m) (β : ComplexFloat) (y : Vec n) :
    Vec n :=
  if m = 0 ∨ n = 0 then y
  else if isZero α && isOne β then y
  else Nat.fold n (fun j hj y => y.set j hj (gbmvTAt p kl ku α A x β j hj y[j])) y

/--
Element `j` of `gbmvTWith p kl ku α A x β y`: `y[j]` when `m = 0`, and otherwise `betaMul β y[j]`,
plus `mul α (gbmvTDot p kl ku A x j)` unless `α = 0`.
-/
public theorem getElem_gbmvTWith (p : ComplexFloat → ComplexFloat) (kl ku : Nat)
    (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec m) (β : ComplexFloat) (y : Vec n)
    (j : Nat) (h : j < n) :
    (gbmvTWith p kl ku α A x β y)[j] =
      if m = 0 then y[j]
      else if isZero α then betaMul β y[j]
      else betaMul β y[j] + mul α (gbmvTDot p kl ku A x j h) := by
  unfold gbmvTWith
  by_cases hm : m = 0
  · simp [hm]
  · have hmn : (m = 0 ∨ n = 0) = False := propext ⟨fun _ => by lia, False.elim⟩
    simp only [hmn, ↓reduceIte]
    simp only [hm, ↓reduceIte]
    by_cases hq : isZero α && isOne β
    · simp only [hq, ↓reduceIte]
      simp only [Bool.and_eq_true] at hq
      simp [betaMul, hq.1, hq.2]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      rw [Vec.getElem_fold_of_pointwise
        (fun j hj y => y.set j hj (gbmvTAt p kl ku α A x β j hj y[j]))
        (fun l hl i _ s => if i = l then gbmvTAt p kl ku α A x β l hl s else s)
        (fun l hl y i hi => by rw [Vec.getElem_set]; split <;> simp_all) y j h n (Nat.le_refl _)]
      rw [fold_only j h (fun l hl s => gbmvTAt p kl ku α A x β l hl s)]
      rfl

/-- `gbmvT kl ku α A x β y` is `α * Aᵀ * x + β * y`, as `zgbmv` with `TRANS = 'T'`. -/
@[expose] public def gbmvT (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : ComplexFloat) (y : Vec n) : Vec n :=
  gbmvTWith id kl ku α A x β y

/-- `gbmvC kl ku α A x β y` is `α * Aᴴ * x + β * y`, as `zgbmv` with `TRANS = 'C'`. -/
@[expose] public def gbmvC (kl ku : Nat) (α : ComplexFloat) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : ComplexFloat) (y : Vec n) : Vec n :=
  gbmvTWith ComplexFloat.conj kl ku α A x β y


/-! ## Triangular band storage -/

/-- The first row of the band of column `j` other than the diagonal: `j - k` or `j + 1`. -/
@[expose, inline] public def tbLo : Float64.Uplo → Nat → Nat → Nat
  | .upper, k, j => j - k
  | .lower, _, j => j + 1

/-- The number of rows of the band of column `j` other than the diagonal, of order `n`. -/
@[expose, inline] public def tbLen : Float64.Uplo → Nat → Nat → Nat → Nat
  | .upper, _, k, j => j - (j - k)
  | .lower, n, k, j => min n (j + k + 1) - (j + 1)

/-- The row of the storage of the first row `tbLo` of the band of column `j`. -/
@[expose, inline] public def tbAr : Float64.Uplo → Nat → Nat → Nat
  | .upper, k, j => k - (j - (j - k))
  | .lower, _, _ => 1

/-- The row of the storage of the diagonal: `k` for `.upper`, `0` for `.lower`. -/
@[expose, inline] public def tbDiag : Float64.Uplo → Nat → Nat
  | .upper, k => k
  | .lower, _ => 0

/-- The row of the storage of element `(i, j)`: `k + i - j` for `.upper`, `i - j` for `.lower`. -/
@[expose] public def tbRow : Float64.Uplo → Nat → Nat → Nat → Nat
  | .upper, k, i, j => k + i - j
  | .lower, _, i, j => i - j

/-- Whether element `(i, j)` is in the band of `k` off-diagonals of the triangle, not on the
diagonal. -/
@[expose] public def InTBand (uplo : Float64.Uplo) (k i j : Nat) : Prop :=
  (uplo = .upper ∧ i < j ∧ j ≤ i + k) ∨ (uplo = .lower ∧ j < i ∧ i ≤ j + k)

public instance (uplo : Float64.Uplo) (k i j : Nat) : Decidable (InTBand uplo k i j) := by
  unfold InTBand; infer_instance

public theorem tbLo_add_tbLen (uplo : Float64.Uplo) (n k j : Nat) (hj : j < n) :
    tbLo uplo k j + tbLen uplo n k j ≤ n := by
  cases uplo <;> simp only [tbLo, tbLen] <;> grind

public theorem tbAr_add_tbLen (uplo : Float64.Uplo) (n k j : Nat) :
    tbAr uplo k j + tbLen uplo n k j ≤ k + 1 := by
  cases uplo <;> simp only [tbAr, tbLen] <;> grind

public theorem tbDiag_lt (uplo : Float64.Uplo) (k : Nat) : tbDiag uplo k < k + 1 := by
  cases uplo <;> simp only [tbDiag] <;> lia

public theorem mem_tb (uplo : Float64.Uplo) (n k i j : Nat) (hi : i < n) :
    (tbLo uplo k j ≤ i ∧ i < tbLo uplo k j + tbLen uplo n k j) ↔ InTBand uplo k i j := by
  cases uplo <;> simp only [tbLo, tbLen, InTBand, reduceCtorEq, true_and, false_and, or_false,
    false_or] <;> grind

public theorem tbAr_add_sub (uplo : Float64.Uplo) (k i j : Nat) (h : InTBand uplo k i j) :
    tbAr uplo k j + (i - tbLo uplo k j) = tbRow uplo k i j := by
  cases uplo <;> simp only [tbAr, tbLo, tbRow, InTBand, reduceCtorEq, true_and, false_and,
    or_false, false_or] at * <;> grind

public theorem tbRow_lt (uplo : Float64.Uplo) (k i j : Nat) (h : InTBand uplo k i j) :
    tbRow uplo k i j < k + 1 := by
  cases uplo <;> simp only [tbRow, InTBand, reduceCtorEq, true_and, false_and, or_false,
    false_or] at * <;> grind

public theorem not_inTBand_self (uplo : Float64.Uplo) (k j : Nat) : ¬InTBand uplo k j j := by
  simp only [InTBand]; lia

/-- Element `(i, j)` of `A`, or `0` outside `A`, for the models. -/
@[expose] public def bget0 (A : Mat r n) (i j : Nat) : ComplexFloat :=
  if h : i < r ∧ j < n then A[(i, j)] else zero

@[simp] public theorem bget0_eq (A : Mat r n) {i j : Nat} (h : i < r ∧ j < n) :
    A.bget0 i j = A[(i, j)] := by
  simp [bget0, h]

private theorem vget0_eq (x : Vec n) {i : Nat} (h : i < n) : x.get0 i = x[i] := by
  simp [Vec.get0, h]

private theorem mget_eq (A : Mat r n) {i i' j j' : Nat} (e : i = i') (e' : j = j')
    (h : i < r ∧ j < n) : A[(i, j)] = A[(i', j')]'(e ▸ e' ▸ h) := by
  subst e; subst e'; rfl

/-! ## `hbmv` -/

/-- The `dotc` of the band of column `j` of the Hermitian band matrix, without the diagonal, with
`x`. -/
@[inline] public def hbmvDot (uplo : Float64.Uplo) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (hj : j < n) : ComplexFloat :=
  Vec.acc ComplexFloat.conj (· + ·) zero
    ((A.col j hj).slice (tbAr uplo k j) (tbLen uplo n k j) (tbAr_add_tbLen ..))
    (x.slice (tbLo uplo k j) (tbLen uplo n k j) (tbLo_add_tbLen uplo n k j hj))

/--
`hbmvDot` is the sum of the terms `mul (conj A[tbAr uplo k j + l, j]) x[tbLo uplo k j + l]`, for
the rows `tbLo uplo k j + l` of the band of column `j` off the diagonal, in increasing order.
-/
public theorem hbmvDot_eq (uplo : Float64.Uplo) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (hj : j < n) :
    hbmvDot uplo k A x j hj = Nat.fold (tbLen uplo n k j) (fun l hl s =>
      s + mul (A[(tbAr uplo k j + l, j)]'⟨by have := tbAr_add_tbLen uplo n k j; lia, hj⟩).conj
        (x[tbLo uplo k j + l]'(by have := tbLo_add_tbLen uplo n k j hj; lia))) zero := by
  simp only [hbmvDot, Vec.acc_eq, Vec.opC_add, Vec.getElem_slice, getElem_col]

/-- The step of `hbmv` for column `j`, as `zhbmv`. -/
@[inline] public def hbmvCol (uplo : Float64.Uplo) (k : Nat) (α : ComplexFloat)
    (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) (y : Vec n) : Vec n :=
  let t₁ := mul α x[j]
  let y := A.addColAt j hj (tbAr uplo k j) (tbLo uplo k j) (tbLen uplo n k j)
    (tbAr_add_tbLen ..) (tbLo_add_tbLen uplo n k j hj) t₁ y
  y.set j hj (y[j] + mulr t₁ (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩).re +
    mul α (hbmvDot uplo k A x j hj))

/--
The step `j` of `hbmv` at element `i` of `y`, from its value `s`: with `t₁ = mul α x[j]`, it adds
`mul t₁ A[tbRow uplo k i j, j]` when `(i, j)` is in the band off the diagonal, and on the diagonal
it gives `s + mulr t₁ A[tbDiag uplo k, j].re + mul α (hbmvDot uplo k A x j)`, as `zhbmv`.
-/
@[expose] public def hbmvStep (uplo : Float64.Uplo) (k : Nat) (α : ComplexFloat)
    (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) (i : Nat) (s : ComplexFloat) :
    ComplexFloat :=
  if i = j then s + mulr (mul α x[j]) (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩).re +
    mul α (hbmvDot uplo k A x j hj)
  else if h : InTBand uplo k i j then
    s + mul (mul α x[j]) (A[(tbRow uplo k i j, j)]'⟨tbRow_lt uplo k i j h, hj⟩)
  else s

private theorem getElem_hbmvCol (uplo : Float64.Uplo) (k : Nat) (α : ComplexFloat)
    (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (hbmvCol uplo k α A x j hj y)[i] = hbmvStep uplo k α A x j hj i y[i] := by
  have hj' : ¬(tbLo uplo k j ≤ j ∧ j < tbLo uplo k j + tbLen uplo n k j) :=
    fun h => not_inTBand_self uplo k j ((mem_tb uplo n k j j hj).1 h)
  simp only [hbmvCol, hbmvStep, Vec.getElem_set, getElem_addColAt]
  by_cases e : i = j
  · subst e; simp only [hj', ↓reduceDIte, ↓reduceIte]
  · simp only [e, ↓reduceIte]
    by_cases h : InTBand uplo k i j
    · have hm := (mem_tb uplo n k i j hi).2 h
      simp only [hm, h, and_self, ↓reduceDIte]
      simp only [tbAr_add_sub uplo k i j h]
    · have hm : ¬(tbLo uplo k j ≤ i ∧ i < tbLo uplo k j + tbLen uplo n k j) :=
        fun h' => h ((mem_tb uplo n k i j hi).1 h')
      simp only [hm, h, ↓reduceDIte]

/--
`hbmv uplo α A x β y` is `α * A * x + β * y` for the Hermitian band matrix `A` with `k`
off-diagonals, stored in its upper or lower triangle, as `zhbmv`: it returns `y` when `n = 0`, or
`α = 0` and `β = 1`; it scales `y` by `β` (`betaScal`), returns when `α = 0`, and then runs the
steps `hbmvCol` for each column in increasing order. It reads only the real part of the diagonal.
-/
@[expose] public def hbmv (uplo : Float64.Uplo) {k : Nat} (α : ComplexFloat) (A : Mat (k + 1) n)
    (x : Vec n) (β : ComplexFloat) (y : Vec n) : Vec n :=
  if n = 0 then y
  else if isZero α && isOne β then y
  else
    let y := y.betaScal β
    if isZero α then y else Nat.fold n (fun j hj y => hbmvCol uplo k α A x j hj y) y

/--
Element `i` of `hbmv`: `betaMul β y[i]` when `α = 0`, and otherwise the fold of the steps
`hbmvStep` over the columns, from `betaMul β y[i]`.
-/
public theorem getElem_hbmv (uplo : Float64.Uplo) {k : Nat} (α : ComplexFloat)
    (A : Mat (k + 1) n) (x : Vec n) (β : ComplexFloat) (y : Vec n) (i : Nat) (h : i < n) :
    (hbmv uplo α A x β y)[i] =
      if isZero α then betaMul β y[i]
      else Nat.fold n (fun j hj s => hbmvStep uplo k α A x j hj i s) (betaMul β y[i]) := by
  unfold hbmv
  have hn : n ≠ 0 := by lia
  simp only [hn, ↓reduceIte]
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp [ha, hb]
  · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [Vec.getElem_fold_of_pointwise (fun j hj y => hbmvCol uplo k α A x j hj y)
      (fun j hj i _ s => hbmvStep uplo k α A x j hj i s)
      (fun j hj y i hi => getElem_hbmvCol uplo k α A x j hj y i hi) _ i h n (Nat.le_refl _),
      Vec.getElem_betaScal]

/-! ## `tbmv` -/

/--
The step of `tbmv` for column `j`: add `x[j]` times the band of column `j` off the diagonal, and
multiply `x[j]` by the diagonal element unless the diagonal is unit, as `ztbmv`.
-/
@[inline] public def tbmvCol (uplo : Float64.Uplo) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := x[j]
  let x := A.addColAt j hj (tbAr uplo k j) (tbLo uplo k j) (tbLen uplo n k j)
    (tbAr_add_tbLen ..) (tbLo_add_tbLen uplo n k j hj) t x
  x.set j hj (diagMul d x[j] (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩))

private theorem getElem_tbmvCol (uplo : Float64.Uplo) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (tbmvCol uplo d k A j hj y)[i] =
      if i = j then diagMul d y[j] (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩)
      else if h : InTBand uplo k i j then
        y[i] + mul y[j] (A[(tbRow uplo k i j, j)]'⟨tbRow_lt uplo k i j h, hj⟩)
      else y[i] := by
  have hj' : ¬(tbLo uplo k j ≤ j ∧ j < tbLo uplo k j + tbLen uplo n k j) :=
    fun h => not_inTBand_self uplo k j ((mem_tb uplo n k j j hj).1 h)
  simp only [tbmvCol, Vec.getElem_set, getElem_addColAt]
  by_cases e : i = j
  · subst e; simp only [hj', ↓reduceDIte, ↓reduceIte]
  · simp only [e, ↓reduceIte]
    by_cases h : InTBand uplo k i j
    · have hm := (mem_tb uplo n k i j hi).2 h
      simp only [hm, h, and_self, ↓reduceDIte]
      simp only [tbAr_add_sub uplo k i j h]
    · have hm : ¬(tbLo uplo k j ≤ i ∧ i < tbLo uplo k j + tbLen uplo n k j) :=
        fun h' => h ((mem_tb uplo n k i j hi).1 h')
      simp only [hm, h, ↓reduceDIte]

/--
`tbmv uplo d A x` is `A * x` for the triangular band matrix `A` with `k` off-diagonals, with a
unit diagonal if `d` is `.unit`, by the loops of `ztbmv`: the steps `tbmvCol` for
`j = 0, …, n - 1` for the upper triangle, and from `j = n - 1` down to `0` for the lower one.
-/
@[expose] public def tbmv (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun j hj x => tbmvCol .upper d k A j hj x) x
  | .lower => Nat.fold n (fun s hs x => tbmvCol .lower d k A (n - 1 - s) (by lia) x) x

private theorem getElem_tbmv_upper' (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n)
    (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tbmvCol .upper d k A j (by lia) x) x)[i] =
        if i < K then Nat.fold (min k (K - 1 - i)) (fun t _ s => s + mul (x.get0 (i + 1 + t))
          (A.bget0 (k - 1 - t) (i + 1 + t))) (diagMul d x[i] A[(k, i)])
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tbmvCol .upper d k A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      have hyK := hy K hK
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
      rw [getElem_tbmvCol, hyK, hy i hi]
      by_cases e : i = K
      · subst e
        rw [Nat.fold_congr (show min k (i + 1 - 1 - i) = 0 by lia)]
        simp [tbDiag]
      · simp only [e, ↓reduceIte]
        by_cases h : InTBand .upper k i K
        · have h' : i < K ∧ K ≤ i + k := by simpa [InTBand] using h
          simp only [h, ↓reduceDIte, h'.1, show i < K + 1 by lia, ↓reduceIte]
          rw [Nat.fold_congr (show min k (K + 1 - 1 - i) = min k (K - 1 - i) + 1 by grind),
            Nat.fold_succ]
          have e1 : i + 1 + min k (K - 1 - i) = K := by grind
          have e2 : k - 1 - min k (K - 1 - i) = k + i - K := by grind
          rw [e1, e2, vget0_eq x hK, bget0_eq A ⟨by lia, hK⟩]
          rfl
        · simp only [h, ↓reduceDIte]
          by_cases hl : i < K
          · have h' : K > i + k := by simp [InTBand] at h; lia
            simp only [hl, show i < K + 1 by lia, ↓reduceIte]
            rw [Nat.fold_congr (show min k (K + 1 - 1 - i) = min k (K - 1 - i) by grind)]
          · simp [hl, show ¬i < K + 1 by lia])

private theorem getElem_tbmv_lower' (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n)
    (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tbmvCol .lower d k A (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then Nat.fold (min k (i - (n - K))) (fun t _ s => s +
          mul (x.get0 (i - 1 - t)) (A.bget0 (1 + t) (i - 1 - t))) (diagMul d x[i] A[(0, i)])
        else x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tbmvCol .lower d k A (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      have hyK := hy (n - 1 - K) (by lia)
      simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
      rw [getElem_tbmvCol, hyK, hy i hi]
      by_cases e : i = n - 1 - K
      · subst e
        rw [Nat.fold_congr (show min k (n - 1 - K - (n - (K + 1))) = 0 by lia)]
        simp [tbDiag, show n - (K + 1) ≤ n - 1 - K by lia]
      · simp only [e, ↓reduceIte]
        by_cases h : InTBand .lower k i (n - 1 - K)
        · have h' : n - 1 - K < i ∧ i ≤ n - 1 - K + k := by simpa [InTBand] using h
          simp only [h, ↓reduceDIte, show n - K ≤ i by lia, show n - (K + 1) ≤ i by lia,
            ↓reduceIte]
          rw [Nat.fold_congr (show min k (i - (n - (K + 1))) = min k (i - (n - K)) + 1 by grind),
            Nat.fold_succ]
          have e1 : i - 1 - min k (i - (n - K)) = n - 1 - K := by grind
          have e2 : 1 + min k (i - (n - K)) = i - (n - 1 - K) := by grind
          rw [e1, e2, vget0_eq x (by lia), bget0_eq A ⟨by lia, by lia⟩]
          rfl
        · simp only [h, ↓reduceDIte]
          by_cases hl : n - K ≤ i
          · have h' : i > n - 1 - K + k := by simp [InTBand] at h; lia
            simp only [hl, show n - (K + 1) ≤ i by lia, ↓reduceIte]
            rw [Nat.fold_congr (show min k (i - (n - (K + 1))) = min k (i - (n - K)) by grind)]
          · have h2 : ¬n - (K + 1) ≤ i := by
              intro h2
              have : i = n - 1 - K := by lia
              exact e this
            simp [hl, h2])

/--
Element `i` of `tbmv .upper d A x` is `x[i]` times `A[k, i]` (unless the diagonal is unit), plus
the terms `mul x[j] A[k + i - j, j]` for `j = i + 1, …, min (i + k) (n - 1)`, in this order.
-/
public theorem getElem_tbmv_upper (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tbmv .upper d A x)[i] = Nat.fold (min k (n - 1 - i)) (fun t ht s =>
      s + mul (x[i + 1 + t]'(by grind)) (A[(k - 1 - t, i + 1 + t)]'⟨by lia, by grind⟩))
        (diagMul d x[i] A[(k, i)]) := by
  rw [tbmv, getElem_tbmv_upper' d k A x n (Nat.le_refl _) i hi, ite_eq_left hi]
  congr 1; funext t ht s
  rw [vget0_eq x (by grind), bget0_eq A ⟨by lia, by grind⟩]

/--
Element `i` of `tbmv .lower d A x` is `x[i]` times `A[0, i]` (unless the diagonal is unit), plus
the terms `mul x[j] A[i - j, j]` for `j = i - 1, …, i - min k i`, in this order.
-/
public theorem getElem_tbmv_lower (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tbmv .lower d A x)[i] = Nat.fold (min k i) (fun t ht s =>
      s + mul (x[i - 1 - t]'(by lia)) (A[(1 + t, i - 1 - t)]'⟨by grind, by lia⟩))
        (diagMul d x[i] A[(0, i)]) := by
  rw [tbmv, getElem_tbmv_lower' d k A x n (Nat.le_refl _) i hi, ite_eq_left (by lia),
    Nat.sub_self, Nat.sub_zero]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), bget0_eq A ⟨by grind, by lia⟩]


/-! ## `tbmvT` and `tbmvC` -/

/--
The step of `tbmvTWith p .upper` for column `j`: `x[j]` becomes `x[j]` times `p A[k, j]`, plus
`mul (p A[k + i - j, j]) x[i]` for `i = j - 1, …, j - min k j`.
-/
@[expose, specialize] public def tbmvTUpperCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (x : Vec n) :
    Vec n :=
  let t := Vec.accRev p (· + ·) (diagMul d x[j] (p (A[(k, j)]'⟨by lia, hj⟩)))
    ((A.col j hj).slice (tbAr .upper k j) (tbLen .upper n k j) (tbAr_add_tbLen ..))
    (x.slice (tbLo .upper k j) (tbLen .upper n k j) (tbLo_add_tbLen .upper n k j hj))
  x.set j hj t

/--
The step of `tbmvTWith p .lower` for column `j`: `x[j]` becomes `x[j]` times `p A[0, j]`, plus
`mul (p A[i - j, j]) x[i]` for `i = j + 1, …, j + min k (n - 1 - j)`.
-/
@[expose, specialize] public def tbmvTLowerCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (x : Vec n) :
    Vec n :=
  let t := Vec.acc p (· + ·) (diagMul d x[j] (p (A[(0, j)]'⟨by lia, hj⟩)))
    ((A.col j hj).slice (tbAr .lower k j) (tbLen .lower n k j) (tbAr_add_tbLen ..))
    (x.slice (tbLo .lower k j) (tbLen .lower n k j) (tbLo_add_tbLen .lower n k j hj))
  x.set j hj t

/--
`tbmvTWith p uplo d A x` is the product of `x` by the transpose of the triangular band matrix `A`,
with each element of `A` mapped by `p`, by the loops of `ztbmv`: from `j = n - 1` down to `0` for
the upper triangle, and for `j = 0, …, n - 1` for the lower one, it sets `x[j]` to `x[j]` times
`p` of the diagonal element (unless the diagonal is unit) plus the terms of the band of column
`j`, from the diagonal outwards.
-/
@[expose, specialize] public def tbmvTWith (p : ComplexFloat → ComplexFloat)
    (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun s hs x => tbmvTUpperCol p d k A (n - 1 - s) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => tbmvTLowerCol p d k A j hj x) x

private theorem getElem_tbmvT_upper' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tbmvTUpperCol p d k A (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then Nat.fold (min k i) (fun t _ s => s + mul (p (A.bget0 (k - 1 - t) i))
          (x.get0 (i - 1 - t))) (diagMul d x[i] (p A[(k, i)]))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tbmvTUpperCol p d k A (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      simp only [tbmvTUpperCol, Vec.getElem_set]
      by_cases e : i = n - 1 - K
      · subst e
        have hyK := hy (n - 1 - K) (by lia)
        simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
        simp only [↓reduceIte, show n - (K + 1) ≤ n - 1 - K by lia, Vec.accRev_eq, hyK,
          Vec.opC_add]
        rw [Nat.fold_congr (show tbLen .upper n k (n - 1 - K) = min k (n - 1 - K) by
          simp only [tbLen]; grind)]
        congr 1; funext t ht s
        have hl : tbLo .upper k (n - 1 - K) + (tbLen .upper n k (n - 1 - K) - 1 - t) =
            n - 1 - K - 1 - t := by simp only [tbLo, tbLen]; grind
        have hr : tbAr .upper k (n - 1 - K) + (tbLen .upper n k (n - 1 - K) - 1 - t) =
            k - 1 - t := by simp only [tbAr, tbLen]; grind
        have hyl := hy (n - 1 - K - 1 - t) (by grind)
        simp only [show ¬n - K ≤ n - 1 - K - 1 - t by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col]
        rw [Vec.getElem_eq_of_eq _ hl, hyl, mget_eq A hr rfl, vget0_eq x (by grind),
          bget0_eq A ⟨by lia, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : n - K ≤ i
        · simp [h, show n - (K + 1) ≤ i by lia]
        · simp [h, show ¬n - (K + 1) ≤ i by lia])

private theorem getElem_tbmvT_lower' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tbmvTLowerCol p d k A j (by lia) x) x)[i] =
        if i < K then Nat.fold (min k (n - 1 - i)) (fun t _ s => s +
          mul (p (A.bget0 (1 + t) i)) (x.get0 (i + 1 + t))) (diagMul d x[i] (p A[(0, i)]))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tbmvTLowerCol p d k A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      simp only [tbmvTLowerCol, Vec.getElem_set]
      by_cases e : i = K
      · subst e
        have hyK := hy i hK
        simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
        simp only [↓reduceIte, Nat.lt_add_one, Vec.acc_eq, hyK, Vec.opC_add]
        rw [Nat.fold_congr (show tbLen .lower n k i = min k (n - 1 - i) by
          simp only [tbLen]; grind)]
        congr 1; funext t ht s
        have hyl := hy (i + 1 + t) (by grind)
        simp only [show ¬i + 1 + t < i by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col, tbLo, tbAr]
        rw [Vec.getElem_eq_of_eq _ (show i + 1 + t = i + 1 + t from rfl), hyl,
          vget0_eq x (by grind), bget0_eq A ⟨by grind, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : i < K
        · simp [h, show i < K + 1 by lia]
        · simp [h, show ¬i < K + 1 by lia])

/--
Element `j` of `tbmvTWith p .upper d A x` is `x[j]` times `p A[k, j]` (unless the diagonal is
unit), plus the terms `mul (p A[k + i - j, j]) x[i]` for `i = j - 1, …, j - min k j`, in this
order.
-/
public theorem getElem_tbmvTWith_upper (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) :
    (tbmvTWith p .upper d A x)[j] = Nat.fold (min k j) (fun t _ht s =>
      s + mul (p (A[(k - 1 - t, j)]'⟨by lia, hj⟩)) (x[j - 1 - t]'(by grind)))
        (diagMul d x[j] (p A[(k, j)])) := by
  rw [tbmvTWith, getElem_tbmvT_upper' p d k A x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]
  congr 1; funext t ht s
  rw [vget0_eq x (by grind), bget0_eq A ⟨by lia, hj⟩]

/--
Element `j` of `tbmvTWith p .lower d A x` is `x[j]` times `p A[0, j]` (unless the diagonal is
unit), plus the terms `mul (p A[i - j, j]) x[i]` for `i = j + 1, …, j + min k (n - 1 - j)`, in
this order.
-/
public theorem getElem_tbmvTWith_lower (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) :
    (tbmvTWith p .lower d A x)[j] = Nat.fold (min k (n - 1 - j)) (fun t ht s =>
      s + mul (p (A[(1 + t, j)]'⟨by grind, hj⟩)) (x[j + 1 + t]'(by grind)))
        (diagMul d x[j] (p A[(0, j)])) := by
  rw [tbmvTWith, getElem_tbmvT_lower' p d k A x n (Nat.le_refl _) j hj, ite_eq_left hj]
  congr 1; funext t ht s
  rw [vget0_eq x (by grind), bget0_eq A ⟨by grind, hj⟩]

/-- `tbmvT uplo d A x` is `Aᵀ * x` for the triangular band matrix `A`, as `ztbmv` with `'T'`. -/
@[expose] public def tbmvT (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : Vec n :=
  tbmvTWith id uplo d A x

/-- `tbmvC uplo d A x` is `Aᴴ * x` for the triangular band matrix `A`, as `ztbmv` with `'C'`. -/
@[expose] public def tbmvC (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : Vec n :=
  tbmvTWith ComplexFloat.conj uplo d A x

/-! ## `tbsv` -/

/--
Element `i` of the solution of `A * y = x` for the lower triangular band matrix `A`: `x[i]`, minus
the terms `mul y[j] A[i - j, j]` for `j = i - min k i, …, i - 1`, divided by `A[0, i]` unless the
diagonal is unit.
-/
@[expose] public def tbsvLowerM (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (min k i) (fun t _ht s => s - mul (tbsvLowerM d k A x (i - min k i + t))
    (A.bget0 (min k i - t) (i - min k i + t))) (x.get0 i)) (A.bget0 0 i)
termination_by i
decreasing_by grind

/--
Element `i` of the solution of `A * y = x` for the upper triangular band matrix `A`: `x[i]`, minus
the terms `mul y[j] A[k + i - j, j]` for `j = i + min k (n - 1 - i), …, i + 1`, divided by
`A[k, i]` unless the diagonal is unit.
-/
@[expose] public def tbsvUpperM (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (min k (n - 1 - i)) (fun t _ht s =>
      s - mul (tbsvUpperM d k A x (i + min k (n - 1 - i) - t))
        (A.bget0 (k - min k (n - 1 - i) + t) (i + min k (n - 1 - i) - t))) (x.get0 i))
    (A.bget0 k i)
termination_by n - i
decreasing_by grind

/--
The step of `tbsv` for column `j`: divide `x[j]` by the diagonal element unless the diagonal is
unit, and subtract `x[j]` times the band of column `j` off the diagonal, as `ztbsv`.
-/
@[inline] public def tbsvCol (uplo : Float64.Uplo) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d x[j] (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩)
  let x := x.set j hj t
  A.subColAt j hj (tbAr uplo k j) (tbLo uplo k j) (tbLen uplo n k j)
    (tbAr_add_tbLen ..) (tbLo_add_tbLen uplo n k j hj) t x

private theorem getElem_tbsvCol (uplo : Float64.Uplo) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (tbsvCol uplo d k A j hj y)[i] =
      if i = j then diagDiv d y[j] (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩)
      else if h : InTBand uplo k i j then
        y[i] - mul (diagDiv d y[j] (A[(tbDiag uplo k, j)]'⟨tbDiag_lt .., hj⟩))
          (A[(tbRow uplo k i j, j)]'⟨tbRow_lt uplo k i j h, hj⟩)
      else y[i] := by
  have hj' : ¬(tbLo uplo k j ≤ j ∧ j < tbLo uplo k j + tbLen uplo n k j) :=
    fun h => not_inTBand_self uplo k j ((mem_tb uplo n k j j hj).1 h)
  simp only [tbsvCol, getElem_subColAt, Vec.getElem_set]
  by_cases e : i = j
  · subst e; simp only [hj', ↓reduceDIte, ↓reduceIte]
  · simp only [e, ↓reduceIte]
    by_cases h : InTBand uplo k i j
    · have hm := (mem_tb uplo n k i j hi).2 h
      simp only [hm, h, and_self, ↓reduceDIte]
      simp only [tbAr_add_sub uplo k i j h]
    · have hm : ¬(tbLo uplo k j ≤ i ∧ i < tbLo uplo k j + tbLen uplo n k j) :=
        fun h' => h ((mem_tb uplo n k i j hi).1 h')
      simp only [hm, h, ↓reduceDIte]

/--
`tbsv uplo d A x` solves `A * y = x` for the triangular band matrix `A` with `k` off-diagonals,
with a unit diagonal if `d` is `.unit`, by the loops of `ztbsv`: the steps `tbsvCol` from
`j = n - 1` down to `0` for the upper triangle, and for `j = 0, …, n - 1` for the lower one. Like
the reference BLAS, it doesn't check for a zero on the diagonal.
-/
@[expose] public def tbsv (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun s hs x => tbsvCol .upper d k A (n - 1 - s) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => tbsvCol .lower d k A j hj x) x

private theorem tbsvLowerM_eq (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    {i : Nat} (hi : i < n) :
    tbsvLowerM d k A x i = diagDiv d (Nat.fold (min k i) (fun t _ s =>
      s - mul (tbsvLowerM d k A x (i - min k i + t)) (A.bget0 (min k i - t) (i - min k i + t)))
        x[i]) A[(0, i)] := by
  rw [tbsvLowerM, vget0_eq x hi, bget0_eq A ⟨by lia, hi⟩]

private theorem tbsvUpperM_eq (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    {i : Nat} (hi : i < n) :
    tbsvUpperM d k A x i = diagDiv d (Nat.fold (min k (n - 1 - i)) (fun t _ s =>
      s - mul (tbsvUpperM d k A x (i + min k (n - 1 - i) - t))
        (A.bget0 (k - min k (n - 1 - i) + t) (i + min k (n - 1 - i) - t))) x[i]) A[(k, i)] := by
  rw [tbsvUpperM, vget0_eq x hi, bget0_eq A ⟨by lia, hi⟩]

private theorem getElem_tbsv_lower' (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n)
    (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tbsvCol .lower d k A j (by lia) x) x)[i] =
        if i < K then tbsvLowerM d k A x i
        else Nat.fold (K - (i - min k i)) (fun t _ s => s - mul (tbsvLowerM d k A x
          (i - min k i + t)) (A.bget0 (min k i - t) (i - min k i + t))) x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tbsvCol .lower d k A j (by lia) x) _ x
    (fun i hi => by
      simp only [Nat.not_lt_zero, ↓reduceIte]
      rw [Nat.fold_congr (Nat.zero_sub _), Nat.fold_zero]) (by
      intro K hK y hy i hi
      have hyK := hy K hK
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
      have ht : diagDiv d y[K] (A[(tbDiag .lower k, K)]'⟨tbDiag_lt .lower k, hK⟩) =
          tbsvLowerM d k A x K := by
        rw [hyK, tbsvLowerM_eq d k A x hK,
          Nat.fold_congr (show K - (K - min k K) = min k K by grind)]
        rfl
      rw [getElem_tbsvCol, ht, hy i hi]
      by_cases e : i = K
      · subst e; simp
      · simp only [e, ↓reduceIte]
        by_cases h : InTBand .lower k i K
        · have h' : K < i ∧ i ≤ K + k := by simpa [InTBand] using h
          simp only [h, ↓reduceDIte, show ¬i < K by lia, show ¬i < K + 1 by lia, ↓reduceIte]
          rw [Nat.fold_congr (show K + 1 - (i - min k i) = K - (i - min k i) + 1 by grind),
            Nat.fold_succ]
          have e1 : i - min k i + (K - (i - min k i)) = K := by grind
          have e2 : min k i - (K - (i - min k i)) = i - K := by grind
          rw [e1, e2, bget0_eq A ⟨by grind, hK⟩]
          rfl
        · simp only [h, ↓reduceDIte]
          by_cases hl : i < K
          · simp [hl, show i < K + 1 by lia]
          · have h' : i > K + k := by simp [InTBand] at h; lia
            simp only [hl, show ¬i < K + 1 by lia, ↓reduceIte]
            rw [Nat.fold_congr (show K + 1 - (i - min k i) = K - (i - min k i) by grind)])

private theorem getElem_tbsv_upper' (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n)
    (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tbsvCol .upper d k A (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then tbsvUpperM d k A x i
        else Nat.fold (i + min k (n - 1 - i) + 1 - (n - K)) (fun t _ s =>
          s - mul (tbsvUpperM d k A x (i + min k (n - 1 - i) - t))
            (A.bget0 (k - min k (n - 1 - i) + t) (i + min k (n - 1 - i) - t))) x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tbsvCol .upper d k A (n - 1 - s) (by lia) x) _ x
    (fun i hi => by
      simp only [Nat.sub_zero, show ¬n ≤ i by lia, ↓reduceIte]
      rw [Nat.fold_congr (show i + min k (n - 1 - i) + 1 - n = 0 by grind), Nat.fold_zero]) (by
      intro K hK y hy i hi
      have hyK := hy (n - 1 - K) (by lia)
      simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
      have ht : diagDiv d y[n - 1 - K]
          (A[(tbDiag .upper k, n - 1 - K)]'⟨tbDiag_lt .upper k, by lia⟩) =
          tbsvUpperM d k A x (n - 1 - K) := by
        rw [hyK, tbsvUpperM_eq d k A x (by lia),
          Nat.fold_congr (show n - 1 - K + min k (n - 1 - (n - 1 - K)) + 1 - (n - K) =
            min k (n - 1 - (n - 1 - K)) by grind)]
        rfl
      rw [getElem_tbsvCol, ht, hy i hi]
      by_cases e : i = n - 1 - K
      · subst e; simp [show n - (K + 1) ≤ n - 1 - K by lia]
      · simp only [e, ↓reduceIte]
        by_cases h : InTBand .upper k i (n - 1 - K)
        · have h' : i < n - 1 - K ∧ n - 1 - K ≤ i + k := by simpa [InTBand] using h
          simp only [h, ↓reduceDIte, show ¬n - K ≤ i by lia, show ¬n - (K + 1) ≤ i by lia,
            ↓reduceIte]
          rw [Nat.fold_congr (show i + min k (n - 1 - i) + 1 - (n - (K + 1)) =
            i + min k (n - 1 - i) + 1 - (n - K) + 1 by grind), Nat.fold_succ]
          have e1 : i + min k (n - 1 - i) - (i + min k (n - 1 - i) + 1 - (n - K)) =
              n - 1 - K := by grind
          have e2 : k - min k (n - 1 - i) + (i + min k (n - 1 - i) + 1 - (n - K)) =
              k + i - (n - 1 - K) := by grind
          rw [e1, e2, bget0_eq A ⟨by grind, by lia⟩]
          rfl
        · simp only [h, ↓reduceDIte]
          by_cases hl : n - K ≤ i
          · simp [hl, show n - (K + 1) ≤ i by lia]
          · have h2 : ¬n - (K + 1) ≤ i := by
              intro h2
              have : i = n - 1 - K := by lia
              exact e this
            have h' : n - 1 - K > i + k := by simp [InTBand] at h; lia
            simp only [hl, h2, ↓reduceIte]
            rw [Nat.fold_congr (show i + min k (n - 1 - i) + 1 - (n - (K + 1)) =
              i + min k (n - 1 - i) + 1 - (n - K) by grind)])

/-- Element `i` of `tbsv .lower d A x` is element `i` of the model `tbsvLowerM`. -/
public theorem getElem_tbsv_lower_eq (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (hi : i < n) : (tbsv .lower d A x)[i] = tbsvLowerM d k A x i := by
  rw [tbsv, getElem_tbsv_lower' d k A x n (Nat.le_refl _) i hi, ite_eq_left hi]

/-- Element `i` of `tbsv .upper d A x` is element `i` of the model `tbsvUpperM`. -/
public theorem getElem_tbsv_upper_eq (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (hi : i < n) : (tbsv .upper d A x)[i] = tbsvUpperM d k A x i := by
  rw [tbsv, getElem_tbsv_upper' d k A x n (Nat.le_refl _) i hi, ite_eq_left (by lia)]

/--
Element `i` of `y = tbsv .lower d A x` is `x[i]`, minus the terms `mul y[j] A[i - j, j]` for
`j = i - min k i, …, i - 1`, divided by `A[0, i]` unless the diagonal is unit: forward
substitution, in the order of the loops.
-/
public theorem getElem_tbsv_lower (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tbsv .lower d A x)[i] = diagDiv d (Nat.fold (min k i) (fun t ht s =>
      s - mul ((tbsv .lower d A x)[i - min k i + t]'(by grind))
        (A[(min k i - t, i - min k i + t)]'⟨by grind, by grind⟩)) x[i]) A[(0, i)] := by
  rw [getElem_tbsv_lower_eq d A x i hi, tbsvLowerM_eq d k A x hi]
  congr 1; congr 1; funext t ht s
  rw [getElem_tbsv_lower_eq d A x _ (by grind), bget0_eq A ⟨by grind, by grind⟩]

/--
Element `i` of `y = tbsv .upper d A x` is `x[i]`, minus the terms `mul y[j] A[k + i - j, j]` for
`j = i + min k (n - 1 - i), …, i + 1`, divided by `A[k, i]` unless the diagonal is unit: back
substitution, in the order of the loops.
-/
public theorem getElem_tbsv_upper (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tbsv .upper d A x)[i] = diagDiv d (Nat.fold (min k (n - 1 - i)) (fun t ht s =>
      s - mul ((tbsv .upper d A x)[i + min k (n - 1 - i) - t]'(by grind))
        (A[(k - min k (n - 1 - i) + t, i + min k (n - 1 - i) - t)]'⟨by grind, by grind⟩))
          x[i]) A[(k, i)] := by
  rw [getElem_tbsv_upper_eq d A x i hi, tbsvUpperM_eq d k A x hi]
  congr 1; congr 1; funext t ht s
  rw [getElem_tbsv_upper_eq d A x _ (by grind), bget0_eq A ⟨by grind, by grind⟩]

/-! ## `tbsvT` and `tbsvC` -/

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the upper triangular band matrix `A`: `x[j]`,
minus the terms `mul (p A[k + i - j, j]) y[i]` for `i = j - min k j, …, j - 1`, divided by
`p A[k, j]` unless the diagonal is unit.
-/
@[expose] public def tbsvTUpperM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (x : Vec n) (j : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (min k j) (fun t _ht s => s - mul (p (A.bget0 (k - min k j + t) j))
    (tbsvTUpperM p d k A x (j - min k j + t))) (x.get0 j)) (p (A.bget0 k j))
termination_by j
decreasing_by grind

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the lower triangular band matrix `A`: `x[j]`,
minus the terms `mul (p A[i - j, j]) y[i]` for `i = j + min k (n - 1 - j), …, j + 1`, divided by
`p A[0, j]` unless the diagonal is unit.
-/
@[expose] public def tbsvTLowerM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (x : Vec n) (j : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (min k (n - 1 - j)) (fun t _ht s =>
      s - mul (p (A.bget0 (min k (n - 1 - j) - t) j))
        (tbsvTLowerM p d k A x (j + min k (n - 1 - j) - t))) (x.get0 j)) (p (A.bget0 0 j))
termination_by n - j
decreasing_by grind

/-- The step of `tbsvTWith p .upper` for column `j`: solve for `x[j]` from the band above. -/
@[expose, specialize] public def tbsvTUpperCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (x : Vec n) :
    Vec n :=
  let t := diagDiv d (Vec.acc p (· - ·) x[j]
    ((A.col j hj).slice (tbAr .upper k j) (tbLen .upper n k j) (tbAr_add_tbLen ..))
    (x.slice (tbLo .upper k j) (tbLen .upper n k j) (tbLo_add_tbLen .upper n k j hj)))
    (p (A[(k, j)]'⟨by lia, hj⟩))
  x.set j hj t

/-- The step of `tbsvTWith p .lower` for column `j`: solve for `x[j]` from the band below. -/
@[expose, specialize] public def tbsvTLowerCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (hj : j < n) (x : Vec n) :
    Vec n :=
  let t := diagDiv d (Vec.accRev p (· - ·) x[j]
    ((A.col j hj).slice (tbAr .lower k j) (tbLen .lower n k j) (tbAr_add_tbLen ..))
    (x.slice (tbLo .lower k j) (tbLen .lower n k j) (tbLo_add_tbLen .lower n k j hj)))
    (p (A[(0, j)]'⟨by lia, hj⟩))
  x.set j hj t

/--
`tbsvTWith p uplo d A x` solves `(p A)ᵀ * y = x` for the triangular band matrix `A`, where `p A`
maps each element of `A` by `p`, by the loops of `ztbsv`: for `j = 0, …, n - 1` for the upper
triangle, and from `j = n - 1` down to `0` for the lower one, it subtracts the terms of the band
of column `j` from `x[j]`, from the far end inwards, and divides it by `p` of the diagonal element
(`div`) unless the diagonal is unit.
-/
@[expose, specialize] public def tbsvTWith (p : ComplexFloat → ComplexFloat)
    (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun j hj x => tbsvTUpperCol p d k A j hj x) x
  | .lower => Nat.fold n (fun s hs x => tbsvTLowerCol p d k A (n - 1 - s) (by lia) x) x

private theorem tbsvTUpperM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (x : Vec n) {j : Nat} (hj : j < n) :
    tbsvTUpperM p d k A x j = diagDiv d (Nat.fold (min k j) (fun t _ s =>
      s - mul (p (A.bget0 (k - min k j + t) j)) (tbsvTUpperM p d k A x (j - min k j + t))) x[j])
        (p A[(k, j)]) := by
  rw [tbsvTUpperM, vget0_eq x hj, bget0_eq A ⟨by lia, hj⟩]

private theorem tbsvTLowerM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (k : Nat)
    (A : Mat (k + 1) n) (x : Vec n) {j : Nat} (hj : j < n) :
    tbsvTLowerM p d k A x j = diagDiv d (Nat.fold (min k (n - 1 - j)) (fun t _ s =>
      s - mul (p (A.bget0 (min k (n - 1 - j) - t) j))
        (tbsvTLowerM p d k A x (j + min k (n - 1 - j) - t))) x[j]) (p A[(0, j)]) := by
  rw [tbsvTLowerM, vget0_eq x hj, bget0_eq A ⟨by lia, hj⟩]

private theorem getElem_tbsvT_upper' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tbsvTUpperCol p d k A j (by lia) x) x)[i] =
        if i < K then tbsvTUpperM p d k A x i else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tbsvTUpperCol p d k A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      simp only [tbsvTUpperCol, Vec.getElem_set]
      by_cases e : i = K
      · subst e
        have hyK := hy i hK
        simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
        simp only [↓reduceIte, Nat.lt_add_one, Vec.acc_eq, hyK, Vec.opC_sub,
          tbsvTUpperM_eq p d k A x hK]
        rw [Nat.fold_congr (show tbLen .upper n k i = min k i by simp only [tbLen]; grind)]
        congr 1; congr 1; funext t ht s
        have hl : tbLo .upper k i + t = i - min k i + t := by simp only [tbLo]; grind
        have hr : tbAr .upper k i + t = k - min k i + t := by simp only [tbAr]; grind
        have hyl := hy (i - min k i + t) (by grind)
        simp only [show i - min k i + t < i by grind, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col]
        rw [Vec.getElem_eq_of_eq _ hl, hyl, mget_eq A hr rfl, bget0_eq A ⟨by grind, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : i < K
        · simp [h, show i < K + 1 by lia]
        · simp [h, show ¬i < K + 1 by lia])

private theorem getElem_tbsvT_lower' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tbsvTLowerCol p d k A (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then tbsvTLowerM p d k A x i else x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tbsvTLowerCol p d k A (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      simp only [tbsvTLowerCol, Vec.getElem_set]
      by_cases e : i = n - 1 - K
      · subst e
        have hyK := hy (n - 1 - K) (by lia)
        simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
        simp only [↓reduceIte, show n - (K + 1) ≤ n - 1 - K by lia, Vec.accRev_eq, hyK,
          Vec.opC_sub, tbsvTLowerM_eq p d k A x hi]
        rw [Nat.fold_congr (show tbLen .lower n k (n - 1 - K) = min k (n - 1 - (n - 1 - K)) by
          simp only [tbLen]; grind)]
        congr 1; congr 1; funext t ht s
        have hl : tbLo .lower k (n - 1 - K) + (tbLen .lower n k (n - 1 - K) - 1 - t) =
            n - 1 - K + min k (n - 1 - (n - 1 - K)) - t := by simp only [tbLo, tbLen]; grind
        have hr : tbAr .lower k (n - 1 - K) + (tbLen .lower n k (n - 1 - K) - 1 - t) =
            min k (n - 1 - (n - 1 - K)) - t := by simp only [tbAr, tbLen]; grind
        have hyl := hy (n - 1 - K + min k (n - 1 - (n - 1 - K)) - t) (by grind)
        simp only [show n - K ≤ n - 1 - K + min k (n - 1 - (n - 1 - K)) - t by grind,
          ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col]
        rw [Vec.getElem_eq_of_eq _ hl, hyl, mget_eq A hr rfl, bget0_eq A ⟨by grind, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : n - K ≤ i
        · simp [h, show n - (K + 1) ≤ i by lia]
        · simp [h, show ¬n - (K + 1) ≤ i by lia])

/-- Element `j` of `tbsvTWith p .upper d A x` is element `j` of the model `tbsvTUpperM`. -/
public theorem getElem_tbsvTWith_upper_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) :
    (tbsvTWith p .upper d A x)[j] = tbsvTUpperM p d k A x j := by
  rw [tbsvTWith, getElem_tbsvT_upper' p d k A x n (Nat.le_refl _) j hj, ite_eq_left hj]

/-- Element `j` of `tbsvTWith p .lower d A x` is element `j` of the model `tbsvTLowerM`. -/
public theorem getElem_tbsvTWith_lower_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) :
    (tbsvTWith p .lower d A x)[j] = tbsvTLowerM p d k A x j := by
  rw [tbsvTWith, getElem_tbsvT_lower' p d k A x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]

/--
Element `j` of `y = tbsvTWith p .upper d A x` is `x[j]`, minus the terms
`mul (p A[k + i - j, j]) y[i]` for `i = j - min k j, …, j - 1`, divided by `p A[k, j]` unless the
diagonal is unit.
-/
public theorem getElem_tbsvTWith_upper (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) :
    (tbsvTWith p .upper d A x)[j] = diagDiv d (Nat.fold (min k j) (fun t ht s =>
      s - mul (p (A[(k - min k j + t, j)]'⟨by grind, hj⟩))
        ((tbsvTWith p .upper d A x)[j - min k j + t]'(by grind))) x[j]) (p A[(k, j)]) := by
  rw [getElem_tbsvTWith_upper_eq p d A x j hj, tbsvTUpperM_eq p d k A x hj]
  congr 1; congr 1; funext t ht s
  rw [getElem_tbsvTWith_upper_eq p d A x _ (by grind), bget0_eq A ⟨by grind, hj⟩]

/--
Element `j` of `y = tbsvTWith p .lower d A x` is `x[j]`, minus the terms
`mul (p A[i - j, j]) y[i]` for `i = j + min k (n - 1 - j), …, j + 1`, divided by `p A[0, j]`
unless the diagonal is unit.
-/
public theorem getElem_tbsvTWith_lower (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat) (hj : j < n) :
    (tbsvTWith p .lower d A x)[j] = diagDiv d (Nat.fold (min k (n - 1 - j)) (fun t ht s =>
      s - mul (p (A[(min k (n - 1 - j) - t, j)]'⟨by grind, hj⟩))
        ((tbsvTWith p .lower d A x)[j + min k (n - 1 - j) - t]'(by grind))) x[j])
          (p A[(0, j)]) := by
  rw [getElem_tbsvTWith_lower_eq p d A x j hj, tbsvTLowerM_eq p d k A x hj]
  congr 1; congr 1; funext t ht s
  rw [getElem_tbsvTWith_lower_eq p d A x _ (by grind), bget0_eq A ⟨by grind, hj⟩]

/-- `tbsvT uplo d A x` solves `Aᵀ * y = x` for the triangular band matrix `A` (`ztbsv`, `'T'`). -/
@[expose] public def tbsvT (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : Vec n :=
  tbsvTWith id uplo d A x

/-- `tbsvC uplo d A x` solves `Aᴴ * y = x` for the triangular band matrix `A` (`ztbsv`, `'C'`). -/
@[expose] public def tbsvC (uplo : Float64.Uplo) (d : Float64.Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : Vec n :=
  tbsvTWith ComplexFloat.conj uplo d A x

end Mat

end BLAS.ComplexFloat64
