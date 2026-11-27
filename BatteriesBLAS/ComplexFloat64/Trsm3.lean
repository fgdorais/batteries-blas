/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Trmm3

/-!
# Complex triangular solve, Level 3

`trsm` (`B := α * A⁻¹ * B`), `trsmT` (`B := α * A⁻ᵀ * B`) and `trsmC` (`B := α * A⁻ᴴ * B`), and
`trsmRight` (`B := α * B * A⁻¹`), `trsmRightT` (`B := α * B * A⁻ᵀ`) and `trsmRightC`
(`B := α * B * A⁻ᴴ`), for the upper or the lower triangle of `A`, with a unit diagonal or not, as
`ztrsm` in the reference BLAS (`master`, without the zero skips and the `α = 1` skips of LAPACK
3.12), with the same operations in the same order. Like the reference BLAS, they don't check for a
zero on the diagonal.

On the left, each column of `B` is solved for apart from the others: `trsm` solves each column,
scaled by `α`, by `trsv`, and `trsmT` and `trsmC` by `trsvTAscWith`, which runs the loops of
`ztrsv` for the upper triangle and the loops of `ztrsm`, with the terms in increasing order, for
the lower one. On the right, each row of `B` is solved for apart from the others, but the loops
of `ztrsm` run over the columns, as here: each element `(i, j)` of `trsmRight` is element `j` of
the solution of a transposed system for row `i` (`trsvTAscWith id`), and each element of
`trsmRightT` and `trsmRightC` is `α` times element `j` of the solution of a system for row `i` by
`trsvLWith`, which multiplies by the element of `A` on the left as `ztrsm` does.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.ComplexFloat64

namespace Mat

variable {m n : Nat}

/-! ## Updates of a vector by columns -/

/-- `v` minus `mul t C[i, k]` at each element `i`, in place. -/
@[inline] public def subColOf (C : Mat m n) (k : Nat) (hk : k < n) (t : ComplexFloat)
    (v : Vec m) : Vec m :=
  v.withSlice 0 m (by lia)
    (fun s => Vec.zipWithData (fun v a => v.re - mulRe t a) (fun v a => v.im - mulIm t a)
      ((C.col k hk).slice 0 m (by lia)) s)
    (fun s => by rw [Vec.size_zipWithData])

public theorem getElem_subColOf (C : Mat m n) (k : Nat) (hk : k < n) (t : ComplexFloat)
    (v : Vec m) (i : Nat) (hi : i < m) :
    (C.subColOf k hk t v)[i] = v[i] - mul t C[(i, k)] := by
  unfold subColOf
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  simp only [Nat.zero_le, Nat.zero_add, hi, and_self, ↓reduceIte, Nat.sub_zero, Vec.get0,
    ↓reduceDIte, Vec.getElem_slice, getElem_col, mulRe_eq, mulIm_eq]
  rfl

/--
`y` with `mul (p A[i, j]) t` subtracted from the elements `lo ≤ i < lo + len`, in place: the
element of `A` multiplies on the left, as in `ztrsm`.
-/
@[inline] public def subColL (p : ComplexFloat → ComplexFloat) (A : Mat n n) (j : Nat)
    (hj : j < n) (lo len : Nat) (h : lo + len ≤ n) (t : ComplexFloat) (y : Vec n) : Vec n :=
  y.withSlice lo len h
    (fun s => Vec.zipWithData (fun v a => v.re - mulRe (p a) t) (fun v a => v.im - mulIm (p a) t)
      ((A.col j hj).slice lo len h) s)
    (fun s => by rw [Vec.size_zipWithData])

public theorem getElem_subColL (p : ComplexFloat → ComplexFloat) (A : Mat n n) (j : Nat)
    (hj : j < n) (lo len : Nat) (h : lo + len ≤ n) (t : ComplexFloat) (y : Vec n) (i : Nat)
    (hi : i < n) :
    (subColL p A j hj lo len h t y)[i] =
      if lo ≤ i ∧ i < lo + len then y[i] - mul (p A[(i, j)]) t else y[i] := by
  unfold subColL
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  split
  · simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col,
      mulRe_eq, mulIm_eq]
    have e : lo + (i - lo) = i := by lia
    simp only [e]
    rfl
  · rfl

/-! ## `trsvTLowerAsc`: the transposed lower solve, with the terms in increasing order -/

/--
The step of `trsvTLowerAsc p` for column `j`: solve for `x[j]` from the elements below, with the
terms `mul (p A[i, j]) x[i]` for `i = j + 1, …, n - 1`, in this order.
-/
@[expose, specialize] public def trsvTLowerAscCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d (Vec.acc p (· - ·) x[j]
    ((A.col j hj).slice (j + 1) (n - (j + 1)) (by lia)) (x.slice (j + 1) (n - (j + 1)) (by lia)))
    (p A[(j, j)])
  x.set j hj t

/--
`trsvTLowerAsc p d A x` solves `(p A)ᵀ * y = x` for the lower triangle of `A`, from `j = n - 1`
down to `0`, as `trsvTWith p .lower`, but with the terms of each element in increasing order, as
in `ztrsm` with `SIDE = 'L'` and `TRANSA = 'T'` or `'C'`.
-/
@[expose, specialize] public def trsvTLowerAsc (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (A : Mat n n) (x : Vec n) : Vec n :=
  Nat.fold n (fun k hk x => trsvTLowerAscCol p d A (n - 1 - k) (by lia) x) x

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the lower triangle of `A`: `x[j]`, minus the
terms `mul (p A[l, j]) y[l]` for `l = j + 1, …, n - 1`, divided by `p A[j, j]` unless the
diagonal is unit.
-/
@[expose] public def trsvTLowerAscM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (A.get0 (j + 1 + t) j)) (trsvTLowerAscM p d A x (j + 1 + t))) (x.get0 j))
    (p (A.get0 j j))
termination_by n - j
decreasing_by lia

private theorem vget0_eq' (x : Vec n) {i : Nat} (h : i < n) : x.get0 i = x[i] := by
  simp [Vec.get0, h]

private theorem trsvTLowerAscM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) {j : Nat} (hj : j < n) :
    trsvTLowerAscM p d A x j = diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (A.get0 (j + 1 + t) j)) (trsvTLowerAscM p d A x (j + 1 + t))) x[j])
      (p A[(j, j)]) := by
  rw [trsvTLowerAscM, vget0_eq' x hj, get0_eq A ⟨hj, hj⟩]

/-- The steps of `trsvTLowerAsc` change only the element they solve for. -/
private theorem getElem_trsvTLowerAscCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (trsvTLowerAscCol p d A j hj y)[i] =
      if i = j then diagDiv d (Vec.acc p (· - ·) y[j]
        ((A.col j hj).slice (j + 1) (n - (j + 1)) (by lia))
        (y.slice (j + 1) (n - (j + 1)) (by lia))) (p A[(j, j)])
      else y[i] := by
  simp only [trsvTLowerAscCol, Vec.getElem_set]

private theorem getElem_trsvTLowerAsc' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvTLowerAscCol p d A (n - 1 - j) (by lia) x) x)[i] =
        if n - k ≤ i then trsvTLowerAscM p d A x i else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvTLowerAscCol p d A (n - 1 - j) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro k hk y hy i hi
      rw [getElem_trsvTLowerAscCol]
      by_cases e : i = n - 1 - k
      · subst e
        have hyk := hy (n - 1 - k) (by lia)
        simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hyk
        simp only [↓reduceIte, show n - (k + 1) ≤ n - 1 - k by lia, Vec.acc_eq, hyk,
          Vec.opC_sub, trsvTLowerAscM_eq p d A x hi]
        rw [Nat.fold_congr (show n - (n - 1 - k + 1) = n - 1 - (n - 1 - k) by lia)]
        congr 1; congr 1; funext t ht s
        have hyl := hy (n - 1 - k + 1 + t) (by lia)
        simp only [show n - k ≤ n - 1 - k + 1 + t by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col, hyl,
          get0_eq A (i := n - 1 - k + 1 + t) (j := n - 1 - k) ⟨by lia, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : n - k ≤ i
        · simp [h, show n - (k + 1) ≤ i by lia]
        · simp [h, show ¬n - (k + 1) ≤ i by lia])

/-- Element `j` of `trsvTLowerAsc p d A x` is element `j` of the model `trsvTLowerAscM`. -/
public theorem getElem_trsvTLowerAsc_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trsvTLowerAsc p d A x)[j] = trsvTLowerAscM p d A x j := by
  rw [trsvTLowerAsc, getElem_trsvTLowerAsc' p d A x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]

/--
Element `j` of `y = trsvTLowerAsc p d A x` is `x[j]`, minus the terms `mul (p A[l, j]) y[l]` for
`l = j + 1, …, n - 1`, divided by `p A[j, j]` unless the diagonal is unit.
-/
public theorem getElem_trsvTLowerAsc (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trsvTLowerAsc p d A x)[j] = diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (A[(j + 1 + t, j)]'⟨by lia, hj⟩))
        ((trsvTLowerAsc p d A x)[j + 1 + t]'(by lia))) x[j]) (p A[(j, j)]) := by
  rw [getElem_trsvTLowerAsc_eq p d A x j hj, trsvTLowerAscM_eq p d A x hj]
  congr 1; congr 1; funext t ht s
  rw [getElem_trsvTLowerAsc_eq p d A x (j + 1 + t) (by lia),
    get0_eq A (i := j + 1 + t) (j := j) ⟨by lia, hj⟩]

/--
`trsvTAscWith p uplo d A x` solves `(p A)ᵀ * y = x` for the triangle `uplo` of `A` by the loops
of `ztrsm` with `SIDE = 'L'` and `TRANSA = 'T'` or `'C'`: `trsvTWith p .upper` for the upper
triangle, whose terms are in increasing order, and `trsvTLowerAsc p` for the lower one.
-/
@[expose, specialize] public def trsvTAscWith (p : ComplexFloat → ComplexFloat)
    (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => trsvTWith p .upper d A x
  | .lower => trsvTLowerAsc p d A x

/-! ## `trsvLWith`: the solve with the elements of `A` on the left -/

/--
The step of `trsvLWith p .upper` for column `j`: `x[j]` is divided by `p A[j, j]` (unless the
diagonal is unit), and `mul (p A[i, j]) x[j]` is subtracted from the elements `i < j`.
-/
@[expose, specialize] public def trsvLUpperCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d x[j] (p A[(j, j)])
  let x := x.set j hj t
  subColL p A j hj 0 j (by lia) t x

/--
The step of `trsvLWith p .lower` for column `j`: `x[j]` is divided by `p A[j, j]` (unless the
diagonal is unit), and `mul (p A[i, j]) x[j]` is subtracted from the elements `i > j`.
-/
@[expose, specialize] public def trsvLLowerCol (p : ComplexFloat → ComplexFloat)
    (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d x[j] (p A[(j, j)])
  let x := x.set j hj t
  subColL p A j hj (j + 1) (n - (j + 1)) (by lia) t x

/--
`trsvLWith p uplo d A x` solves `(p A) * y = x` for the triangle `uplo` of `A`, with each element
of `A` mapped by `p`, by the loops of `trsv`, but with the products `mul (p A[i, j]) y[j]`, the
element of `A` on the left: from `j = n - 1` down to `0` for the upper triangle, and for
`j = 0, …, n - 1` for the lower one.
-/
@[expose, specialize] public def trsvLWith (p : ComplexFloat → ComplexFloat)
    (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun k hk x => trsvLUpperCol p d A (n - 1 - k) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => trsvLLowerCol p d A j hj x) x

private theorem getElem_trsvLUpperCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (trsvLUpperCol p d A j hj y)[i] =
      if i = j then diagDiv d y[j] (p A[(j, j)])
      else if i < j then y[i] - mul (p A[(i, j)]) (diagDiv d y[j] (p A[(j, j)])) else y[i] := by
  simp only [trsvLUpperCol, getElem_subColL, Vec.getElem_set]
  by_cases e : i = j
  · subst e; simp
  · simp [e]

private theorem getElem_trsvLLowerCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (trsvLLowerCol p d A j hj y)[i] =
      if i = j then diagDiv d y[j] (p A[(j, j)])
      else if j < i then y[i] - mul (p A[(i, j)]) (diagDiv d y[j] (p A[(j, j)])) else y[i] := by
  simp only [trsvLLowerCol, getElem_subColL, Vec.getElem_set]
  by_cases e : i = j
  · subst e; simp [show ¬(i + 1 ≤ i) by lia]
  · have : (j + 1 ≤ i ∧ i < j + 1 + (n - (j + 1))) = (j < i) := by apply propext; lia
    simp [e, this]

/--
Element `i` of the solution of `(p A) * y = x` for the lower triangle of `A`: `x[i]`, minus the
terms `mul (p A[i, l]) y[l]` for `l = 0, …, i - 1`, divided by `p A[i, i]` unless the diagonal is
unit.
-/
@[expose] public def trsvLLowerM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (i : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold i (fun l _hl s => s - mul (p (A.get0 i l)) (trsvLLowerM p d A x l))
    (x.get0 i)) (p (A.get0 i i))
termination_by i
decreasing_by exact _hl

/--
Element `i` of the solution of `(p A) * y = x` for the upper triangle of `A`: `x[i]`, minus the
terms `mul (p A[i, l]) y[l]` for `l = n - 1, …, i + 1`, divided by `p A[i, i]` unless the
diagonal is unit.
-/
@[expose] public def trsvLUpperM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (i : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul (p (A.get0 i (n - 1 - t))) (trsvLUpperM p d A x (n - 1 - t))) (x.get0 i))
    (p (A.get0 i i))
termination_by n - i
decreasing_by lia

private theorem trsvLLowerM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) {i : Nat} (hi : i < n) :
    trsvLLowerM p d A x i = diagDiv d (Nat.fold i (fun l _ s =>
      s - mul (p (A.get0 i l)) (trsvLLowerM p d A x l)) x[i]) (p A[(i, i)]) := by
  rw [trsvLLowerM, vget0_eq' x hi, get0_eq A ⟨hi, hi⟩]

private theorem trsvLUpperM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) {i : Nat} (hi : i < n) :
    trsvLUpperM p d A x i = diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul (p (A.get0 i (n - 1 - t))) (trsvLUpperM p d A x (n - 1 - t))) x[i])
      (p A[(i, i)]) := by
  rw [trsvLUpperM, vget0_eq' x hi, get0_eq A ⟨hi, hi⟩]

private theorem getElem_trsvL_lower' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvLLowerCol p d A j (by lia) x) x)[i] =
        if i < k then trsvLLowerM p d A x i
        else Nat.fold k (fun l _ s => s - mul (p (A.get0 i l)) (trsvLLowerM p d A x l)) x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvLLowerCol p d A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro k hk y hy i hi
      have hyk := hy k hk
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyk
      have ht : diagDiv d y[k] (p A[(k, k)]) = trsvLLowerM p d A x k := by
        rw [hyk, trsvLLowerM_eq p d A x hk]
      rw [getElem_trsvLLowerCol, ht, hy i hi]
      by_cases e : i = k
      · subst e; simp
      · by_cases h : i < k
        · simp [e, h, show i < k + 1 by lia, show ¬k < i by lia]
        · simp only [e, h, show k < i by lia, show ¬i < k + 1 by lia, ↓reduceIte, Nat.fold_succ]
          rw [get0_eq A ⟨hi, hk⟩])

private theorem getElem_trsvL_upper' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvLUpperCol p d A (n - 1 - j) (by lia) x) x)[i] =
        if n - k ≤ i then trsvLUpperM p d A x i
        else Nat.fold k (fun t _ s =>
          s - mul (p (A.get0 i (n - 1 - t))) (trsvLUpperM p d A x (n - 1 - t))) x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvLUpperCol p d A (n - 1 - j) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro k hk y hy i hi
      have hyk := hy (n - 1 - k) (by lia)
      simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hyk
      have ht : diagDiv d y[n - 1 - k] (p A[(n - 1 - k, n - 1 - k)]) =
          trsvLUpperM p d A x (n - 1 - k) := by
        rw [hyk, trsvLUpperM_eq p d A x (by lia),
          Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
      rw [getElem_trsvLUpperCol, ht, hy i hi]
      by_cases e : i = n - 1 - k
      · subst e; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · by_cases h : n - k ≤ i
        · simp [e, h, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k by lia]
        · simp only [e, h, show i < n - 1 - k by lia, show ¬n - (k + 1) ≤ i by lia, ↓reduceIte,
            Nat.fold_succ]
          rw [get0_eq A (i := i) (j := n - 1 - k) ⟨hi, by lia⟩])

/-- Element `i` of `trsvLWith p .lower d A x` is element `i` of the model `trsvLLowerM`. -/
public theorem getElem_trsvLWith_lower_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (i : Nat) (hi : i < n) :
    (trsvLWith p .lower d A x)[i] = trsvLLowerM p d A x i := by
  rw [trsvLWith, getElem_trsvL_lower' p d A x n (Nat.le_refl _) i hi, ite_eq_left hi]

/-- Element `i` of `trsvLWith p .upper d A x` is element `i` of the model `trsvLUpperM`. -/
public theorem getElem_trsvLWith_upper_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (i : Nat) (hi : i < n) :
    (trsvLWith p .upper d A x)[i] = trsvLUpperM p d A x i := by
  rw [trsvLWith, getElem_trsvL_upper' p d A x n (Nat.le_refl _) i hi, ite_eq_left (by lia)]

/--
Element `i` of `y = trsvLWith p .lower d A x` is `x[i]`, minus the terms `mul (p A[i, l]) y[l]`
for `l = 0, …, i - 1`, divided by `p A[i, i]` unless the diagonal is unit.
-/
public theorem getElem_trsvLWith_lower (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (i : Nat) (hi : i < n) :
    (trsvLWith p .lower d A x)[i] = diagDiv d (Nat.fold i (fun l hl s =>
      s - mul (p (A[(i, l)]'⟨hi, by lia⟩)) ((trsvLWith p .lower d A x)[l]'(by lia))) x[i])
        (p A[(i, i)]) := by
  rw [getElem_trsvLWith_lower_eq p d A x i hi, trsvLLowerM_eq p d A x hi]
  congr 1; congr 1; funext l hl s
  rw [getElem_trsvLWith_lower_eq p d A x l (by lia), get0_eq A (i := i) (j := l) ⟨hi, by lia⟩]

/--
Element `i` of `y = trsvLWith p .upper d A x` is `x[i]`, minus the terms `mul (p A[i, l]) y[l]`
for `l = n - 1, …, i + 1`, divided by `p A[i, i]` unless the diagonal is unit.
-/
public theorem getElem_trsvLWith_upper (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (i : Nat) (hi : i < n) :
    (trsvLWith p .upper d A x)[i] = diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul (p (A[(i, n - 1 - t)]'⟨hi, by lia⟩))
        ((trsvLWith p .upper d A x)[n - 1 - t]'(by lia))) x[i]) (p A[(i, i)]) := by
  rw [getElem_trsvLWith_upper_eq p d A x i hi, trsvLUpperM_eq p d A x hi]
  congr 1; congr 1; funext t ht s
  rw [getElem_trsvLWith_upper_eq p d A x (n - 1 - t) (by lia),
    get0_eq A (i := i) (j := n - 1 - t) ⟨hi, by lia⟩]

/-! ## Updates of a column by a vector -/

/-- `C` with column `j` set to `f v[i]` at each row `i`, in one loop. -/
public def setColMap (f : ComplexFloat → ComplexFloat) (v : Vec m) (C : Mat m n) (j : Nat)
    (hj : j < n) : Mat m n :=
  C.withColSlice j hj 0 m (by lia)
    (fun s => Vec.zipWithData (fun _ b => (f b).re) (fun _ b => (f b).im) v s)
    (fun s => by rw [Vec.zipWithData_eq, size_modifyAt2])

public theorem getElem_setColMap (f : ComplexFloat → ComplexFloat) (v : Vec m) (C : Mat m n)
    (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (setColMap f v C j hj)[(i, j')] = if j' = j then f v[i] else C[(i, j')] := by
  unfold setColMap
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  by_cases e : j' = j
  · simp only [e, Nat.zero_le, Nat.zero_add, h.1, and_self, ↓reduceIte, Nat.sub_zero, Vec.get0,
      ↓reduceDIte]
  · simp [e]

/-- `C` with `mul t x[i]` subtracted from each element `i` of column `j`, in one loop. -/
public def subColVec (t : ComplexFloat) (x : Vec m) (C : Mat m n) (j : Nat) (hj : j < n) :
    Mat m n :=
  C.withColSlice j hj 0 m (by lia)
    (fun s => Vec.zipWithData (fun c b => c.re - mulRe t b) (fun c b => c.im - mulIm t b) x s)
    (fun s => by rw [Vec.zipWithData_eq, size_modifyAt2])

public theorem getElem_subColVec (t : ComplexFloat) (x : Vec m) (C : Mat m n) (j : Nat)
    (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (subColVec t x C j hj)[(i, j')] = if j' = j then C[(i, j')] - mul t x[i] else C[(i, j')] := by
  unfold subColVec
  rw [getElem_withColSlice _ _ _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  by_cases e : j' = j
  · simp only [e, Nat.zero_le, Nat.zero_add, h.1, and_self, ↓reduceIte, Nat.sub_zero, Vec.get0,
      ↓reduceDIte, mulRe_eq, mulIm_eq]
    rfl
  · simp [e]

/--
After `k` steps `g l` that each keep an invariant `inv l` of the elements, from `C` that has
`inv 0`, the matrix has `inv k`.
-/
public theorem getElem_fold_of_inv {K : Nat} (g : (l : Nat) → l < K → Mat m n → Mat m n)
    (inv : Nat → (i j : Nat) → i < m ∧ j < n → ComplexFloat) (C : Mat m n)
    (h0 : ∀ i j h, C[(i, j)] = inv 0 i j h)
    (hg : ∀ l hl (D : Mat m n), (∀ i j h, D[(i, j)] = inv l i j h) →
      ∀ i j h, (g l hl D)[(i, j)] = inv (l + 1) i j h) :
    ∀ k (hk : k ≤ K) i j h, (Nat.fold k (fun l hl D => g l (by lia) D) C)[(i, j)] = inv k i j h
  | 0, _ => by simpa using h0
  | k + 1, hk => by
    rw [Nat.fold_succ]
    exact hg k (by lia) _ (getElem_fold_of_inv g inv C h0 hg k (by lia))

/-! ## `trsm`, `trsmT` and `trsmC` -/

/--
`trsm uplo d α A B` is `α * A⁻¹ * B` for the triangle `uplo` of `A`, with a unit diagonal if `d`
is `.unit`, as `ztrsm` with `SIDE = 'L'` and `TRANSA = 'N'`: it sets `B` to `0` when `α = 0`, and
otherwise sets each column `j` to the solution `trsv uplo d A` of the column scaled by `α`, whose
elements are `mul α B[i, j]`.
-/
@[expose] public def trsm (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat m m) (B : Mat m n) : Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else Nat.fold n (fun j hj C =>
    setColMap id (trsv uplo d A (Vec.ofFn fun i => mul α B[(i.val, j)])) C j hj) B

/-- Element `(i, j)` of `trsm uplo d α A B`: `0` when `α = 0`, and otherwise element `i` of the
solution `trsv uplo d A` of column `j` scaled by `α`. -/
public theorem getElem_trsm (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat m m) (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trsm uplo d α A B)[(i, j)] =
      if isZero α then zero
      else (trsv uplo d A (Vec.ofFn fun l => mul α (B[(l.val, j)]'⟨l.isLt, h.2⟩)))[i] := by
  unfold trsm
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C =>
        setColMap id (trsv uplo d A (Vec.ofFn fun i => mul α B[(i.val, j)])) C j hj)
      (fun i j hij _ =>
        (trsv uplo d A (Vec.ofFn fun l => mul α (B[(l.val, j)]'⟨l.isLt, hij.2⟩)))[i])
      (fun _ _ _ _ _ _ => by rw [getElem_setColMap]; rfl) B i j h n (Nat.le_refl _)]
    simp [h.2]

/--
`trsmTWith p uplo d α A B` is `α` times the solution of `(p A)ᵀ * X = B` for the triangle `uplo`
of `A`, with its elements mapped by `p`, as `ztrsm` with `SIDE = 'L'` and `TRANSA = 'T'`
(`p = id`) or `'C'` (`p = conj`): it sets `B` to `0` when `α = 0`, and otherwise sets each column
`j` to the solution `trsvTAscWith p uplo d A` of the column scaled by `α`.
-/
@[expose, specialize] public def trsmTWith (p : ComplexFloat → ComplexFloat)
    (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat) (A : Mat m m) (B : Mat m n) :
    Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else Nat.fold n (fun j hj C =>
    setColMap id (trsvTAscWith p uplo d A (Vec.ofFn fun i => mul α B[(i.val, j)])) C j hj) B

/-- Element `(i, j)` of `trsmTWith p uplo d α A B`: `0` when `α = 0`, and otherwise element `i`
of the solution `trsvTAscWith p uplo d A` of column `j` scaled by `α`. -/
public theorem getElem_trsmTWith (p : ComplexFloat → ComplexFloat) (uplo : Float64.Uplo)
    (d : Float64.Diag) (α : ComplexFloat) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trsmTWith p uplo d α A B)[(i, j)] =
      if isZero α then zero
      else (trsvTAscWith p uplo d A
        (Vec.ofFn fun l => mul α (B[(l.val, j)]'⟨l.isLt, h.2⟩)))[i] := by
  unfold trsmTWith
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C =>
        setColMap id (trsvTAscWith p uplo d A (Vec.ofFn fun i => mul α B[(i.val, j)])) C j hj)
      (fun i j hij _ => (trsvTAscWith p uplo d A
        (Vec.ofFn fun l => mul α (B[(l.val, j)]'⟨l.isLt, hij.2⟩)))[i])
      (fun _ _ _ _ _ _ => by rw [getElem_setColMap]; rfl) B i j h n (Nat.le_refl _)]
    simp [h.2]

/-- `trsmT uplo d α A B` is `α * A⁻ᵀ * B`, as `trsmTWith id`. -/
@[expose] public def trsmT (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat m m) (B : Mat m n) : Mat m n :=
  trsmTWith id uplo d α A B

/-- `trsmC uplo d α A B` is `α * A⁻ᴴ * B`, as `trsmTWith conj`. -/
@[expose] public def trsmC (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat m m) (B : Mat m n) : Mat m n :=
  trsmTWith ComplexFloat.conj uplo d α A B

/-! ## `trsmRight` -/

/--
Column `j` of `trsmRight .upper`: `α` times the column, minus `mul A[l, j] C[i, l]` for the solved
columns `l = 0, …, j - 1`, in this order, divided by `A[j, j]` unless the diagonal is unit, as
`ztrsm` with `SIDE = 'R'`, `TRANSA = 'N'` and `UPLO = 'U'`.
-/
public def trsmRightUpperCol (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n) (C : Mat m n)
    (j : Nat) (hj : j < n) : Mat m n :=
  let v : Vec m := Vec.ofFn fun i => mul α C[(i.val, j)]
  let v := Nat.fold j (fun l hl v => C.subColOf l (by lia) A[(l, j)] v) v
  setColMap (fun z => diagDiv d z A[(j, j)]) v C j hj

/--
Column `j` of `trsmRight .lower`: `α` times the column, minus `mul A[l, j] C[i, l]` for the solved
columns `l = j + 1, …, n - 1`, in this order, divided by `A[j, j]` unless the diagonal is unit, as
`ztrsm` with `SIDE = 'R'`, `TRANSA = 'N'` and `UPLO = 'L'`.
-/
public def trsmRightLowerCol (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n) (C : Mat m n)
    (j : Nat) (hj : j < n) : Mat m n :=
  let v : Vec m := Vec.ofFn fun i => mul α C[(i.val, j)]
  let v := Nat.fold (n - (j + 1)) (fun t ht v => C.subColOf (j + 1 + t) (by lia)
    A[(j + 1 + t, j)] v) v
  setColMap (fun z => diagDiv d z A[(j, j)]) v C j hj

private theorem getElem_trsmRightUpperCol (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n)
    (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (trsmRightUpperCol d α A C j hj)[(i, j')] =
      if j' = j then diagDiv d (Nat.fold j (fun l hl s =>
          s - mul (A[(l, j)]'⟨by lia, hj⟩) (C[(i, l)]'⟨h.1, by lia⟩)) (mul α C[(i, j)]))
        A[(j, j)]
      else C[(i, j')] := by
  unfold trsmRightUpperCol
  rw [getElem_setColMap]
  by_cases e : j' = j
  · subst e
    simp only [↓reduceIte]
    rw [Vec.getElem_fold_of_pointwise (fun l hl v => C.subColOf l (by lia) A[(l, j')] v)
      (fun l hl i hi s => s - mul (A[(l, j')]'⟨by lia, hj⟩) (C[(i, l)]'⟨hi, by lia⟩))
      (fun _ _ _ _ _ => getElem_subColOf ..) _ i h.1 j' (Nat.le_refl _), Vec.getElem_ofFn]
  · simp [e]

private theorem getElem_trsmRightLowerCol (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n)
    (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (trsmRightLowerCol d α A C j hj)[(i, j')] =
      if j' = j then diagDiv d (Nat.fold (n - (j + 1)) (fun t ht s =>
          s - mul (A[(j + 1 + t, j)]'⟨by lia, hj⟩) (C[(i, j + 1 + t)]'⟨h.1, by lia⟩))
          (mul α C[(i, j)])) A[(j, j)]
      else C[(i, j')] := by
  unfold trsmRightLowerCol
  rw [getElem_setColMap]
  by_cases e : j' = j
  · subst e
    simp only [↓reduceIte]
    rw [Vec.getElem_fold_of_pointwise (fun t ht v => C.subColOf (j' + 1 + t) (by lia)
        A[(j' + 1 + t, j')] v)
      (fun t ht i hi s => s - mul (A[(j' + 1 + t, j')]'⟨by lia, hj⟩)
        (C[(i, j' + 1 + t)]'⟨hi, by lia⟩))
      (fun _ _ _ _ _ => getElem_subColOf ..) _ i h.1 (n - (j' + 1)) (Nat.le_refl _),
      Vec.getElem_ofFn]
  · simp [e]

/-- Row `i` of `B` scaled by `α`, as a vector. -/
@[expose] public def rowScaled (α : ComplexFloat) (B : Mat m n) (i : Nat) (hi : i < m) : Vec n :=
  Vec.ofFn fun l => mul α (B[(i, l.val)]'⟨hi, l.isLt⟩)

@[simp] public theorem getElem_rowScaled (α : ComplexFloat) (B : Mat m n) (i : Nat) (hi : i < m)
    (l : Nat) (hl : l < n) : (rowScaled α B i hi)[l] = mul α B[(i, l)] := by
  simp [rowScaled]

/-- The first `k` steps of `trsvTWith id .upper d A x`. -/
private def rowU (d : Float64.Diag) (A : Mat n n) (x : Vec n) (k : Nat) : Vec n :=
  Nat.fold k (fun l _ x => if h : l < n then trsvTUpperCol id d A l h x else x) x

private theorem rowU_succ (d : Float64.Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k < n) :
    rowU d A x (k + 1) = trsvTUpperCol id d A k hk (rowU d A x k) := by
  simp [rowU, Nat.fold_succ, hk]

private theorem rowU_n (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    rowU d A x n = trsvTWith id .upper d A x := by
  unfold rowU trsvTWith
  congr 1; funext l hl y; simp [hl]

/-- The steps of `rowU` keep the elements they haven't reached. -/
private theorem getElem_rowU_ge (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    ∀ s j (hj : j < n), s ≤ j → (rowU d A x s)[j] = x[j]
  | 0, _, _, _ => by simp [rowU]
  | s + 1, j, hj, hsj => by
    rw [rowU_succ d A x (by lia)]
    simp only [trsvTUpperCol, Vec.getElem_set, show j ≠ s by lia, ↓reduceIte]
    exact getElem_rowU_ge d A x s j hj (by lia)

/-- The first `k` steps of `trsvTLowerAsc id d A x`. -/
private def rowL (d : Float64.Diag) (A : Mat n n) (x : Vec n) (k : Nat) : Vec n :=
  Nat.fold k (fun l _ x => if h : l < n then trsvTLowerAscCol id d A (n - 1 - l) (by lia) x
    else x) x

private theorem rowL_succ (d : Float64.Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k < n) :
    rowL d A x (k + 1) = trsvTLowerAscCol id d A (n - 1 - k) (by lia) (rowL d A x k) := by
  simp [rowL, Nat.fold_succ, hk]

private theorem rowL_n (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    rowL d A x n = trsvTLowerAsc id d A x := by
  unfold rowL trsvTLowerAsc
  congr 1; funext l hl y; simp [hl]

/-- The steps of `rowL` keep the elements they haven't reached. -/
private theorem getElem_rowL_lt (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    ∀ s j (hj : j < n), j < n - s → (rowL d A x s)[j] = x[j]
  | 0, _, _, _ => by simp [rowL]
  | s + 1, j, hj, hsj => by
    rw [rowL_succ d A x (by lia)]
    simp only [trsvTLowerAscCol, Vec.getElem_set, show j ≠ n - 1 - s by lia, ↓reduceIte]
    exact getElem_rowL_lt d A x s j hj (by lia)

private theorem getElem_trsmRight_upper (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n)
    (B : Mat m n) :
    ∀ k (hk : k ≤ n) i j (h : i < m ∧ j < n),
      (Nat.fold k (fun j hj C => trsmRightUpperCol d α A C j (by lia)) B)[(i, j)] =
        if j < k then (rowU d A (rowScaled α B i h.1) k)[j] else B[(i, j)] :=
  getElem_fold_of_inv (K := n) (fun j hj C => trsmRightUpperCol d α A C j hj)
    (fun k i j h => if j < k then (rowU d A (rowScaled α B i h.1) k)[j] else B[(i, j)]) B
    (fun i j h => by simp) (by
      intro k hk D hD i j h
      rw [getElem_trsmRightUpperCol]
      by_cases e : j = k
      · subst e
        have hDj := hD i j h
        simp only [Nat.lt_irrefl, ↓reduceIte] at hDj
        simp only [↓reduceIte, Nat.lt_add_one, rowU_succ d A _ hk, trsvTUpperCol, Vec.getElem_set,
          Vec.acc_eq, Vec.opC_sub, id, hDj]
        rw [getElem_rowU_ge d A _ j j h.2 (Nat.le_refl _)]
        rw [getElem_rowScaled]
        congr 1; congr 1; funext l hl s
        have hDl := hD i l ⟨h.1, by lia⟩
        simp only [hl, ↓reduceIte] at hDl
        simp only [Vec.getElem_slice, getElem_col, Nat.zero_add, hDl]
      · rw [ite_eq_right e, hD i j h]
        by_cases hj : j < k
        · simp only [hj, ↓reduceIte, show j < k + 1 by lia, rowU_succ d A _ hk, trsvTUpperCol,
            Vec.getElem_set, e]
        · simp [hj, show ¬j < k + 1 by lia])

private theorem getElem_trsmRight_lower (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n)
    (B : Mat m n) :
    ∀ k (hk : k ≤ n) i j (h : i < m ∧ j < n),
      (Nat.fold k (fun s hs C => trsmRightLowerCol d α A C (n - 1 - s) (by lia)) B)[(i, j)] =
        if n - k ≤ j then (rowL d A (rowScaled α B i h.1) k)[j] else B[(i, j)] :=
  getElem_fold_of_inv (K := n) (fun s hs C => trsmRightLowerCol d α A C (n - 1 - s) (by lia))
    (fun k i j h => if n - k ≤ j then (rowL d A (rowScaled α B i h.1) k)[j] else B[(i, j)]) B
    (fun i j h => by simp [show ¬n ≤ j by lia]) (by
      intro k hk D hD i j h
      rw [getElem_trsmRightLowerCol]
      by_cases e : j = n - 1 - k
      · subst e
        have hDj := hD i (n - 1 - k) h
        simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hDj
        simp only [↓reduceIte, show n - (k + 1) ≤ n - 1 - k by lia, rowL_succ d A _ hk,
          trsvTLowerAscCol, Vec.getElem_set, Vec.acc_eq, Vec.opC_sub, id, hDj]
        rw [getElem_rowL_lt d A _ k (n - 1 - k) h.2 (by lia)]
        rw [getElem_rowScaled]
        congr 1; congr 1; funext t ht s
        have hDl := hD i (n - 1 - k + 1 + t) ⟨h.1, by lia⟩
        simp only [show n - k ≤ n - 1 - k + 1 + t by lia, ↓reduceIte] at hDl
        simp only [Vec.getElem_slice, getElem_col, hDl]
      · rw [ite_eq_right e, hD i j h]
        by_cases hj : n - k ≤ j
        · simp only [hj, ↓reduceIte, show n - (k + 1) ≤ j by lia, rowL_succ d A _ hk,
            trsvTLowerAscCol, Vec.getElem_set, e]
        · simp [hj, show ¬n - (k + 1) ≤ j by lia])

/--
`trsmRight uplo d α A B` is `α * B * A⁻¹` for the triangle `uplo` of `A`, with a unit diagonal if
`d` is `.unit`, as `ztrsm` with `SIDE = 'R'` and `TRANSA = 'N'`: it sets `B` to `0` when `α = 0`,
and otherwise solves for the columns in increasing order for the upper triangle
(`trsmRightUpperCol`) and in decreasing order for the lower one (`trsmRightLowerCol`).
-/
@[expose] public def trsmRight (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat n n) (B : Mat m n) : Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else match uplo with
    | .upper => Nat.fold n (fun j hj C => trsmRightUpperCol d α A C j hj) B
    | .lower => Nat.fold n (fun s hs C => trsmRightLowerCol d α A C (n - 1 - s) (by lia)) B

/--
Element `(i, j)` of `trsmRight uplo d α A B`: `0` when `α = 0`, and otherwise element `j` of the
solution `trsvTAscWith id uplo d A` for row `i` of `B` scaled by `α` (`rowScaled`): row `i` of the
result `X` solves `X[i, :] * A = α * B[i, :]`, with the terms in the order of `ztrsm`.
-/
public theorem getElem_trsmRight (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat n n) (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRight uplo d α A B)[(i, j)] =
      if isZero α then zero else (trsvTAscWith id uplo d A (rowScaled α B i h.1))[j] := by
  unfold trsmRight
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    cases uplo
    · rw [getElem_trsmRight_upper d α A B n (Nat.le_refl _) i j h, ite_eq_left h.2, rowU_n]
      rfl
    · rw [getElem_trsmRight_lower d α A B n (Nat.le_refl _) i j h, ite_eq_left (by lia), rowL_n]
      rfl

/-! ## `trsmRightT` and `trsmRightC` -/

/--
Step `k` of `trsmRightTWith p`: column `k` is divided by `p A[k, k]` (unless the diagonal is unit),
`mul (p A[j, k]) C[i, k]` is subtracted from the columns `j` in the triangle of column `k` of `A`,
other than `k`, with the divided column `k`, and column `k` is then multiplied by `α`, as `ztrsm`
with `SIDE = 'R'` and `TRANSA = 'T'` or `'C'`.
-/
@[specialize] public def trsmRightTStep (p : ComplexFloat → ComplexFloat) (uplo : Float64.Uplo)
    (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n) (C : Mat m n) (k : Nat) (hk : k < n) :
    Mat m n :=
  let C := mapColSlice (fun z => diagDiv d z (p A[(k, k)])) C k hk 0 m (by lia)
  let x : Vec m := Vec.ofFn fun i => C[(i.val, k)]
  let C := Nat.fold n (fun j hj C =>
    if InTri uplo j k then subColVec (p A[(j, k)]) x C j hj else C) C
  mapColSlice (mul α) C k hk 0 m (by lia)

private theorem fold_single {α : Type _} : ∀ (K : Nat) (f : (j : Nat) → j < K → α → α) (j' : Nat)
    (v : α), (∀ j hj w, j ≠ j' → f j hj w = w) →
    Nat.fold K f v = if h : j' < K then f j' h v else v
  | 0, _, _, _, _ => by simp
  | K + 1, f, j', v, hf => by
    rw [Nat.fold_succ, fold_single K _ j' v (fun j hj w hne => hf j _ w hne)]
    by_cases e : j' = K
    · subst e; simp
    · rw [hf K _ _ (Ne.symm e)]
      by_cases h : j' < K
      · simp [h, Nat.lt_succ_of_lt h]
      · have h' : ¬ j' < K + 1 := by lia
        simp [h, h']

private theorem getElem_trsmRightTStep (p : ComplexFloat → ComplexFloat) (uplo : Float64.Uplo)
    (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n) (C : Mat m n) (k : Nat) (hk : k < n)
    (i j' : Nat) (h : i < m ∧ j' < n) :
    (trsmRightTStep p uplo d α A C k hk)[(i, j')] =
      if j' = k then mul α (diagDiv d C[(i, k)] (p A[(k, k)]))
      else if InTri uplo j' k then
        C[(i, j')] - mul (p A[(j', k)]) (diagDiv d C[(i, k)] (p A[(k, k)]))
      else C[(i, j')] := by
  unfold trsmRightTStep
  have hC1 : ∀ i (hi : i < m), (mapColSlice (fun z => diagDiv d z (p A[(k, k)])) C k hk 0 m
      (by lia))[(i, k)] = diagDiv d C[(i, k)] (p A[(k, k)]) := by
    intro i hi; simp [getElem_mapColSlice, hi]
  rw [getElem_mapColSlice]
  rw [getElem_fold_of_pointwise (fun j hj C' =>
      if InTri uplo j k then subColVec (p A[(j, k)])
        (Vec.ofFn fun i : Fin m => (mapColSlice (fun z => diagDiv d z (p A[(k, k)])) C k hk 0 m
          (by lia))[(i.val, k)]) C' j hj else C')
    (fun j hj i j' h w => if j' = j ∧ InTri uplo j k then
      w - mul (p A[(j, k)]) ((Vec.ofFn fun i : Fin m => (mapColSlice (fun z => diagDiv d z
        (p A[(k, k)])) C k hk 0 m (by lia))[(i.val, k)])[i]) else w)
    (fun j hj C' i j' h => by
      by_cases ht : InTri uplo j k
      · simp only [ht, ↓reduceIte, getElem_subColVec, and_true]
      · simp [ht])
    _ i j' h n (Nat.le_refl _)]
  have hi : (0 ≤ i ∧ i < 0 + m) = True := by simp [h.1]
  simp only [Vec.getElem_ofFn, getElem_mapColSlice, hi, and_true, ↓reduceIte]
  by_cases e : j' = k
  · subst e
    have hn : ¬ InTri uplo j' j' := by unfold InTri; lia
    rw [fold_single _ _ j' _ (fun j hj w hne => by simp [Ne.symm hne])]
    simp [hn, h.2]
  · simp only [e, ↓reduceIte]
    rw [fold_single _ _ j' _ (fun j hj w hne => by simp [Ne.symm hne])]
    simp [h.2]

/-- Row `i` of `B`, as a vector. -/
@[expose] public def rowVec (B : Mat m n) (i : Nat) (hi : i < m) : Vec n :=
  Vec.ofFn fun l => B[(i, l.val)]'⟨hi, l.isLt⟩

@[simp] public theorem getElem_rowVec (B : Mat m n) (i : Nat) (hi : i < m) (l : Nat)
    (hl : l < n) : (rowVec B i hi)[l] = B[(i, l)] := by
  simp [rowVec]

/-- The first `k` steps of `trsvLWith p .upper d A x`. -/
private def rowLU (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (A : Mat n n) (x : Vec n)
    (k : Nat) : Vec n :=
  Nat.fold k (fun l _ x => if h : l < n then trsvLUpperCol p d A (n - 1 - l) (by lia) x
    else x) x

private theorem rowLU_succ (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (A : Mat n n)
    (x : Vec n) {k : Nat} (hk : k < n) :
    rowLU p d A x (k + 1) = trsvLUpperCol p d A (n - 1 - k) (by lia) (rowLU p d A x k) := by
  simp [rowLU, Nat.fold_succ, hk]

private theorem rowLU_n (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (A : Mat n n)
    (x : Vec n) : rowLU p d A x n = trsvLWith p .upper d A x := by
  unfold rowLU trsvLWith
  congr 1; funext l hl y; simp [hl]

/-- The first `k` steps of `trsvLWith p .lower d A x`. -/
private def rowLL (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (A : Mat n n) (x : Vec n)
    (k : Nat) : Vec n :=
  Nat.fold k (fun l _ x => if h : l < n then trsvLLowerCol p d A l h x else x) x

private theorem rowLL_succ (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (A : Mat n n)
    (x : Vec n) {k : Nat} (hk : k < n) :
    rowLL p d A x (k + 1) = trsvLLowerCol p d A k hk (rowLL p d A x k) := by
  simp [rowLL, Nat.fold_succ, hk]

private theorem rowLL_n (p : ComplexFloat → ComplexFloat) (d : Float64.Diag) (A : Mat n n)
    (x : Vec n) : rowLL p d A x n = trsvLWith p .lower d A x := by
  unfold rowLL trsvLWith
  congr 1; funext l hl y; simp [hl]

private theorem getElem_trsmRightT_upper (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (α : ComplexFloat) (A : Mat n n) (B : Mat m n) :
    ∀ k (hk : k ≤ n) i j (h : i < m ∧ j < n),
      (Nat.fold k (fun s hs C => trsmRightTStep p .upper d α A C (n - 1 - s) (by lia)) B)[(i, j)] =
        if n - k ≤ j then mul α (rowLU p d A (rowVec B i h.1) k)[j]
        else (rowLU p d A (rowVec B i h.1) k)[j] :=
  getElem_fold_of_inv (K := n) (fun s hs C => trsmRightTStep p .upper d α A C (n - 1 - s)
      (by lia))
    (fun k i j h => if n - k ≤ j then mul α (rowLU p d A (rowVec B i h.1) k)[j]
      else (rowLU p d A (rowVec B i h.1) k)[j]) B
    (fun i j h => by simp [show ¬n ≤ j by lia, rowLU]) (by
      intro k hk D hD i j h
      rw [getElem_trsmRightTStep, rowLU_succ p d A _ hk, getElem_trsvLUpperCol]
      have hDk := hD i (n - 1 - k) ⟨h.1, by lia⟩
      simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hDk
      by_cases e : j = n - 1 - k
      · subst e
        simp [show n - (k + 1) ≤ n - 1 - k by lia, hDk]
      · by_cases hj : j < n - 1 - k
        · have hDj := hD i j h
          simp only [show ¬n - k ≤ j by lia, ↓reduceIte] at hDj
          simp [e, hj, InTri, show ¬n - (k + 1) ≤ j by lia, hDj, hDk]
        · have hDj := hD i j h
          simp only [show n - k ≤ j by lia, ↓reduceIte] at hDj
          simp [e, hj, InTri, show n - (k + 1) ≤ j by lia, hDj])

private theorem getElem_trsmRightT_lower (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (α : ComplexFloat) (A : Mat n n) (B : Mat m n) :
    ∀ k (hk : k ≤ n) i j (h : i < m ∧ j < n),
      (Nat.fold k (fun k hk C => trsmRightTStep p .lower d α A C k (by lia)) B)[(i, j)] =
        if j < k then mul α (rowLL p d A (rowVec B i h.1) k)[j]
        else (rowLL p d A (rowVec B i h.1) k)[j] :=
  getElem_fold_of_inv (K := n) (fun k hk C => trsmRightTStep p .lower d α A C k hk)
    (fun k i j h => if j < k then mul α (rowLL p d A (rowVec B i h.1) k)[j]
      else (rowLL p d A (rowVec B i h.1) k)[j]) B
    (fun i j h => by simp [rowLL]) (by
      intro k hk D hD i j h
      rw [getElem_trsmRightTStep, rowLL_succ p d A _ hk, getElem_trsvLLowerCol]
      have hDk := hD i k ⟨h.1, hk⟩
      simp only [Nat.lt_irrefl, ↓reduceIte] at hDk
      by_cases e : j = k
      · subst e
        simp [hDk]
      · by_cases hj : k < j
        · have hDj := hD i j h
          simp only [show ¬j < k by lia, ↓reduceIte] at hDj
          simp [e, hj, InTri, show ¬j < k + 1 by lia, hDj, hDk]
        · have hDj := hD i j h
          simp only [show j < k by lia, ↓reduceIte] at hDj
          simp [e, hj, InTri, show j < k + 1 by lia, hDj])

/--
`trsmRightTWith p uplo d α A B` is `α` times the solution of `X * (p A)ᵀ = B` for the triangle
`uplo` of `A`, with its elements mapped by `p`, as `ztrsm` with `SIDE = 'R'` and `TRANSA = 'T'`
(`p = id`) or `'C'` (`p = conj`): it sets `B` to `0` when `α = 0`, and otherwise runs the steps
`trsmRightTStep p` from the last column for the upper triangle and from the first one for the
lower one.
-/
@[expose, specialize] public def trsmRightTWith (p : ComplexFloat → ComplexFloat)
    (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n) (B : Mat m n) :
    Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else match uplo with
    | .upper => Nat.fold n (fun s hs C => trsmRightTStep p .upper d α A C (n - 1 - s) (by lia)) B
    | .lower => Nat.fold n (fun k hk C => trsmRightTStep p .lower d α A C k hk) B

/--
Element `(i, j)` of `trsmRightTWith p uplo d α A B`: `0` when `α = 0`, and otherwise `α` times
element `j` of the solution `trsvLWith p uplo d A` for row `i` of `B` (`rowVec`): row `i` of the
result, divided by `α`, solves `(p A) * y = B[i, :]`, with the operations in the order of `ztrsm`.
-/
public theorem getElem_trsmRightTWith (p : ComplexFloat → ComplexFloat) (uplo : Float64.Uplo)
    (d : Float64.Diag) (α : ComplexFloat) (A : Mat n n) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trsmRightTWith p uplo d α A B)[(i, j)] =
      if isZero α then zero else mul α (trsvLWith p uplo d A (rowVec B i h.1))[j] := by
  unfold trsmRightTWith
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    cases uplo
    · rw [getElem_trsmRightT_upper p d α A B n (Nat.le_refl _) i j h, ite_eq_left (by lia),
        rowLU_n]
    · rw [getElem_trsmRightT_lower p d α A B n (Nat.le_refl _) i j h, ite_eq_left h.2, rowLL_n]

/-- `trsmRightT uplo d α A B` is `α * B * A⁻ᵀ`, as `trsmRightTWith id`. -/
@[expose] public def trsmRightT (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat n n) (B : Mat m n) : Mat m n :=
  trsmRightTWith id uplo d α A B

/-- `trsmRightC uplo d α A B` is `α * B * A⁻ᴴ`, as `trsmRightTWith conj`. -/
@[expose] public def trsmRightC (uplo : Float64.Uplo) (d : Float64.Diag) (α : ComplexFloat)
    (A : Mat n n) (B : Mat m n) : Mat m n :=
  trsmRightTWith ComplexFloat.conj uplo d α A B

end Mat

end BLAS.ComplexFloat64
