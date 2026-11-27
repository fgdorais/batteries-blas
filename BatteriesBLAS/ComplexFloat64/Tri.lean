/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Herm

/-!
# Triangular Level 2

The triangular routines on complex matrices: the products `trmv` (`x := A * x`), `trmvT`
(`x := Aᵀ * x`) and `trmvC` (`x := Aᴴ * x`), and the solves `trsv`, `trsvT` and `trsvC` of the
same systems, on the upper or the lower triangle of `A`, with a unit diagonal or not, as `ztrmv`
and `ztrsv` in the reference BLAS (`master`), with the same operations in the same order. A
quotient is `div`, the division of gfortran.

They run a step per column of `A`, in the order of the reference BLAS: the products and solves
by `A` update a part of `x` by a multiple of the part of the column in the triangle, and the
others set an element of `x` to a sum over the part of the column, from the diagonal outwards in
the products and towards the diagonal in the solves. Each step updates `x` in place when its
array is not shared.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.ComplexFloat64

namespace Vec

variable {n : Nat}

/-! ## Sums over a range -/

/-- The parts of `z` and `w` combined by `op`: `⟨op z.re w.re, op z.im w.im⟩`. -/
@[expose] public def opC (op : Float → Float → Float) (z w : ComplexFloat) :
    ComplexFloat :=
  ⟨op z.re w.re, op z.im w.im⟩

/--
The loop of `acc` from the index `i`, up to the bound `m`, which is `n`, with the parts `sr` and
`si` of the sum so far: it combines it with `mul (p x[i]) y[i]` by `op`.
-/
@[specialize] public def accLoop (p : ComplexFloat → ComplexFloat)
    (op : Float → Float → Float)
    (x y : Vec n) (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float) : ComplexFloat :=
  if hi : i < m then
    let u := p (x.uget xo xo1 xc hxo hxo1 hxc hs.1 i (hm ▸ hi))
    let v := y.uget yo yo1 yc hyo hyo1 hyc hs.2 i (hm ▸ hi)
    let tr := u.re * v.re - u.im * v.im
    let ti := u.re * v.im + u.im * v.re
    let ok := tr == tr || ti == ti
    accLoop p op x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm (i + 1)
      (op sr (if ok then tr else mulRecoverRe u.re u.im v.re v.im))
      (op si (if ok then ti else mulRecoverIm u.re u.im v.re v.im))
  else ⟨sr, si⟩
termination_by m.toNat - i.toNat
decreasing_by
  grind

/-- The step of `accLoop` is `opC op` with `mul (p u) v`. -/
private theorem opC_mul (p : ComplexFloat → ComplexFloat) (op : Float → Float → Float)
    (s u v : ComplexFloat) :
    (⟨op s.re (if ((p u).re * v.re - (p u).im * v.im == (p u).re * v.re - (p u).im * v.im ||
          (p u).re * v.im + (p u).im * v.re == (p u).re * v.im + (p u).im * v.re) = true
        then (p u).re * v.re - (p u).im * v.im else mulRecoverRe (p u).re (p u).im v.re v.im),
      op s.im (if ((p u).re * v.re - (p u).im * v.im == (p u).re * v.re - (p u).im * v.im ||
          (p u).re * v.im + (p u).im * v.re == (p u).re * v.im + (p u).im * v.re) = true
        then (p u).re * v.im + (p u).im * v.re else mulRecoverIm (p u).re (p u).im v.re v.im)⟩ :
      ComplexFloat) = opC op s (mul (p u) v) := by
  simp only [opC, mul, mulRecoverRe, mulRecoverIm]
  split <;> rfl

private theorem accLoop_eq (p : ComplexFloat → ComplexFloat) (op : Float → Float → Float)
    (x y : Vec n) (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float) (z : ComplexFloat) (j : Nat)
    (hj : i.toNat = j) (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl s => opC op s (mul (p x[l]) y[l])) z = ⟨sr, si⟩) :
    accLoop p op x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm i sr si =
      Nat.fold n (fun l hl s => opC op s (mul (p x[l]) y[l])) z := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i sr si j with
  | zero =>
    rw [accLoop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    rw [accLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem]
    subst hj
    refine ih (i + 1) _ _ (i.toNat + 1) hsucc (by lia) ?_ (by lia)
    rw [Nat.fold_succ, hacc]
    exact (opC_mul ..).symm

/--
The loop of `accRev` from the step `i`, up to the bound `m`, which is `n`: it combines the sum so
far with `mul (p x[k]) y[k]` by `op`, for `k = m - 1 - i`.
-/
@[specialize] public def accRevLoop (p : ComplexFloat → ComplexFloat)
    (op : Float → Float → Float) (x y : Vec n) (xo xo1 xc yo yo1 yc : USize)
    (hxo : (2 * x.off).toUSize = xo) (hxo1 : (2 * x.off + 1).toUSize = xo1)
    (hxc : (2 * x.inc).toUSize = xc) (hyo : (2 * y.off).toUSize = yo)
    (hyo1 : (2 * y.off + 1).toUSize = yo1) (hyc : (2 * y.inc).toUSize = yc)
    (hs : x.data.size < USize.size ∧ y.data.size < USize.size) (m : USize) (hm : m.toNat = n)
    (i : USize) (sr si : Float) : ComplexFloat :=
  if hi : i < m then
    have hk : (m - 1 - i).toNat < n := by grind
    let u := p (x.uget xo xo1 xc hxo hxo1 hxc hs.1 (m - 1 - i) hk)
    let v := y.uget yo yo1 yc hyo hyo1 hyc hs.2 (m - 1 - i) hk
    let tr := u.re * v.re - u.im * v.im
    let ti := u.re * v.im + u.im * v.re
    let ok := tr == tr || ti == ti
    accRevLoop p op x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm (i + 1)
      (op sr (if ok then tr else mulRecoverRe u.re u.im v.re v.im))
      (op si (if ok then ti else mulRecoverIm u.re u.im v.re v.im))
  else ⟨sr, si⟩
termination_by m.toNat - i.toNat
decreasing_by
  grind

private theorem accRevLoop_eq (p : ComplexFloat → ComplexFloat)
    (op : Float → Float → Float)
    (x y : Vec n) (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float) (z : ComplexFloat) (j : Nat)
    (hj : i.toNat = j) (hjn : j ≤ n)
    (hacc : Nat.fold j (fun t ht s => opC op s
      (mul (p (x[n - 1 - t]'(by lia))) (y[n - 1 - t]'(by lia)))) z = ⟨sr, si⟩) :
    accRevLoop p op x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm i sr si =
      Nat.fold n (fun t ht s => opC op s
        (mul (p (x[n - 1 - t]'(by lia))) (y[n - 1 - t]'(by lia)))) z := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i sr si j with
  | zero =>
    rw [accRevLoop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    have hk : (m - 1 - i).toNat = n - 1 - j := by
      have : i.toNat < m.toNat := hi
      rw [USize.toNat_sub_of_le _ _ (by grind), USize.toNat_sub_of_le _ _ (by grind)]
      simp; lia
    rw [accRevLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem, getElem_eq_of_eq _ hk]
    refine ih (i + 1) _ _ (j + 1) hsucc (by lia) ?_ (by lia)
    rw [Nat.fold_succ, hacc]
    exact (opC_mul ..).symm

/--
`Nat.fold n (fun l _ s => opC op s (mul (p x[l]) y[l])) z`: the sum `z` combined by `op` with the
products `mul (p x[l]) y[l]` for `l = 0, …, n - 1`, by `accLoop`.
-/
@[inline] public def acc (p : ComplexFloat → ComplexFloat) (op : Float → Float → Float)
    (z : ComplexFloat) (x y : Vec n) : ComplexFloat :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    accLoop p op x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hs n.toUSize (x.toNat_toUSize hs.1)
      0 z.re z.im
  else Nat.fold n (fun l _ s => opC op s (mul (p x[l]) y[l])) z

public theorem acc_eq (p : ComplexFloat → ComplexFloat) (op : Float → Float → Float)
    (z : ComplexFloat) (x y : Vec n) :
    acc p op z x y = Nat.fold n (fun l _ s => opC op s (mul (p x[l]) y[l])) z := by
  unfold acc
  split
  · exact accLoop_eq p op x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl _ _ _ _ _ _ z 0 (by simp)
      (by lia) (by simp)
  · rfl

/--
The sum `z` combined by `op` with the products `mul (p x[l]) y[l]` for `l = n - 1, …, 0`, by
`accRevLoop`.
-/
@[inline] public def accRev (p : ComplexFloat → ComplexFloat) (op : Float → Float → Float)
    (z : ComplexFloat) (x y : Vec n) : ComplexFloat :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    accRevLoop p op x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hs n.toUSize (x.toNat_toUSize hs.1)
      0 z.re z.im
  else Nat.fold n (fun t _ s => opC op s
    (mul (p (x[n - 1 - t]'(by lia))) (y[n - 1 - t]'(by lia)))) z

public theorem accRev_eq (p : ComplexFloat → ComplexFloat) (op : Float → Float → Float)
    (z : ComplexFloat) (x y : Vec n) :
    accRev p op z x y = Nat.fold n (fun t _ s => opC op s
      (mul (p (x[n - 1 - t]'(by lia))) (y[n - 1 - t]'(by lia)))) z := by
  unfold accRev
  split
  · exact accRevLoop_eq p op x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl _ _ _ _ _ _ z 0 (by simp)
      (by lia) (by simp)
  · rfl

@[simp] public theorem opC_add (z w : ComplexFloat) : opC (· + ·) z w = z + w := rfl

@[simp] public theorem opC_sub (z w : ComplexFloat) : opC (· - ·) z w = z - w := rfl

/--
After `m` steps `g k` that each keep an invariant `inv k`, from `x` that has `inv 0`, the vector
has `inv m`.
-/
public theorem getElem_fold_of_inv {m : Nat} (g : (k : Nat) → k < m → Vec n → Vec n)
    (inv : Nat → (i : Nat) → i < n → ComplexFloat) (x : Vec n)
    (h0 : ∀ i hi, x[i] = inv 0 i hi)
    (hg : ∀ k hk (y : Vec n), (∀ i hi, y[i] = inv k i hi) →
      ∀ i hi, (g k hk y)[i] = inv (k + 1) i hi) :
    ∀ k (hk : k ≤ m) i hi, (Nat.fold k (fun j hj y => g j (by lia) y) x)[i] = inv k i hi
  | 0, _ => by simpa using h0
  | k + 1, hk => by
    rw [Nat.fold_succ]
    exact hg k (by lia) _ (getElem_fold_of_inv g inv x h0 hg k (by lia))

end Vec

namespace Mat

variable {n : Nat}

/-- `v` times the diagonal element `a`, unless the diagonal is unit. -/
@[expose] public def diagMul : Float64.Diag → ComplexFloat → ComplexFloat → ComplexFloat
  | .unit, v, _ => v
  | .nonUnit, v, a => mul v a

/-- `v` divided by the diagonal element `a` (`div`), unless the diagonal is unit. -/
@[expose] public def diagDiv : Float64.Diag → ComplexFloat → ComplexFloat → ComplexFloat
  | .unit, v, _ => v
  | .nonUnit, v, a => div v a

/-- `y` with the elements `lo ≤ i < lo + len` updated by `+ mul t A[i, j]`, in place. -/
@[inline] public def addCol (A : Mat n n) (j : Nat) (hj : j < n) (lo len : Nat)
    (h : lo + len ≤ n) (t : ComplexFloat) (y : Vec n) : Vec n :=
  y.withSlice lo len h (fun s => Vec.axpyData t ((A.col j hj).slice lo len h) s)
    (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])

public theorem getElem_addCol (A : Mat n n) (j : Nat) (hj : j < n) (lo len : Nat)
    (h : lo + len ≤ n) (t : ComplexFloat) (y : Vec n) (i : Nat) (hi : i < n) :
    (A.addCol j hj lo len h t y)[i] =
      if lo ≤ i ∧ i < lo + len then y[i] + mul t A[(i, j)] else y[i] := by
  unfold addCol
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.axpyData_eq ..)]
  split
  · simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col]
    have e : lo + (i - lo) = i := by lia
    simp only [e]
    rfl
  · rfl

/-- `y` with the elements `lo ≤ i < lo + len` updated by `- mul t A[i, j]`, in place. -/
@[inline] public def subCol (A : Mat n n) (j : Nat) (hj : j < n) (lo len : Nat)
    (h : lo + len ≤ n) (t : ComplexFloat) (y : Vec n) : Vec n :=
  y.withSlice lo len h
    (fun s => Vec.zipWithData (fun v a => v.re - mulRe t a) (fun v a => v.im - mulIm t a)
      ((A.col j hj).slice lo len h) s)
    (fun s => by rw [Vec.size_zipWithData])

public theorem getElem_subCol (A : Mat n n) (j : Nat) (hj : j < n) (lo len : Nat)
    (h : lo + len ≤ n) (t : ComplexFloat) (y : Vec n) (i : Nat) (hi : i < n) :
    (A.subCol j hj lo len h t y)[i] =
      if lo ≤ i ∧ i < lo + len then y[i] - mul t A[(i, j)] else y[i] := by
  unfold subCol
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  split
  · simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, getElem_col,
      mulRe_eq, mulIm_eq]
    have e : lo + (i - lo) = i := by lia
    simp only [e]
    rfl
  · rfl

/-- Element `(i, j)` of `A`, or `0` outside `A`. -/
@[expose] public def get0 (A : Mat n n) (i j : Nat) : ComplexFloat :=
  if h : i < n ∧ j < n then A[(i, j)] else zero

@[simp] public theorem get0_eq (A : Mat n n) {i j : Nat} (h : i < n ∧ j < n) :
    A.get0 i j = A[(i, j)] := by
  simp [get0, h]

private theorem mgetElem_eq_of_eq (A : Mat n n) {i i' j : Nat} (e : i = i')
    (h : i < n ∧ j < n) : A[(i, j)] = A[(i', j)]'(e ▸ h) := by
  subst e; rfl

private theorem vget0_eq (x : Vec n) {i : Nat} (h : i < n) : x.get0 i = x[i] := by
  simp [Vec.get0, h]

/-! ## `trmv` -/

/-- The step of `trmv .upper` for column `j`: add `x[j]` times the column above the diagonal. -/
@[expose] public def trmvUpperCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (x : Vec n) : Vec n :=
  let t := x[j]
  let x := A.addCol j hj 0 j (by lia) t x
  x.set j hj (diagMul d x[j] A[(j, j)])

/-- The step of `trmv .lower` for column `j`: add `x[j]` times the column below the diagonal. -/
@[expose] public def trmvLowerCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (x : Vec n) : Vec n :=
  let t := x[j]
  let x := A.addCol j hj (j + 1) (n - (j + 1)) (by lia) t x
  x.set j hj (diagMul d x[j] A[(j, j)])

/--
`trmv uplo d A x` is `A * x` for the triangle `uplo` of `A`, with a unit diagonal if `d` is
`.unit`, by the loops of `ztrmv`: for the upper triangle, for `j = 0, …, n - 1`, it adds
`mul x[j] A[i, j]` to the elements `i < j` and then multiplies `x[j]` by `A[j, j]`; for the lower
triangle, it does the same from `j = n - 1` down to `0`, for the elements below the diagonal.
-/
@[expose] public def trmv (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun j hj x => trmvUpperCol d A j hj x) x
  | .lower => Nat.fold n (fun k hk x => trmvLowerCol d A (n - 1 - k) (by lia) x) x

private theorem getElem_trmvUpperCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (y : Vec n) (i : Nat) (hi : i < n) :
    (trmvUpperCol d A j hj y)[i] =
      if i = j then diagMul d y[j] A[(j, j)]
      else if i < j then y[i] + mul y[j] A[(i, j)] else y[i] := by
  simp only [trmvUpperCol, Vec.getElem_set, getElem_addCol]
  by_cases e : i = j
  · subst e; simp
  · simp [e]

private theorem getElem_trmvLowerCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (y : Vec n) (i : Nat) (hi : i < n) :
    (trmvLowerCol d A j hj y)[i] =
      if i = j then diagMul d y[j] A[(j, j)]
      else if j < i then y[i] + mul y[j] A[(i, j)] else y[i] := by
  simp only [trmvLowerCol, Vec.getElem_set, getElem_addCol]
  by_cases e : i = j
  · subst e; simp [show ¬(i + 1 ≤ i) by lia]
  · have : (j + 1 ≤ i ∧ i < j + 1 + (n - (j + 1))) = (j < i) := by apply propext; lia
    simp [e, this]

private theorem getElem_trmv_upper' (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trmvUpperCol d A j (by lia) x) x)[i] =
        if i < k then Nat.fold (k - 1 - i) (fun t _ s => s + mul (x.get0 (i + 1 + t))
          (A.get0 i (i + 1 + t))) (diagMul d x[i] A[(i, i)])
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trmvUpperCol d A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro k hk y hy i hi
      have hyk := hy k hk
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyk
      rw [getElem_trmvUpperCol, hyk, hy i hi]
      by_cases e : i = k
      · subst e
        rw [Nat.fold_congr (show i + 1 - 1 - i = 0 by lia)]
        simp
      · by_cases h : i < k
        · simp only [e, h, show i < k + 1 by lia, ↓reduceIte]
          rw [Nat.fold_congr (show k + 1 - 1 - i = (k - 1 - i) + 1 by lia), Nat.fold_succ]
          rw [show i + 1 + (k - 1 - i) = k by lia, vget0_eq x hk, get0_eq A ⟨hi, hk⟩]
        · simp [e, h, show ¬i < k + 1 by lia])

private theorem getElem_trmv_lower' (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trmvLowerCol d A (n - 1 - j) (by lia) x) x)[i] =
        if n - k ≤ i then Nat.fold (i - (n - k)) (fun t _ s => s + mul (x.get0 (i - 1 - t))
          (A.get0 i (i - 1 - t))) (diagMul d x[i] A[(i, i)])
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trmvLowerCol d A (n - 1 - j) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro k hk y hy i hi
      have hyk := hy (n - 1 - k) (by lia)
      simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hyk
      rw [getElem_trmvLowerCol, hyk, hy i hi]
      by_cases e : i = n - 1 - k
      · subst e
        rw [Nat.fold_congr (show n - 1 - k - (n - (k + 1)) = 0 by lia)]
        simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · by_cases h : n - k ≤ i
        · simp only [e, h, show n - (k + 1) ≤ i by lia, show n - 1 - k < i by lia, ↓reduceIte]
          rw [Nat.fold_congr (show i - (n - (k + 1)) = (i - (n - k)) + 1 by lia), Nat.fold_succ]
          rw [show i - 1 - (i - (n - k)) = n - 1 - k by lia, vget0_eq x (by lia),
            get0_eq A ⟨hi, by lia⟩]
        · simp [e, h, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k < i by lia])

/--
Element `i` of `trmv .upper d A x` is `x[i]` times `A[i, i]` (unless the diagonal is unit), plus
the terms `mul x[j] A[i, j]` for `j = i + 1, …, n - 1`, in this order.
-/
public theorem getElem_trmv_upper (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (hi : i < n) :
    (trmv .upper d A x)[i] = Nat.fold (n - 1 - i) (fun t _ s =>
      s + mul (x[i + 1 + t]'(by lia)) (A[(i, i + 1 + t)]'⟨hi, by lia⟩))
        (diagMul d x[i] A[(i, i)]) := by
  rw [trmv, getElem_trmv_upper' d A x n (Nat.le_refl _) i hi, ite_eq_left hi]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), get0_eq A ⟨hi, by lia⟩]

/--
Element `i` of `trmv .lower d A x` is `x[i]` times `A[i, i]` (unless the diagonal is unit), plus
the terms `mul x[j] A[i, j]` for `j = i - 1, …, 0`, in this order.
-/
public theorem getElem_trmv_lower (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (hi : i < n) :
    (trmv .lower d A x)[i] = Nat.fold i (fun t _ s =>
      s + mul (x[i - 1 - t]'(by lia)) (A[(i, i - 1 - t)]'⟨hi, by lia⟩))
        (diagMul d x[i] A[(i, i)]) := by
  rw [trmv, getElem_trmv_lower' d A x n (Nat.le_refl _) i hi, ite_eq_left (by lia),
    Nat.sub_self, Nat.sub_zero]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), get0_eq A ⟨hi, by lia⟩]

/-! ## `trmvT` and `trmvC` -/

/--
The step of `trmvTWith p .upper` for column `j`: `x[j]` becomes `x[j]` times `p A[j, j]`, plus
`mul (p A[i, j]) x[i]` for `i = j - 1, …, 0`.
-/
@[expose, specialize] public def trmvTUpperCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := Vec.accRev p (· + ·) (diagMul d x[j] (p A[(j, j)])) ((A.col j hj).slice 0 j (by lia))
    (x.slice 0 j (by lia))
  x.set j hj t

/--
The step of `trmvTWith p .lower` for column `j`: `x[j]` becomes `x[j]` times `p A[j, j]`, plus
`mul (p A[i, j]) x[i]` for `i = j + 1, …, n - 1`.
-/
@[expose, specialize] public def trmvTLowerCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := Vec.acc p (· + ·) (diagMul d x[j] (p A[(j, j)]))
    ((A.col j hj).slice (j + 1) (n - (j + 1)) (by lia)) (x.slice (j + 1) (n - (j + 1)) (by lia))
  x.set j hj t

/--
`trmvTWith p uplo d A x` is the product of `x` by the transpose of the triangle `uplo` of `A`,
with each element of `A` mapped by `p`, by the loops of `ztrmv`: for the upper triangle, from
`j = n - 1` down to `0`, and for the lower triangle, for `j = 0, …, n - 1`, it sets `x[j]` to
`x[j]` times `p A[j, j]` (unless the diagonal is unit) plus the terms `mul (p A[i, j]) x[i]` of
the other elements of column `j` in the triangle, from the diagonal outwards.
-/
@[expose, specialize] public def trmvTWith (p : ComplexFloat → ComplexFloat) (uplo : Float64.Uplo)
    (d : Float64.Diag) (A : Mat n n) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun k hk x => trmvTUpperCol p d A (n - 1 - k) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => trmvTLowerCol p d A j hj x) x

private theorem getElem_trmvT_upper' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trmvTUpperCol p d A (n - 1 - j) (by lia) x) x)[i] =
        if n - k ≤ i then Nat.fold i (fun t _ s => s + mul (p (A.get0 (i - 1 - t) i))
          (x.get0 (i - 1 - t))) (diagMul d x[i] (p A[(i, i)]))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trmvTUpperCol p d A (n - 1 - j) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro k hk y hy i hi
      simp only [trmvTUpperCol, Vec.getElem_set]
      by_cases e : i = n - 1 - k
      · subst e
        have hyk := hy (n - 1 - k) (by lia)
        simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hyk
        simp only [↓reduceIte, show n - (k + 1) ≤ n - 1 - k by lia, Vec.accRev_eq, hyk,
          Vec.opC_add]
        congr 1; funext t ht s
        have hl : n - 1 - k - 1 - t < n - k := by lia
        have hyl := hy (n - 1 - k - 1 - t) (by lia)
        simp only [show ¬n - k ≤ n - 1 - k - 1 - t by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col, Nat.zero_add, hyl,
          vget0_eq x (show n - 1 - k - 1 - t < n by lia),
          get0_eq A (i := n - 1 - k - 1 - t) (j := n - 1 - k) ⟨by lia, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : n - k ≤ i
        · simp [h, show n - (k + 1) ≤ i by lia]
        · simp [h, show ¬n - (k + 1) ≤ i by lia])

private theorem getElem_trmvT_lower' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trmvTLowerCol p d A j (by lia) x) x)[i] =
        if i < k then Nat.fold (n - 1 - i) (fun t _ s => s + mul (p (A.get0 (i + 1 + t) i))
          (x.get0 (i + 1 + t))) (diagMul d x[i] (p A[(i, i)]))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trmvTLowerCol p d A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro k hk y hy i hi
      simp only [trmvTLowerCol, Vec.getElem_set]
      by_cases e : i = k
      · subst e
        have hyk := hy i hk
        simp only [Nat.lt_irrefl, ↓reduceIte] at hyk
        simp only [↓reduceIte, Nat.lt_add_one, Vec.acc_eq, hyk, Vec.opC_add]
        rw [Nat.fold_congr (show n - (i + 1) = n - 1 - i by lia)]
        congr 1; funext t ht s
        have hyl := hy (i + 1 + t) (by lia)
        simp only [show ¬i + 1 + t < i by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col, hyl, vget0_eq x (show i + 1 + t < n by lia),
          get0_eq A (i := i + 1 + t) (j := i) ⟨by lia, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : i < k
        · simp [h, show i < k + 1 by lia]
        · simp [h, show ¬i < k + 1 by lia])

/--
Element `j` of `trmvTWith p .upper d A x` is `x[j]` times `p A[j, j]` (unless the diagonal is
unit), plus the terms `mul (p A[i, j]) x[i]` for `i = j - 1, …, 0`, in this order.
-/
public theorem getElem_trmvTWith_upper (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trmvTWith p .upper d A x)[j] = Nat.fold j (fun t _ s =>
      s + mul (p (A[(j - 1 - t, j)]'⟨by lia, hj⟩)) (x[j - 1 - t]'(by lia)))
        (diagMul d x[j] (p A[(j, j)])) := by
  rw [trmvTWith, getElem_trmvT_upper' p d A x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), get0_eq A ⟨by lia, hj⟩]

/--
Element `j` of `trmvTWith p .lower d A x` is `x[j]` times `p A[j, j]` (unless the diagonal is
unit), plus the terms `mul (p A[i, j]) x[i]` for `i = j + 1, …, n - 1`, in this order.
-/
public theorem getElem_trmvTWith_lower (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trmvTWith p .lower d A x)[j] = Nat.fold (n - 1 - j) (fun t _ s =>
      s + mul (p (A[(j + 1 + t, j)]'⟨by lia, hj⟩)) (x[j + 1 + t]'(by lia)))
        (diagMul d x[j] (p A[(j, j)])) := by
  rw [trmvTWith, getElem_trmvT_lower' p d A x n (Nat.le_refl _) j hj, ite_eq_left hj]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), get0_eq A ⟨by lia, hj⟩]

/-- `trmvT uplo d A x` is `Aᵀ * x` for the triangle `uplo` of `A`, as `ztrmv` with `'T'`. -/
@[expose] public def trmvT (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    Vec n :=
  trmvTWith id uplo d A x

/--
`trmvC uplo d A x` is `Aᴴ * x` for the triangle `uplo` of `A`, as `ztrmv` with `'C'`: the
elements of `A` are conjugated.
-/
@[expose] public def trmvC (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    Vec n :=
  trmvTWith ComplexFloat.conj uplo d A x


/-! ## `trsv` -/

/--
Element `i` of the solution of `A * y = x` for the lower triangle of `A`: `x[i]`, minus the terms
`mul y[l] A[i, l]` for `l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal is unit.
-/
@[expose] public def trsvLowerM (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat) :
    ComplexFloat :=
  diagDiv d (Nat.fold i (fun l _hl s => s - mul (trsvLowerM d A x l) (A.get0 i l)) (x.get0 i))
    (A.get0 i i)
termination_by i
decreasing_by exact _hl

/--
Element `i` of the solution of `A * y = x` for the upper triangle of `A`: `x[i]`, minus the terms
`mul y[l] A[i, l]` for `l = n - 1, …, i + 1`, divided by `A[i, i]` unless the diagonal is unit.
-/
@[expose] public def trsvUpperM (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat) :
    ComplexFloat :=
  diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul (trsvUpperM d A x (n - 1 - t)) (A.get0 i (n - 1 - t))) (x.get0 i)) (A.get0 i i)
termination_by n - i
decreasing_by lia

/-- The step of `trsv .lower` for column `j`: solve for `x[j]`, and update the elements below. -/
@[expose] public def trsvLowerCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (x : Vec n) : Vec n :=
  let t := diagDiv d x[j] A[(j, j)]
  let x := x.set j hj t
  A.subCol j hj (j + 1) (n - (j + 1)) (by lia) t x

/-- The step of `trsv .upper` for column `j`: solve for `x[j]`, and update the elements above. -/
@[expose] public def trsvUpperCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (x : Vec n) : Vec n :=
  let t := diagDiv d x[j] A[(j, j)]
  let x := x.set j hj t
  A.subCol j hj 0 j (by lia) t x

/--
`trsv uplo d A x` solves `A * y = x` for the triangle `uplo` of `A`, with a unit diagonal if `d`
is `.unit`, by the loops of `ztrsv`: for the lower triangle, for `j = 0, …, n - 1`, it divides
`x[j]` by `A[j, j]` (`div`) and subtracts `mul x[j] A[i, j]` from the elements `i > j`; for the
upper triangle, it does the same from `j = n - 1` down to `0`, for the elements `i < j`. Like the
reference BLAS, it doesn't check for a zero on the diagonal.
-/
@[expose] public def trsv (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun k hk x => trsvUpperCol d A (n - 1 - k) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => trsvLowerCol d A j hj x) x

private theorem getElem_trsvLowerCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (y : Vec n) (i : Nat) (hi : i < n) :
    (trsvLowerCol d A j hj y)[i] =
      if i = j then diagDiv d y[j] A[(j, j)]
      else if j < i then y[i] - mul (diagDiv d y[j] A[(j, j)]) A[(i, j)] else y[i] := by
  simp only [trsvLowerCol, getElem_subCol, Vec.getElem_set]
  by_cases e : i = j
  · subst e; simp [show ¬(i + 1 ≤ i) by lia]
  · have : (j + 1 ≤ i ∧ i < j + 1 + (n - (j + 1))) = (j < i) := by apply propext; lia
    simp [e, this]

private theorem getElem_trsvUpperCol (d : Float64.Diag) (A : Mat n n) (j : Nat) (hj : j < n)
    (y : Vec n) (i : Nat) (hi : i < n) :
    (trsvUpperCol d A j hj y)[i] =
      if i = j then diagDiv d y[j] A[(j, j)]
      else if i < j then y[i] - mul (diagDiv d y[j] A[(j, j)]) A[(i, j)] else y[i] := by
  simp only [trsvUpperCol, getElem_subCol, Vec.getElem_set]
  by_cases e : i = j
  · subst e; simp
  · simp [e]

private theorem trsvLowerM_eq (d : Float64.Diag) (A : Mat n n) (x : Vec n) {i : Nat}
    (hi : i < n) :
    trsvLowerM d A x i = diagDiv d (Nat.fold i (fun l _ s =>
      s - mul (trsvLowerM d A x l) (A.get0 i l)) x[i]) A[(i, i)] := by
  rw [trsvLowerM, vget0_eq x hi, get0_eq A ⟨hi, hi⟩]

private theorem trsvUpperM_eq (d : Float64.Diag) (A : Mat n n) (x : Vec n) {i : Nat}
    (hi : i < n) :
    trsvUpperM d A x i = diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul (trsvUpperM d A x (n - 1 - t)) (A.get0 i (n - 1 - t))) x[i]) A[(i, i)] := by
  rw [trsvUpperM, vget0_eq x hi, get0_eq A ⟨hi, hi⟩]

private theorem getElem_trsv_lower' (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvLowerCol d A j (by lia) x) x)[i] =
        if i < k then trsvLowerM d A x i
        else Nat.fold k (fun l _ s => s - mul (trsvLowerM d A x l) (A.get0 i l)) x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvLowerCol d A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro k hk y hy i hi
      have hyk := hy k hk
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyk
      have ht : diagDiv d y[k] A[(k, k)] = trsvLowerM d A x k := by
        rw [hyk, trsvLowerM_eq d A x hk]
      rw [getElem_trsvLowerCol, ht, hy i hi]
      by_cases e : i = k
      · subst e; simp
      · by_cases h : i < k
        · simp [e, h, show i < k + 1 by lia, show ¬k < i by lia]
        · simp only [e, h, show k < i by lia, show ¬i < k + 1 by lia, ↓reduceIte, Nat.fold_succ]
          rw [get0_eq A ⟨hi, hk⟩])

private theorem getElem_trsv_upper' (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvUpperCol d A (n - 1 - j) (by lia) x) x)[i] =
        if n - k ≤ i then trsvUpperM d A x i
        else Nat.fold k (fun t _ s =>
          s - mul (trsvUpperM d A x (n - 1 - t)) (A.get0 i (n - 1 - t))) x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvUpperCol d A (n - 1 - j) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro k hk y hy i hi
      have hyk := hy (n - 1 - k) (by lia)
      simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hyk
      have ht : diagDiv d y[n - 1 - k] A[(n - 1 - k, n - 1 - k)] =
          trsvUpperM d A x (n - 1 - k) := by
        rw [hyk, trsvUpperM_eq d A x (by lia),
          Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
      rw [getElem_trsvUpperCol, ht, hy i hi]
      by_cases e : i = n - 1 - k
      · subst e; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · by_cases h : n - k ≤ i
        · simp [e, h, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k by lia]
        · simp only [e, h, show i < n - 1 - k by lia, show ¬n - (k + 1) ≤ i by lia, ↓reduceIte,
            Nat.fold_succ]
          rw [get0_eq A (i := i) (j := n - 1 - k) ⟨hi, by lia⟩])

/-- Element `i` of `trsv .lower d A x` is element `i` of the model `trsvLowerM`. -/
public theorem getElem_trsv_lower_eq (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (hi : i < n) : (trsv .lower d A x)[i] = trsvLowerM d A x i := by
  rw [trsv, getElem_trsv_lower' d A x n (Nat.le_refl _) i hi, ite_eq_left hi]

/-- Element `i` of `trsv .upper d A x` is element `i` of the model `trsvUpperM`. -/
public theorem getElem_trsv_upper_eq (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (hi : i < n) : (trsv .upper d A x)[i] = trsvUpperM d A x i := by
  rw [trsv, getElem_trsv_upper' d A x n (Nat.le_refl _) i hi, ite_eq_left (by lia)]

/--
Element `i` of `y = trsv .lower d A x` is `x[i]`, minus the terms `mul y[l] A[i, l]` for
`l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal is unit: forward substitution, in the
order of the loops.
-/
public theorem getElem_trsv_lower (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (hi : i < n) :
    (trsv .lower d A x)[i] = diagDiv d (Nat.fold i (fun l hl s =>
      s - mul ((trsv .lower d A x)[l]'(by lia)) (A[(i, l)]'⟨hi, by lia⟩)) x[i]) A[(i, i)] := by
  rw [getElem_trsv_lower_eq d A x i hi, trsvLowerM_eq d A x hi]
  congr 1; congr 1; funext l hl s
  rw [getElem_trsv_lower_eq d A x l (by lia), get0_eq A (i := i) (j := l) ⟨hi, by lia⟩]

/--
Element `i` of `y = trsv .upper d A x` is `x[i]`, minus the terms `mul y[l] A[i, l]` for
`l = n - 1, …, i + 1`, divided by `A[i, i]` unless the diagonal is unit: back substitution, in
the order of the loops.
-/
public theorem getElem_trsv_upper (d : Float64.Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (hi : i < n) :
    (trsv .upper d A x)[i] = diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul ((trsv .upper d A x)[n - 1 - t]'(by lia)) (A[(i, n - 1 - t)]'⟨hi, by lia⟩)) x[i])
        A[(i, i)] := by
  rw [getElem_trsv_upper_eq d A x i hi, trsvUpperM_eq d A x hi]
  congr 1; congr 1; funext t ht s
  rw [getElem_trsv_upper_eq d A x (n - 1 - t) (by lia),
    get0_eq A (i := i) (j := n - 1 - t) ⟨hi, by lia⟩]

/-! ## `trsvT` and `trsvC` -/

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the upper triangle of `A`: `x[j]`, minus the
terms `mul (p A[l, j]) y[l]` for `l = 0, …, j - 1`, divided by `p A[j, j]` unless the diagonal is
unit.
-/
@[expose] public def trsvTUpperM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold j (fun l _hl s => s - mul (p (A.get0 l j)) (trsvTUpperM p d A x l))
    (x.get0 j)) (p (A.get0 j j))
termination_by j
decreasing_by exact _hl

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the lower triangle of `A`: `x[j]`, minus the
terms `mul (p A[l, j]) y[l]` for `l = n - 1, …, j + 1`, divided by `p A[j, j]` unless the
diagonal is unit.
-/
@[expose] public def trsvTLowerM (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) : ComplexFloat :=
  diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (A.get0 (n - 1 - t) j)) (trsvTLowerM p d A x (n - 1 - t))) (x.get0 j))
    (p (A.get0 j j))
termination_by n - j
decreasing_by lia

/-- The step of `trsvTWith p .upper` for column `j`: solve for `x[j]` from the elements above. -/
@[expose, specialize] public def trsvTUpperCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d (Vec.acc p (· - ·) x[j] ((A.col j hj).slice 0 j (by lia))
    (x.slice 0 j (by lia))) (p A[(j, j)])
  x.set j hj t

/-- The step of `trsvTWith p .lower` for column `j`: solve for `x[j]` from the elements below. -/
@[expose, specialize] public def trsvTLowerCol (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d (Vec.accRev p (· - ·) x[j]
    ((A.col j hj).slice (j + 1) (n - (j + 1)) (by lia)) (x.slice (j + 1) (n - (j + 1)) (by lia)))
    (p A[(j, j)])
  x.set j hj t

/--
`trsvTWith p uplo d A x` solves `(p A)ᵀ * y = x` for the triangle `uplo` of `A`, where `p A`
maps each element of `A` by `p`, by the loops of `ztrsv`: for the upper triangle, for
`j = 0, …, n - 1`, it subtracts the terms `mul (p A[i, j]) x[i]` for `i = 0, …, j - 1` from
`x[j]` and divides it by `p A[j, j]` (`div`); for the lower triangle, it does the same from
`j = n - 1` down to `0`, with the terms for `i = n - 1, …, j + 1`.
-/
@[expose, specialize] public def trsvTWith (p : ComplexFloat → ComplexFloat) (uplo : Float64.Uplo)
    (d : Float64.Diag) (A : Mat n n) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun j hj x => trsvTUpperCol p d A j hj x) x
  | .lower => Nat.fold n (fun k hk x => trsvTLowerCol p d A (n - 1 - k) (by lia) x) x

private theorem trsvTUpperM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) {j : Nat} (hj : j < n) :
    trsvTUpperM p d A x j = diagDiv d (Nat.fold j (fun l _ s =>
      s - mul (p (A.get0 l j)) (trsvTUpperM p d A x l)) x[j]) (p A[(j, j)]) := by
  rw [trsvTUpperM, vget0_eq x hj, get0_eq A ⟨hj, hj⟩]

private theorem trsvTLowerM_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) {j : Nat} (hj : j < n) :
    trsvTLowerM p d A x j = diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (A.get0 (n - 1 - t) j)) (trsvTLowerM p d A x (n - 1 - t)))
        x[j]) (p A[(j, j)]) := by
  rw [trsvTLowerM, vget0_eq x hj, get0_eq A ⟨hj, hj⟩]

private theorem getElem_trsvT_upper' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvTUpperCol p d A j (by lia) x) x)[i] =
        if i < k then trsvTUpperM p d A x i else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvTUpperCol p d A j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro k hk y hy i hi
      simp only [trsvTUpperCol, Vec.getElem_set]
      by_cases e : i = k
      · subst e
        have hyk := hy i hk
        simp only [Nat.lt_irrefl, ↓reduceIte] at hyk
        simp only [↓reduceIte, Nat.lt_add_one, Vec.acc_eq, hyk, Vec.opC_sub,
          trsvTUpperM_eq p d A x hk]
        congr 1; congr 1; funext l hl s
        have hyl := hy l (by lia)
        simp only [hl, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col, Nat.zero_add, hyl,
          get0_eq A (i := l) (j := i) ⟨by lia, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : i < k
        · simp [h, show i < k + 1 by lia]
        · simp [h, show ¬i < k + 1 by lia])

private theorem getElem_trsvT_lower' (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) :
    ∀ k (hk : k ≤ n) i (hi : i < n),
      (Nat.fold k (fun j hj x => trsvTLowerCol p d A (n - 1 - j) (by lia) x) x)[i] =
        if n - k ≤ i then trsvTLowerM p d A x i else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => trsvTLowerCol p d A (n - 1 - j) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro k hk y hy i hi
      simp only [trsvTLowerCol, Vec.getElem_set]
      by_cases e : i = n - 1 - k
      · subst e
        have hyk := hy (n - 1 - k) (by lia)
        simp only [show ¬n - k ≤ n - 1 - k by lia, ↓reduceIte] at hyk
        simp only [↓reduceIte, show n - (k + 1) ≤ n - 1 - k by lia, Vec.accRev_eq, hyk,
          Vec.opC_sub, trsvTLowerM_eq p d A x hi]
        rw [Nat.fold_congr (show n - (n - 1 - k + 1) = n - 1 - (n - 1 - k) by lia)]
        congr 1; congr 1; funext t ht s
        have hl : n - 1 - k + 1 + (n - (n - 1 - k + 1) - 1 - t) = n - 1 - t := by lia
        have hyl := hy (n - 1 - t) (by lia)
        simp only [show n - k ≤ n - 1 - t by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice, getElem_col]
        rw [Vec.getElem_eq_of_eq _ hl, hyl, mgetElem_eq_of_eq A hl,
          get0_eq A (i := n - 1 - t) (j := n - 1 - k) ⟨by lia, hi⟩]
      · rw [ite_eq_right e, hy]
        by_cases h : n - k ≤ i
        · simp [h, show n - (k + 1) ≤ i by lia]
        · simp [h, show ¬n - (k + 1) ≤ i by lia])

/-- Element `j` of `trsvTWith p .upper d A x` is element `j` of the model `trsvTUpperM`. -/
public theorem getElem_trsvTWith_upper_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trsvTWith p .upper d A x)[j] = trsvTUpperM p d A x j := by
  rw [trsvTWith, getElem_trsvT_upper' p d A x n (Nat.le_refl _) j hj, ite_eq_left hj]

/-- Element `j` of `trsvTWith p .lower d A x` is element `j` of the model `trsvTLowerM`. -/
public theorem getElem_trsvTWith_lower_eq (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trsvTWith p .lower d A x)[j] = trsvTLowerM p d A x j := by
  rw [trsvTWith, getElem_trsvT_lower' p d A x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]

/--
Element `j` of `y = trsvTWith p .upper d A x` is `x[j]`, minus the terms `mul (p A[l, j]) y[l]`
for `l = 0, …, j - 1`, divided by `p A[j, j]` unless the diagonal is unit.
-/
public theorem getElem_trsvTWith_upper (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trsvTWith p .upper d A x)[j] = diagDiv d (Nat.fold j (fun l hl s =>
      s - mul (p (A[(l, j)]'⟨by lia, hj⟩)) ((trsvTWith p .upper d A x)[l]'(by lia))) x[j])
        (p A[(j, j)]) := by
  rw [getElem_trsvTWith_upper_eq p d A x j hj, trsvTUpperM_eq p d A x hj]
  congr 1; congr 1; funext l hl s
  rw [getElem_trsvTWith_upper_eq p d A x l (by lia), get0_eq A (i := l) (j := j) ⟨by lia, hj⟩]

/--
Element `j` of `y = trsvTWith p .lower d A x` is `x[j]`, minus the terms `mul (p A[l, j]) y[l]`
for `l = n - 1, …, j + 1`, divided by `p A[j, j]` unless the diagonal is unit.
-/
public theorem getElem_trsvTWith_lower (p : ComplexFloat → ComplexFloat) (d : Float64.Diag)
    (A : Mat n n) (x : Vec n) (j : Nat) (hj : j < n) :
    (trsvTWith p .lower d A x)[j] = diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (A[(n - 1 - t, j)]'⟨by lia, hj⟩))
        ((trsvTWith p .lower d A x)[n - 1 - t]'(by lia))) x[j]) (p A[(j, j)]) := by
  rw [getElem_trsvTWith_lower_eq p d A x j hj, trsvTLowerM_eq p d A x hj]
  congr 1; congr 1; funext t ht s
  rw [getElem_trsvTWith_lower_eq p d A x (n - 1 - t) (by lia),
    get0_eq A (i := n - 1 - t) (j := j) ⟨by lia, hj⟩]

/-- `trsvT uplo d A x` solves `Aᵀ * y = x` for the triangle `uplo` of `A`, as `ztrsv` with `'T'`. -/
@[expose] public def trsvT (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    Vec n :=
  trsvTWith id uplo d A x

/--
`trsvC uplo d A x` solves `Aᴴ * y = x` for the triangle `uplo` of `A`, as `ztrsv` with `'C'`: the
elements of `A` are conjugated.
-/
@[expose] public def trsvC (uplo : Float64.Uplo) (d : Float64.Diag) (A : Mat n n) (x : Vec n) :
    Vec n :=
  trsvTWith ComplexFloat.conj uplo d A x

end Mat

end BLAS.ComplexFloat64
