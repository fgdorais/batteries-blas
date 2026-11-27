/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Band
public import BatteriesBLAS.Float32.Spr
import all BatteriesBLAS.Internal

/-!
# Complex packed matrix-vector products, solves and updates

A packed triangle is stored as in the reference BLAS, as for the real packed routines: the upper
or lower triangle of a matrix of order `n`, packed by columns in a vector
`ap : Vec (n * (n + 1) / 2)`. Column `j` starts at `Float32.packedStart uplo n j`. In the upper
triangle (`.upper`) it holds the elements `0, …, j`, so the element `(i, j)` is at
`packedStart .upper n j + i`. In the lower triangle (`.lower`) it holds the elements `j, …, n - 1`,
so the element `(i, j)` is at `packedStart .lower n j + (i - j)`.

The routines are `hpmv` (`zhpmv`), `hpr` (`zhpr`) and `hpr2` (`zhpr2`), `tpmv`, `tpmvT` and
`tpmvC` (`ztpmv`), and `tpsv`, `tpsvT` and `tpsvC` (`ztpsv`). Each runs the loops of the reference
BLAS (`master`, which has no zero skips in `ztpmv` and `ztpsv`, and keeps those of `zhpr` and
`zhpr2`), with the same operations in the same order.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.ComplexFloat32

namespace Mat

variable {m n N : Nat}

/-! ## Updates of a vector by a slice of another -/

/--
`y` with the elements `lo ≤ i < lo + len` updated by `+ mul t c[ar + (i - lo)]`, in place: an
`axpy` of a slice of `c` into a slice of `y`.
-/
@[inline] public def addVecAt (c : Vec N) (ar lo len : Nat) (ha : ar + len ≤ N) (h : lo + len ≤ m)
    (t : ComplexFloat32) (y : Vec m) : Vec m :=
  y.withSlice lo len h (fun s => Vec.axpyData t (c.slice ar len ha) s)
    (fun s => by rw [Vec.axpyData_eq, size_modifyAt2])

public theorem getElem_addVecAt (c : Vec N) (ar lo len : Nat) (ha : ar + len ≤ N)
    (h : lo + len ≤ m) (t : ComplexFloat32) (y : Vec m) (i : Nat) (hi : i < m) :
    (addVecAt c ar lo len ha h t y)[i] =
      if hl : lo ≤ i ∧ i < lo + len then y[i] + mul t (c[ar + (i - lo)]'(by lia))
      else y[i] := by
  unfold addVecAt
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.axpyData_eq ..)]
  by_cases hl : lo ≤ i ∧ i < lo + len
  · simp only [hl, and_self, ↓reduceIte, ↓reduceDIte]
    simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice]
    rfl
  · simp only [hl, ↓reduceIte, ↓reduceDIte]

/-- `y` with the elements `lo ≤ i < lo + len` updated by `- mul t c[ar + (i - lo)]`, in place. -/
@[inline] public def subVecAt (c : Vec N) (ar lo len : Nat) (ha : ar + len ≤ N) (h : lo + len ≤ m)
    (t : ComplexFloat32) (y : Vec m) : Vec m :=
  y.withSlice lo len h
    (fun s => Vec.zipWithData (fun v a => v.re - mulRe t a) (fun v a => v.im - mulIm t a)
      (c.slice ar len ha) s)
    (fun s => by rw [Vec.size_zipWithData])

public theorem getElem_subVecAt (c : Vec N) (ar lo len : Nat) (ha : ar + len ≤ N)
    (h : lo + len ≤ m) (t : ComplexFloat32) (y : Vec m) (i : Nat) (hi : i < m) :
    (subVecAt c ar lo len ha h t y)[i] =
      if hl : lo ≤ i ∧ i < lo + len then y[i] - mul t (c[ar + (i - lo)]'(by lia))
      else y[i] := by
  unfold subVecAt
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.zipWithData_eq ..)]
  by_cases hl : lo ≤ i ∧ i < lo + len
  · simp only [hl, and_self, ↓reduceIte, ↓reduceDIte]
    simp only [Vec.get0, show i - lo < len by lia, ↓reduceDIte, Vec.getElem_slice, mulRe_eq,
      mulIm_eq]
    rfl
  · simp only [hl, ↓reduceIte, ↓reduceDIte]

/--
`a` with the elements `ar ≤ q < ar + len` updated by `+ mul v[lo + (q - ar)] t`, in place: the
update of a slice of a packed triangle by `axpyRData`.
-/
@[inline] public def axpyRAt (t : ComplexFloat32) (v : Vec m) (lo ar len : Nat) (h : lo + len ≤ m)
    (ha : ar + len ≤ N) (a : Vec N) : Vec N :=
  a.withSlice ar len ha (fun s => Vec.axpyRData t (v.slice lo len h) s)
    (fun s => by rw [Vec.axpyRData_eq, size_modifyAt2])

public theorem getElem_axpyRAt (t : ComplexFloat32) (v : Vec m) (lo ar len : Nat)
    (h : lo + len ≤ m) (ha : ar + len ≤ N) (a : Vec N) (q : Nat) (hq : q < N) :
    (axpyRAt t v lo ar len h ha a)[q] =
      if hl : ar ≤ q ∧ q < ar + len then a[q] + mul (v[lo + (q - ar)]'(by lia)) t else a[q] := by
  unfold axpyRAt
  rw [Vec.getElem_withSlice _ _ _ _ _ _ _ _ (Vec.axpyRData_eq ..)]
  by_cases hl : ar ≤ q ∧ q < ar + len
  · simp only [hl, and_self, ↓reduceIte, ↓reduceDIte]
    simp only [Vec.get0, show q - ar < len by lia, ↓reduceDIte, Vec.getElem_slice]
    rfl
  · simp only [hl, ↓reduceIte, ↓reduceDIte]

/-- `a` with element `q₀` replaced by `⟨g a[q₀].re, 0⟩`, in place. -/
@[inline] public def setReAt (q₀ : Nat) (hq₀ : q₀ < N) (g : Float32 → Float32) (a : Vec N) :
    Vec N :=
  a.withSlice q₀ 1 (by lia)
    (fun s => s.data.modifyStride2 s.reStride s.imStride 1 (fun u _ => g u) (fun _ _ => 0)
      s.fits_re s.fits_im) (fun _ => by simp)

public theorem getElem_setReAt (q₀ : Nat) (hq₀ : q₀ < N) (g : Float32 → Float32) (a : Vec N)
    (q : Nat) (hq : q < N) :
    (setReAt q₀ hq₀ g a)[q] = if q = q₀ then ⟨g a[q].re, 0⟩ else a[q] := by
  unfold setReAt
  rw [Vec.getElem_withSlice _ _ _ _ _ _ (fun _ u _ => g u) (fun _ _ _ => 0) (modifyStride2_eq ..)]
  have : (q₀ ≤ q ∧ q < q₀ + 1) = (q = q₀) := by apply propext; lia
  simp only [this]

/-! ## Packed storage -/

/-- The index in `ap` of the first element of column `j` other than the diagonal. -/
@[expose, inline] public def tpAr (uplo : Float32.Uplo) (n j : Nat) : Nat :=
  match uplo with
  | .upper => Float32.packedStart .upper n j
  | .lower => Float32.packedStart .lower n j + 1

/-- The first row of column `j` of the triangle other than the diagonal: `0` or `j + 1`. -/
@[expose, inline] public def tpLo : Float32.Uplo → Nat → Nat
  | .upper, _ => 0
  | .lower, j => j + 1

/-- The number of elements of column `j` of the triangle other than the diagonal. -/
@[expose, inline] public def tpLen : Float32.Uplo → Nat → Nat → Nat
  | .upper, _, j => j
  | .lower, n, j => n - 1 - j

/-- The index in `ap` of the element `(i, j)` of the triangle. -/
@[expose] public def tpIdx (uplo : Float32.Uplo) (n i j : Nat) : Nat :=
  match uplo with
  | .upper => Float32.packedStart .upper n j + i
  | .lower => Float32.packedStart .lower n j + (i - j)

/-- The element `(i, j)` of the triangle, `i ≤ j` for `.upper` and `i ≥ j` for `.lower`. -/
@[expose] public def InPTri (uplo : Float32.Uplo) (i j : Nat) : Prop :=
  (uplo = .upper ∧ i ≤ j) ∨ (uplo = .lower ∧ j ≤ i)

public instance (uplo : Float32.Uplo) (i j : Nat) : Decidable (InPTri uplo i j) := by
  unfold InPTri; infer_instance

private theorem upStart (n j : Nat) : Float32.packedStart .upper n j = j * (j + 1) / 2 := rfl

private theorem loStart (n j : Nat) :
    Float32.packedStart .lower n j = n * (n + 1) / 2 - (n - j) * (n - j + 1) / 2 := rfl

public theorem tpIdx_lt (uplo : Float32.Uplo) {n i j : Nat} (h : InPTri uplo i j) (hi : i < n)
    (hj : j < n) : tpIdx uplo n i j < n * (n + 1) / 2 := by
  cases uplo
  · have h' : i ≤ j := by simpa [InPTri] using h
    exact Float32.upIdx_lt h' hj
  · have h' : j ≤ i := by simpa [InPTri] using h
    exact Float32.loIdx_lt h' hi

public theorem inPTri_self (uplo : Float32.Uplo) (j : Nat) : InPTri uplo j j := by
  cases uplo <;> simp [InPTri]

public theorem inPTri_of_inTri {uplo : Float32.Uplo} {i j : Nat} (h : InTri uplo i j) :
    InPTri uplo i j := by
  simp only [InTri, InPTri] at *; lia

public theorem tpIdx_self_lt (uplo : Float32.Uplo) {n j : Nat} (hj : j < n) :
    tpIdx uplo n j j < n * (n + 1) / 2 :=
  tpIdx_lt uplo (inPTri_self uplo j) hj hj

public theorem tpLo_add_tpLen (uplo : Float32.Uplo) (n j : Nat) (hj : j < n) :
    tpLo uplo j + tpLen uplo n j ≤ n := by
  cases uplo <;> simp only [tpLo, tpLen] <;> lia

public theorem tpAr_add_tpLen (uplo : Float32.Uplo) {n j : Nat} (hj : j < n) :
    tpAr uplo n j + tpLen uplo n j ≤ n * (n + 1) / 2 := by
  cases uplo
  · have := Float32.upIdx_lt (Nat.le_refl j) hj
    simp only [Float32.upIdx] at this
    simp only [tpAr, tpLen, upStart]; lia
  · have := Float32.loIdx_lt (show j ≤ n - 1 by lia) (show n - 1 < n by lia)
    simp only [Float32.loIdx] at this
    simp only [tpAr, tpLen, loStart]; lia

public theorem mem_tp (uplo : Float32.Uplo) (n i j : Nat) (hi : i < n) (hj : j < n) :
    (tpLo uplo j ≤ i ∧ i < tpLo uplo j + tpLen uplo n j) ↔ InTri uplo i j := by
  cases uplo <;> simp only [tpLo, tpLen, InTri, reduceCtorEq, true_and, false_and, or_false,
    false_or] <;> lia

public theorem not_inTri_self (uplo : Float32.Uplo) (j : Nat) : ¬InTri uplo j j := by
  simp only [InTri]; lia

public theorem tpAr_add_sub (uplo : Float32.Uplo) (n i j : Nat) (h : InTri uplo i j) :
    tpAr uplo n j + (i - tpLo uplo j) = tpIdx uplo n i j := by
  cases uplo <;> simp only [tpAr, tpLo, tpIdx, InTri, reduceCtorEq, true_and, false_and,
    or_false, false_or] at * <;> lia

private theorem vget0_eq (x : Vec n) {i : Nat} (h : i < n) : x.get0 i = x[i] := by
  simp [Vec.get0, h]

/-- The element `(i, j)` of the packed triangle, or `0` outside the triangle, for the models. -/
@[expose] public def pget0 (uplo : Float32.Uplo) (ap : Vec (n * (n + 1) / 2)) (i j : Nat) :
    ComplexFloat32 :=
  if h : InPTri uplo i j ∧ i < n ∧ j < n then ap[tpIdx uplo n i j]'(tpIdx_lt uplo h.1 h.2.1 h.2.2)
  else zero

@[simp] public theorem pget0_eq (uplo : Float32.Uplo) (ap : Vec (n * (n + 1) / 2)) {i j : Nat}
    (h : InPTri uplo i j) (hi : i < n) (hj : j < n) :
    pget0 uplo ap i j = ap[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj) := by
  simp [pget0, h, hi, hj]

private theorem vget_eq (x : Vec n) {i i' : Nat} (e : i = i') (h : i < n) :
    x[i] = x[i']'(e ▸ h) := by
  subst e; rfl

/-! ## `hpmv` -/

/-- The `dotc` of column `j` of the packed Hermitian matrix, without the diagonal, with `x`. -/
@[inline] public def hpmvDot (uplo : Float32.Uplo) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (hj : j < n) : ComplexFloat32 :=
  Vec.acc ComplexFloat32.conj (· + ·) zero
    (ap.slice (tpAr uplo n j) (tpLen uplo n j) (tpAr_add_tpLen uplo hj))
    (x.slice (tpLo uplo j) (tpLen uplo n j) (tpLo_add_tpLen uplo n j hj))

/--
`hpmvDot` is the sum of the terms `mul (conj ap[tpAr uplo n j + l]) x[tpLo uplo j + l]`, for the
rows `tpLo uplo j + l` of column `j` off the diagonal, in increasing order.
-/
public theorem hpmvDot_eq (uplo : Float32.Uplo) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (j : Nat) (hj : j < n) :
    hpmvDot uplo ap x j hj = Nat.fold (tpLen uplo n j) (fun l hl s =>
      s + mul (ap[tpAr uplo n j + l]'(by have := tpAr_add_tpLen uplo hj; lia)).conj
        (x[tpLo uplo j + l]'(by have := tpLo_add_tpLen uplo n j hj; lia))) zero := by
  simp only [hpmvDot, Vec.acc_eq, Vec.opC_add, Vec.getElem_slice]

/-- The step of `hpmv` for column `j`, as `zhpmv`. -/
@[inline] public def hpmvCol (uplo : Float32.Uplo) (α : ComplexFloat32) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) (j : Nat) (hj : j < n) (y : Vec n) : Vec n :=
  let t₁ := mul α x[j]
  let y := addVecAt ap (tpAr uplo n j) (tpLo uplo j) (tpLen uplo n j) (tpAr_add_tpLen uplo hj)
    (tpLo_add_tpLen uplo n j hj) t₁ y
  y.set j hj (y[j] + mulr t₁ (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj)).re +
    mul α (hpmvDot uplo ap x j hj))

/--
The step `j` of `hpmv` at element `i` of `y`, from its value `s`: with `t₁ = mul α x[j]`, it adds
`mul t₁ ap[tpIdx uplo n i j]` when `(i, j)` is in the triangle off the diagonal, and on the
diagonal it gives `s + mulr t₁ ap[tpIdx uplo n j j].re + mul α (hpmvDot uplo ap x j)`, as `zhpmv`.
-/
@[expose] public def hpmvStep (uplo : Float32.Uplo) (α : ComplexFloat32)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) (i : Nat) (hi : i < n)
    (s : ComplexFloat32) : ComplexFloat32 :=
  if i = j then s + mulr (mul α x[j]) (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj)).re +
    mul α (hpmvDot uplo ap x j hj)
  else if h : InTri uplo i j then
    s + mul (mul α x[j]) (ap[tpIdx uplo n i j]'(tpIdx_lt uplo (inPTri_of_inTri h) hi hj))
  else s

private theorem getElem_hpmvCol (uplo : Float32.Uplo) (α : ComplexFloat32)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat)
    (hi : i < n) : (hpmvCol uplo α ap x j hj y)[i] = hpmvStep uplo α ap x j hj i hi y[i] := by
  have hj' : ¬(tpLo uplo j ≤ j ∧ j < tpLo uplo j + tpLen uplo n j) :=
    fun h => not_inTri_self uplo j ((mem_tp uplo n j j hj hj).1 h)
  simp only [hpmvCol, hpmvStep, Vec.getElem_set, getElem_addVecAt]
  by_cases e : i = j
  · subst e; simp only [hj', ↓reduceDIte, ↓reduceIte]
  · simp only [e, ↓reduceIte]
    by_cases h : InTri uplo i j
    · have hm := (mem_tp uplo n i j hi hj).2 h
      simp only [hm, h, and_self, ↓reduceDIte]
      simp only [tpAr_add_sub uplo n i j h]
    · have hm : ¬(tpLo uplo j ≤ i ∧ i < tpLo uplo j + tpLen uplo n j) :=
        fun h' => h ((mem_tp uplo n i j hi hj).1 h')
      simp only [hm, h, ↓reduceDIte]

/--
`hpmv uplo α ap x β y` is `α * A * x + β * y` for the Hermitian matrix `A` whose upper or lower
triangle is packed in `ap`, as `zhpmv`: it returns `y` when `n = 0`, or `α = 0` and `β = 1`; it
scales `y` by `β` (`betaScal`), returns when `α = 0`, and then runs the steps `hpmvCol` for each
column in increasing order. It reads only the real part of the diagonal.
-/
@[expose] public def hpmv (uplo : Float32.Uplo) (α : ComplexFloat32) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) (β : ComplexFloat32) (y : Vec n) : Vec n :=
  if n = 0 then y
  else if isZero α && isOne β then y
  else
    let y := y.betaScal β
    if isZero α then y else Nat.fold n (fun j hj y => hpmvCol uplo α ap x j hj y) y

/--
Element `i` of `hpmv`: `betaMul β y[i]` when `α = 0`, and otherwise the fold of the steps
`hpmvStep` over the columns, from `betaMul β y[i]`.
-/
public theorem getElem_hpmv (uplo : Float32.Uplo) (α : ComplexFloat32) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) (β : ComplexFloat32) (y : Vec n) (i : Nat) (h : i < n) :
    (hpmv uplo α ap x β y)[i] =
      if isZero α then betaMul β y[i]
      else Nat.fold n (fun j hj s => hpmvStep uplo α ap x j hj i h s) (betaMul β y[i]) := by
  unfold hpmv
  have hn : n ≠ 0 := by lia
  simp only [hn, ↓reduceIte]
  by_cases ha : isZero α
  · by_cases hb : isOne β
    · simp [ha, hb, betaMul]
    · simp [ha, hb]
  · simp only [ha, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [Vec.getElem_fold_of_pointwise (fun j hj y => hpmvCol uplo α ap x j hj y)
      (fun j hj i hi s => hpmvStep uplo α ap x j hj i hi s)
      (fun j hj y i hi => getElem_hpmvCol uplo α ap x j hj y i hi) _ i h n (Nat.le_refl _),
      Vec.getElem_betaScal]

/-! ## `tpmv` -/

/--
The step of `tpmv` for column `j`: add `x[j]` times column `j` off the diagonal, and multiply
`x[j]` by the diagonal element unless the diagonal is unit, as `ztpmv`.
-/
@[inline] public def tpmvCol (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := x[j]
  let x := addVecAt ap (tpAr uplo n j) (tpLo uplo j) (tpLen uplo n j) (tpAr_add_tpLen uplo hj)
    (tpLo_add_tpLen uplo n j hj) t x
  x.set j hj (diagMul d x[j] (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj)))

private theorem getElem_tpmvCol (uplo : Float32.Uplo) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (tpmvCol uplo d ap j hj y)[i] =
      if i = j then diagMul d y[j] (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj))
      else if h : InTri uplo i j then
        y[i] + mul y[j] (ap[tpIdx uplo n i j]'(tpIdx_lt uplo (inPTri_of_inTri h) hi hj))
      else y[i] := by
  have hj' : ¬(tpLo uplo j ≤ j ∧ j < tpLo uplo j + tpLen uplo n j) :=
    fun h => not_inTri_self uplo j ((mem_tp uplo n j j hj hj).1 h)
  simp only [tpmvCol, Vec.getElem_set, getElem_addVecAt]
  by_cases e : i = j
  · subst e; simp only [hj', ↓reduceDIte, ↓reduceIte]
  · simp only [e, ↓reduceIte]
    by_cases h : InTri uplo i j
    · have hm := (mem_tp uplo n i j hi hj).2 h
      simp only [hm, h, and_self, ↓reduceDIte]
      simp only [tpAr_add_sub uplo n i j h]
    · have hm : ¬(tpLo uplo j ≤ i ∧ i < tpLo uplo j + tpLen uplo n j) :=
        fun h' => h ((mem_tp uplo n i j hi hj).1 h')
      simp only [hm, h, ↓reduceDIte]

/--
`tpmv uplo d ap x` is `A * x` for the triangular matrix `A` packed in `ap`, with a unit diagonal
if `d` is `.unit`, by the loops of `ztpmv`: the steps `tpmvCol` for `j = 0, …, n - 1` for the
upper triangle, and from `j = n - 1` down to `0` for the lower one.
-/
@[expose] public def tpmv (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun j hj x => tpmvCol .upper d ap j hj x) x
  | .lower => Nat.fold n (fun s hs x => tpmvCol .lower d ap (n - 1 - s) (by lia) x) x

private theorem getElem_tpmv_upper' (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tpmvCol .upper d ap j (by lia) x) x)[i] =
        if i < K then Nat.fold (K - 1 - i) (fun t _ s => s + mul (x.get0 (i + 1 + t))
          (pget0 .upper ap i (i + 1 + t)))
            (diagMul d x[i] (ap[tpIdx .upper n i i]'(tpIdx_self_lt .upper hi)))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tpmvCol .upper d ap j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      have hyK := hy K hK
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
      rw [getElem_tpmvCol, hyK, hy i hi]
      by_cases e : i = K
      · subst e
        rw [Nat.fold_congr (show i + 1 - 1 - i = 0 by lia)]
        simp
      · simp only [e, ↓reduceIte]
        by_cases h : InTri .upper i K
        · have h' : i < K := by simpa [InTri] using h
          simp only [h, ↓reduceDIte, h', show i < K + 1 by lia, ↓reduceIte]
          rw [Nat.fold_congr (show K + 1 - 1 - i = K - 1 - i + 1 by lia), Nat.fold_succ]
          have e1 : i + 1 + (K - 1 - i) = K := by lia
          rw [e1, vget0_eq x hK, pget0_eq .upper ap (inPTri_of_inTri h) hi hK]
        · simp only [h, ↓reduceDIte]
          have h' : ¬i < K := by simp [InTri] at h; lia
          simp [h', show ¬i < K + 1 by lia])

private theorem getElem_tpmv_lower' (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tpmvCol .lower d ap (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then Nat.fold (i - (n - K)) (fun t _ s => s +
          mul (x.get0 (i - 1 - t)) (pget0 .lower ap i (i - 1 - t)))
            (diagMul d x[i] (ap[tpIdx .lower n i i]'(tpIdx_self_lt .lower hi)))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tpmvCol .lower d ap (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      have hyK := hy (n - 1 - K) (by lia)
      simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
      rw [getElem_tpmvCol, hyK, hy i hi]
      by_cases e : i = n - 1 - K
      · subst e
        rw [Nat.fold_congr (show n - 1 - K - (n - (K + 1)) = 0 by lia)]
        simp [show n - (K + 1) ≤ n - 1 - K by lia]
      · simp only [e, ↓reduceIte]
        by_cases h : InTri .lower i (n - 1 - K)
        · have h' : n - 1 - K < i := by simpa [InTri] using h
          simp only [h, ↓reduceDIte, show n - K ≤ i by lia, show n - (K + 1) ≤ i by lia,
            ↓reduceIte]
          rw [Nat.fold_congr (show i - (n - (K + 1)) = i - (n - K) + 1 by lia), Nat.fold_succ]
          have e1 : i - 1 - (i - (n - K)) = n - 1 - K := by lia
          rw [e1, vget0_eq x (by lia), pget0_eq .lower ap (inPTri_of_inTri h) hi (by lia)]
        · simp only [h, ↓reduceDIte]
          have h' : i < n - 1 - K := by simp [InTri] at h; lia
          simp [show ¬n - K ≤ i by lia, show ¬n - (K + 1) ≤ i by lia])

/--
Element `i` of `tpmv .upper d ap x` is `x[i]` times the diagonal element (unless the diagonal is
unit), plus the terms `mul x[j] A[i, j]` for `j = i + 1, …, n - 1`, in this order.
-/
public theorem getElem_tpmv_upper (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tpmv .upper d ap x)[i] = Nat.fold (n - 1 - i) (fun t ht s =>
      s + mul (x[i + 1 + t]'(by lia))
        (ap[tpIdx .upper n i (i + 1 + t)]'(tpIdx_lt .upper (by simp [InPTri]; lia) hi (by lia))))
        (diagMul d x[i] (ap[tpIdx .upper n i i]'(tpIdx_self_lt .upper hi))) := by
  rw [tpmv, getElem_tpmv_upper' d ap x n (Nat.le_refl _) i hi, ite_eq_left hi]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), pget0_eq .upper ap (by simp [InPTri]; lia) hi (by lia)]

/--
Element `i` of `tpmv .lower d ap x` is `x[i]` times the diagonal element (unless the diagonal is
unit), plus the terms `mul x[j] A[i, j]` for `j = i - 1, …, 0`, in this order.
-/
public theorem getElem_tpmv_lower (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tpmv .lower d ap x)[i] = Nat.fold i (fun t ht s =>
      s + mul (x[i - 1 - t]'(by lia))
        (ap[tpIdx .lower n i (i - 1 - t)]'(tpIdx_lt .lower (by simp [InPTri]; lia) hi (by lia))))
        (diagMul d x[i] (ap[tpIdx .lower n i i]'(tpIdx_self_lt .lower hi))) := by
  rw [tpmv, getElem_tpmv_lower' d ap x n (Nat.le_refl _) i hi, ite_eq_left (by lia),
    Nat.sub_self, Nat.sub_zero]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), pget0_eq .lower ap (by simp [InPTri]; lia) hi (by lia)]

/-! ## `tpmvT` and `tpmvC` -/

/--
The step of `tpmvTWith p .upper` for column `j`: `x[j]` becomes `x[j]` times `p` of the diagonal
element, plus `mul (p A[i, j]) x[i]` for `i = j - 1, …, 0`.
-/
@[expose, specialize] public def tpmvTUpperCol (p : ComplexFloat32 → ComplexFloat32)
    (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := Vec.accRev p (· + ·)
    (diagMul d x[j] (p (ap[tpIdx .upper n j j]'(tpIdx_self_lt .upper hj))))
    (ap.slice (tpAr .upper n j) (tpLen .upper n j) (tpAr_add_tpLen .upper hj))
    (x.slice (tpLo .upper j) (tpLen .upper n j) (tpLo_add_tpLen .upper n j hj))
  x.set j hj t

/--
The step of `tpmvTWith p .lower` for column `j`: `x[j]` becomes `x[j]` times `p` of the diagonal
element, plus `mul (p A[i, j]) x[i]` for `i = j + 1, …, n - 1`.
-/
@[expose, specialize] public def tpmvTLowerCol (p : ComplexFloat32 → ComplexFloat32)
    (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := Vec.acc p (· + ·)
    (diagMul d x[j] (p (ap[tpIdx .lower n j j]'(tpIdx_self_lt .lower hj))))
    (ap.slice (tpAr .lower n j) (tpLen .lower n j) (tpAr_add_tpLen .lower hj))
    (x.slice (tpLo .lower j) (tpLen .lower n j) (tpLo_add_tpLen .lower n j hj))
  x.set j hj t

/--
`tpmvTWith p uplo d ap x` is the product of `x` by the transpose of the triangular matrix `A`
packed in `ap`, with each element of `A` mapped by `p`, by the loops of `ztpmv`: from `j = n - 1`
down to `0` for the upper triangle, and for `j = 0, …, n - 1` for the lower one, it sets `x[j]` to
`x[j]` times `p` of the diagonal element (unless the diagonal is unit) plus the terms of column
`j`, from the diagonal outwards.
-/
@[expose, specialize] public def tpmvTWith (p : ComplexFloat32 → ComplexFloat32)
    (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun s hs x => tpmvTUpperCol p d ap (n - 1 - s) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => tpmvTLowerCol p d ap j hj x) x

private theorem getElem_tpmvT_upper' (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tpmvTUpperCol p d ap (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then Nat.fold i (fun t _ s => s + mul (p (pget0 .upper ap (i - 1 - t) i))
          (x.get0 (i - 1 - t)))
            (diagMul d x[i] (p (ap[tpIdx .upper n i i]'(tpIdx_self_lt .upper hi))))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tpmvTUpperCol p d ap (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      simp only [tpmvTUpperCol, Vec.getElem_set]
      by_cases e : i = n - 1 - K
      · subst e
        have hyK := hy (n - 1 - K) (by lia)
        simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
        simp only [↓reduceIte, show n - (K + 1) ≤ n - 1 - K by lia, Vec.accRev_eq, hyK,
          Vec.opC_add]
        congr 1; funext t ht s
        have hl : tpLo .upper (n - 1 - K) + (tpLen .upper n (n - 1 - K) - 1 - t) =
            n - 1 - K - 1 - t := by simp only [tpLo, tpLen]; lia
        have hr : tpAr .upper n (n - 1 - K) + (tpLen .upper n (n - 1 - K) - 1 - t) =
            tpIdx .upper n (n - 1 - K - 1 - t) (n - 1 - K) := by
          simp only [tpAr, tpLen, tpIdx]
        have hyl := hy (n - 1 - K - 1 - t) (by lia)
        simp only [show ¬n - K ≤ n - 1 - K - 1 - t by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice]
        rw [Vec.getElem_eq_of_eq _ hl, hyl, Vec.getElem_eq_of_eq _ hr, vget0_eq x (by lia),
          pget0_eq .upper ap (by simp [InPTri]; lia) (by lia) hi]
      · rw [ite_eq_right e, hy]
        by_cases h : n - K ≤ i
        · simp [h, show n - (K + 1) ≤ i by lia]
        · simp [h, show ¬n - (K + 1) ≤ i by lia])

private theorem getElem_tpmvT_lower' (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tpmvTLowerCol p d ap j (by lia) x) x)[i] =
        if i < K then Nat.fold (n - 1 - i) (fun t _ s => s +
          mul (p (pget0 .lower ap (i + 1 + t) i)) (x.get0 (i + 1 + t)))
            (diagMul d x[i] (p (ap[tpIdx .lower n i i]'(tpIdx_self_lt .lower hi))))
        else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tpmvTLowerCol p d ap j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      simp only [tpmvTLowerCol, Vec.getElem_set]
      by_cases e : i = K
      · subst e
        have hyK := hy i hK
        simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
        simp only [↓reduceIte, Nat.lt_add_one, Vec.acc_eq, hyK, Vec.opC_add]
        congr 1; funext t ht s
        have hyl := hy (i + 1 + t) (by simp only [tpLen] at ht; lia)
        simp only [show ¬i + 1 + t < i by lia, ↓reduceIte] at hyl
        have hr : tpAr .lower n i + t = tpIdx .lower n (i + 1 + t) i := by
          simp only [tpAr, tpIdx]; lia
        simp only [Vec.getElem_slice]
        rw [Vec.getElem_eq_of_eq _ (show tpLo .lower i + t = i + 1 + t from rfl), hyl,
          Vec.getElem_eq_of_eq _ hr, vget0_eq x (by simp only [tpLen] at ht; lia),
          pget0_eq .lower ap (by simp [InPTri]; lia) (by simp only [tpLen] at ht; lia) hi]
      · rw [ite_eq_right e, hy]
        by_cases h : i < K
        · simp [h, show i < K + 1 by lia]
        · simp [h, show ¬i < K + 1 by lia])

/--
Element `j` of `tpmvTWith p .upper d ap x` is `x[j]` times `p` of the diagonal element (unless
the diagonal is unit), plus the terms `mul (p A[i, j]) x[i]` for `i = j - 1, …, 0`, in this
order.
-/
public theorem getElem_tpmvTWith_upper (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) :
    (tpmvTWith p .upper d ap x)[j] = Nat.fold j (fun t _ht s =>
      s + mul (p (ap[tpIdx .upper n (j - 1 - t) j]'(tpIdx_lt .upper (by simp [InPTri]; lia)
        (by lia) hj))) (x[j - 1 - t]'(by lia)))
        (diagMul d x[j] (p (ap[tpIdx .upper n j j]'(tpIdx_self_lt .upper hj)))) := by
  rw [tpmvTWith, getElem_tpmvT_upper' p d ap x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), pget0_eq .upper ap (by simp [InPTri]; lia) (by lia) hj]

/--
Element `j` of `tpmvTWith p .lower d ap x` is `x[j]` times `p` of the diagonal element (unless
the diagonal is unit), plus the terms `mul (p A[i, j]) x[i]` for `i = j + 1, …, n - 1`, in this
order.
-/
public theorem getElem_tpmvTWith_lower (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) :
    (tpmvTWith p .lower d ap x)[j] = Nat.fold (n - 1 - j) (fun t ht s =>
      s + mul (p (ap[tpIdx .lower n (j + 1 + t) j]'(tpIdx_lt .lower (by simp [InPTri]; lia)
        (by lia) hj))) (x[j + 1 + t]'(by lia)))
        (diagMul d x[j] (p (ap[tpIdx .lower n j j]'(tpIdx_self_lt .lower hj)))) := by
  rw [tpmvTWith, getElem_tpmvT_lower' p d ap x n (Nat.le_refl _) j hj, ite_eq_left hj]
  congr 1; funext t ht s
  rw [vget0_eq x (by lia), pget0_eq .lower ap (by simp [InPTri]; lia) (by lia) hj]

/-- `tpmvT uplo d ap x` is `Aᵀ * x` for the packed triangular matrix `A`, as `ztpmv` with `'T'`. -/
@[expose] public def tpmvT (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : Vec n :=
  tpmvTWith id uplo d ap x

/-- `tpmvC uplo d ap x` is `Aᴴ * x` for the packed triangular matrix `A`, as `ztpmv` with `'C'`. -/
@[expose] public def tpmvC (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : Vec n :=
  tpmvTWith ComplexFloat32.conj uplo d ap x

/-! ## `tpsv` -/

/--
Element `i` of the solution of `A * y = x` for the lower triangular matrix `A` packed in `ap`:
`x[i]`, minus the terms `mul y[j] A[i, j]` for `j = 0, …, i - 1`, divided by the diagonal element
unless the diagonal is unit.
-/
@[expose] public def tpsvLowerM (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) : ComplexFloat32 :=
  diagDiv d (Nat.fold i (fun t _ht s => s - mul (tpsvLowerM d ap x t) (pget0 .lower ap i t))
    (x.get0 i)) (pget0 .lower ap i i)
termination_by i
decreasing_by lia

/--
Element `i` of the solution of `A * y = x` for the upper triangular matrix `A` packed in `ap`:
`x[i]`, minus the terms `mul y[j] A[i, j]` for `j = n - 1, …, i + 1`, divided by the diagonal
element unless the diagonal is unit.
-/
@[expose] public def tpsvUpperM (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) : ComplexFloat32 :=
  diagDiv d (Nat.fold (n - 1 - i) (fun t _ht s =>
      s - mul (tpsvUpperM d ap x (n - 1 - t)) (pget0 .upper ap i (n - 1 - t))) (x.get0 i))
    (pget0 .upper ap i i)
termination_by n - i
decreasing_by lia

/--
The step of `tpsv` for column `j`: divide `x[j]` by the diagonal element unless the diagonal is
unit, and subtract `x[j]` times column `j` off the diagonal, as `ztpsv`.
-/
@[inline] public def tpsvCol (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d x[j] (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj))
  let x := x.set j hj t
  subVecAt ap (tpAr uplo n j) (tpLo uplo j) (tpLen uplo n j) (tpAr_add_tpLen uplo hj)
    (tpLo_add_tpLen uplo n j hj) t x

private theorem getElem_tpsvCol (uplo : Float32.Uplo) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (j : Nat) (hj : j < n) (y : Vec n) (i : Nat) (hi : i < n) :
    (tpsvCol uplo d ap j hj y)[i] =
      if i = j then diagDiv d y[j] (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj))
      else if h : InTri uplo i j then
        y[i] - mul (diagDiv d y[j] (ap[tpIdx uplo n j j]'(tpIdx_self_lt uplo hj)))
          (ap[tpIdx uplo n i j]'(tpIdx_lt uplo (inPTri_of_inTri h) hi hj))
      else y[i] := by
  have hj' : ¬(tpLo uplo j ≤ j ∧ j < tpLo uplo j + tpLen uplo n j) :=
    fun h => not_inTri_self uplo j ((mem_tp uplo n j j hj hj).1 h)
  simp only [tpsvCol, getElem_subVecAt, Vec.getElem_set]
  by_cases e : i = j
  · subst e; simp only [hj', ↓reduceDIte, ↓reduceIte]
  · simp only [e, ↓reduceIte]
    by_cases h : InTri uplo i j
    · have hm := (mem_tp uplo n i j hi hj).2 h
      simp only [hm, h, and_self, ↓reduceDIte]
      simp only [tpAr_add_sub uplo n i j h]
    · have hm : ¬(tpLo uplo j ≤ i ∧ i < tpLo uplo j + tpLen uplo n j) :=
        fun h' => h ((mem_tp uplo n i j hi hj).1 h')
      simp only [hm, h, ↓reduceDIte]

/--
`tpsv uplo d ap x` solves `A * y = x` for the triangular matrix `A` packed in `ap`, with a unit
diagonal if `d` is `.unit`, by the loops of `ztpsv`: the steps `tpsvCol` from `j = n - 1` down to
`0` for the upper triangle, and for `j = 0, …, n - 1` for the lower one. Like the reference BLAS,
it doesn't check for a zero on the diagonal.
-/
@[expose] public def tpsv (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun s hs x => tpsvCol .upper d ap (n - 1 - s) (by lia) x) x
  | .lower => Nat.fold n (fun j hj x => tpsvCol .lower d ap j hj x) x

private theorem tpsvLowerM_eq (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    {i : Nat} (hi : i < n) :
    tpsvLowerM d ap x i = diagDiv d (Nat.fold i (fun t _ s =>
      s - mul (tpsvLowerM d ap x t) (pget0 .lower ap i t)) x[i])
        (ap[tpIdx .lower n i i]'(tpIdx_self_lt .lower hi)) := by
  rw [tpsvLowerM, vget0_eq x hi, pget0_eq .lower ap (inPTri_self .lower i) hi hi]

private theorem tpsvUpperM_eq (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    {i : Nat} (hi : i < n) :
    tpsvUpperM d ap x i = diagDiv d (Nat.fold (n - 1 - i) (fun t _ s =>
      s - mul (tpsvUpperM d ap x (n - 1 - t)) (pget0 .upper ap i (n - 1 - t))) x[i])
        (ap[tpIdx .upper n i i]'(tpIdx_self_lt .upper hi)) := by
  rw [tpsvUpperM, vget0_eq x hi, pget0_eq .upper ap (inPTri_self .upper i) hi hi]

private theorem getElem_tpsv_lower' (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tpsvCol .lower d ap j (by lia) x) x)[i] =
        if i < K then tpsvLowerM d ap x i
        else Nat.fold K (fun t _ s => s - mul (tpsvLowerM d ap x t) (pget0 .lower ap i t)) x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tpsvCol .lower d ap j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      have hyK := hy K hK
      simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
      have ht : diagDiv d y[K] (ap[tpIdx .lower n K K]'(tpIdx_self_lt .lower hK)) =
          tpsvLowerM d ap x K := by
        rw [hyK, tpsvLowerM_eq d ap x hK]
      rw [getElem_tpsvCol, ht, hy i hi]
      by_cases e : i = K
      · subst e; simp
      · simp only [e, ↓reduceIte]
        by_cases h : InTri .lower i K
        · have h' : K < i := by simpa [InTri] using h
          simp only [h, ↓reduceDIte, show ¬i < K by lia, show ¬i < K + 1 by lia, ↓reduceIte]
          rw [Nat.fold_succ, pget0_eq .lower ap (inPTri_of_inTri h) hi hK]
        · simp only [h, ↓reduceDIte]
          have h' : i < K := by simp [InTri] at h; lia
          simp [h', show i < K + 1 by lia])

private theorem getElem_tpsv_upper' (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tpsvCol .upper d ap (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then tpsvUpperM d ap x i
        else Nat.fold K (fun t _ s =>
          s - mul (tpsvUpperM d ap x (n - 1 - t)) (pget0 .upper ap i (n - 1 - t))) x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tpsvCol .upper d ap (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      have hyK := hy (n - 1 - K) (by lia)
      simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
      have ht : diagDiv d y[n - 1 - K]
          (ap[tpIdx .upper n (n - 1 - K) (n - 1 - K)]'(tpIdx_self_lt .upper (by lia))) =
          tpsvUpperM d ap x (n - 1 - K) := by
        rw [hyK, tpsvUpperM_eq d ap x (by lia),
          Nat.fold_congr (show n - 1 - (n - 1 - K) = K by lia)]
      rw [getElem_tpsvCol, ht, hy i hi]
      by_cases e : i = n - 1 - K
      · subst e; simp [show n - (K + 1) ≤ n - 1 - K by lia]
      · simp only [e, ↓reduceIte]
        by_cases h : InTri .upper i (n - 1 - K)
        · have h' : i < n - 1 - K := by simpa [InTri] using h
          simp only [h, ↓reduceDIte, show ¬n - K ≤ i by lia, show ¬n - (K + 1) ≤ i by lia,
            ↓reduceIte]
          rw [Nat.fold_succ, pget0_eq .upper ap (inPTri_of_inTri h) hi (by lia)]
        · simp only [h, ↓reduceDIte]
          have h' : n - 1 - K < i := by simp [InTri] at h; lia
          simp [show n - K ≤ i by lia, show n - (K + 1) ≤ i by lia])

/-- Element `i` of `tpsv .lower d ap x` is element `i` of the model `tpsvLowerM`. -/
public theorem getElem_tpsv_lower_eq (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (hi : i < n) : (tpsv .lower d ap x)[i] = tpsvLowerM d ap x i := by
  rw [tpsv, getElem_tpsv_lower' d ap x n (Nat.le_refl _) i hi, ite_eq_left hi]

/-- Element `i` of `tpsv .upper d ap x` is element `i` of the model `tpsvUpperM`. -/
public theorem getElem_tpsv_upper_eq (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (hi : i < n) : (tpsv .upper d ap x)[i] = tpsvUpperM d ap x i := by
  rw [tpsv, getElem_tpsv_upper' d ap x n (Nat.le_refl _) i hi, ite_eq_left (by lia)]

/--
Element `i` of `y = tpsv .lower d ap x` is `x[i]`, minus the terms `mul y[j] A[i, j]` for
`j = 0, …, i - 1`, divided by the diagonal element unless the diagonal is unit: forward
substitution, in the order of the loops.
-/
public theorem getElem_tpsv_lower (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tpsv .lower d ap x)[i] = diagDiv d (Nat.fold i (fun t ht s =>
      s - mul ((tpsv .lower d ap x)[t]'(by lia))
        (ap[tpIdx .lower n i t]'(tpIdx_lt .lower (by simp [InPTri]; lia) hi (by lia)))) x[i])
          (ap[tpIdx .lower n i i]'(tpIdx_self_lt .lower hi)) := by
  rw [getElem_tpsv_lower_eq d ap x i hi, tpsvLowerM_eq d ap x hi]
  congr 1; congr 1; funext t ht s
  rw [getElem_tpsv_lower_eq d ap x _ (by lia), pget0_eq .lower ap (by simp [InPTri]; lia) hi
    (by lia)]

/--
Element `i` of `y = tpsv .upper d ap x` is `x[i]`, minus the terms `mul y[j] A[i, j]` for
`j = n - 1, …, i + 1`, divided by the diagonal element unless the diagonal is unit: back
substitution, in the order of the loops.
-/
public theorem getElem_tpsv_upper (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n)
    (i : Nat) (hi : i < n) :
    (tpsv .upper d ap x)[i] = diagDiv d (Nat.fold (n - 1 - i) (fun t ht s =>
      s - mul ((tpsv .upper d ap x)[n - 1 - t]'(by lia))
        (ap[tpIdx .upper n i (n - 1 - t)]'(tpIdx_lt .upper (by simp [InPTri]; lia) hi (by lia))))
          x[i]) (ap[tpIdx .upper n i i]'(tpIdx_self_lt .upper hi)) := by
  rw [getElem_tpsv_upper_eq d ap x i hi, tpsvUpperM_eq d ap x hi]
  congr 1; congr 1; funext t ht s
  rw [getElem_tpsv_upper_eq d ap x _ (by lia), pget0_eq .upper ap (by simp [InPTri]; lia) hi
    (by lia)]

/-! ## `tpsvT` and `tpsvC` -/

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the upper triangular matrix `A` packed in
`ap`: `x[j]`, minus the terms `mul (p A[i, j]) y[i]` for `i = 0, …, j - 1`, divided by `p` of the
diagonal element unless the diagonal is unit.
-/
@[expose] public def tpsvTUpperM (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) : ComplexFloat32 :=
  diagDiv d (Nat.fold j (fun t _ht s => s - mul (p (pget0 .upper ap t j))
    (tpsvTUpperM p d ap x t)) (x.get0 j)) (p (pget0 .upper ap j j))
termination_by j
decreasing_by lia

/--
Element `j` of the solution of `(p A)ᵀ * y = x` for the lower triangular matrix `A` packed in
`ap`: `x[j]`, minus the terms `mul (p A[i, j]) y[i]` for `i = n - 1, …, j + 1`, divided by `p` of
the diagonal element unless the diagonal is unit.
-/
@[expose] public def tpsvTLowerM (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) : ComplexFloat32 :=
  diagDiv d (Nat.fold (n - 1 - j) (fun t _ht s =>
      s - mul (p (pget0 .lower ap (n - 1 - t) j)) (tpsvTLowerM p d ap x (n - 1 - t))) (x.get0 j))
    (p (pget0 .lower ap j j))
termination_by n - j
decreasing_by lia

/-- The step of `tpsvTWith p .upper` for column `j`: solve for `x[j]` from the column above. -/
@[expose, specialize] public def tpsvTUpperCol (p : ComplexFloat32 → ComplexFloat32)
    (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d (Vec.acc p (· - ·) x[j]
    (ap.slice (tpAr .upper n j) (tpLen .upper n j) (tpAr_add_tpLen .upper hj))
    (x.slice (tpLo .upper j) (tpLen .upper n j) (tpLo_add_tpLen .upper n j hj)))
    (p (ap[tpIdx .upper n j j]'(tpIdx_self_lt .upper hj)))
  x.set j hj t

/-- The step of `tpsvTWith p .lower` for column `j`: solve for `x[j]` from the column below. -/
@[expose, specialize] public def tpsvTLowerCol (p : ComplexFloat32 → ComplexFloat32)
    (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (j : Nat) (hj : j < n) (x : Vec n) : Vec n :=
  let t := diagDiv d (Vec.accRev p (· - ·) x[j]
    (ap.slice (tpAr .lower n j) (tpLen .lower n j) (tpAr_add_tpLen .lower hj))
    (x.slice (tpLo .lower j) (tpLen .lower n j) (tpLo_add_tpLen .lower n j hj)))
    (p (ap[tpIdx .lower n j j]'(tpIdx_self_lt .lower hj)))
  x.set j hj t

/--
`tpsvTWith p uplo d ap x` solves `(p A)ᵀ * y = x` for the triangular matrix `A` packed in `ap`,
where `p A` maps each element of `A` by `p`, by the loops of `ztpsv`: for `j = 0, …, n - 1` for
the upper triangle, and from `j = n - 1` down to `0` for the lower one, it subtracts the terms of
column `j` from `x[j]`, from the far end inwards, and divides it by `p` of the diagonal element
(`div`) unless the diagonal is unit.
-/
@[expose, specialize] public def tpsvTWith (p : ComplexFloat32 → ComplexFloat32)
    (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2)) (x : Vec n) : Vec n :=
  match uplo with
  | .upper => Nat.fold n (fun j hj x => tpsvTUpperCol p d ap j hj x) x
  | .lower => Nat.fold n (fun s hs x => tpsvTLowerCol p d ap (n - 1 - s) (by lia) x) x

private theorem tpsvTUpperM_eq (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) {j : Nat} (hj : j < n) :
    tpsvTUpperM p d ap x j = diagDiv d (Nat.fold j (fun t _ s =>
      s - mul (p (pget0 .upper ap t j)) (tpsvTUpperM p d ap x t)) x[j])
        (p (ap[tpIdx .upper n j j]'(tpIdx_self_lt .upper hj))) := by
  rw [tpsvTUpperM, vget0_eq x hj, pget0_eq .upper ap (inPTri_self .upper j) hj hj]

private theorem tpsvTLowerM_eq (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) {j : Nat} (hj : j < n) :
    tpsvTLowerM p d ap x j = diagDiv d (Nat.fold (n - 1 - j) (fun t _ s =>
      s - mul (p (pget0 .lower ap (n - 1 - t) j)) (tpsvTLowerM p d ap x (n - 1 - t))) x[j])
        (p (ap[tpIdx .lower n j j]'(tpIdx_self_lt .lower hj))) := by
  rw [tpsvTLowerM, vget0_eq x hj, pget0_eq .lower ap (inPTri_self .lower j) hj hj]

private theorem getElem_tpsvT_upper' (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun j hj x => tpsvTUpperCol p d ap j (by lia) x) x)[i] =
        if i < K then tpsvTUpperM p d ap x i else x[i] :=
  Vec.getElem_fold_of_inv (fun j hj x => tpsvTUpperCol p d ap j (by lia) x) _ x
    (fun i hi => by simp) (by
      intro K hK y hy i hi
      simp only [tpsvTUpperCol, Vec.getElem_set]
      by_cases e : i = K
      · subst e
        have hyK := hy i hK
        simp only [Nat.lt_irrefl, ↓reduceIte] at hyK
        simp only [↓reduceIte, Nat.lt_add_one, Vec.acc_eq, hyK, Vec.opC_sub,
          tpsvTUpperM_eq p d ap x hK]
        congr 1; congr 1; funext t ht s
        have ht' : t < i := by simpa [tpLen] using ht
        have hyl := hy t (by lia)
        simp only [ht', ↓reduceIte] at hyl
        have hr : tpAr .upper n i + t = tpIdx .upper n t i := by simp only [tpAr, tpIdx]
        simp only [Vec.getElem_slice]
        rw [Vec.getElem_eq_of_eq _ (show tpLo .upper i + t = t by simp [tpLo]), hyl,
          Vec.getElem_eq_of_eq _ hr, pget0_eq .upper ap (by simp [InPTri]; lia) (by lia) hi]
      · rw [ite_eq_right e, hy]
        by_cases h : i < K
        · simp [h, show i < K + 1 by lia]
        · simp [h, show ¬i < K + 1 by lia])

private theorem getElem_tpsvT_lower' (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) :
    ∀ K (hK : K ≤ n) i (hi : i < n),
      (Nat.fold K (fun s hs x => tpsvTLowerCol p d ap (n - 1 - s) (by lia) x) x)[i] =
        if n - K ≤ i then tpsvTLowerM p d ap x i else x[i] :=
  Vec.getElem_fold_of_inv (fun s hs x => tpsvTLowerCol p d ap (n - 1 - s) (by lia) x) _ x
    (fun i hi => by simp [show ¬n ≤ i by lia]) (by
      intro K hK y hy i hi
      simp only [tpsvTLowerCol, Vec.getElem_set]
      by_cases e : i = n - 1 - K
      · subst e
        have hyK := hy (n - 1 - K) (by lia)
        simp only [show ¬n - K ≤ n - 1 - K by lia, ↓reduceIte] at hyK
        simp only [↓reduceIte, show n - (K + 1) ≤ n - 1 - K by lia, Vec.accRev_eq, hyK,
          Vec.opC_sub, tpsvTLowerM_eq p d ap x hi]
        congr 1; congr 1; funext t ht s
        have ht' : t < n - 1 - (n - 1 - K) := by simpa [tpLen] using ht
        have hl : tpLo .lower (n - 1 - K) + (tpLen .lower n (n - 1 - K) - 1 - t) = n - 1 - t := by
          simp only [tpLo, tpLen]; lia
        have hr : tpAr .lower n (n - 1 - K) + (tpLen .lower n (n - 1 - K) - 1 - t) =
            tpIdx .lower n (n - 1 - t) (n - 1 - K) := by simp only [tpAr, tpLen, tpIdx]; lia
        have hyl := hy (n - 1 - t) (by lia)
        simp only [show n - K ≤ n - 1 - t by lia, ↓reduceIte] at hyl
        simp only [Vec.getElem_slice]
        rw [Vec.getElem_eq_of_eq _ hl, hyl, Vec.getElem_eq_of_eq _ hr,
          pget0_eq .lower ap (by simp [InPTri]; lia) (by lia) hi]
      · rw [ite_eq_right e, hy]
        by_cases h : n - K ≤ i
        · simp [h, show n - (K + 1) ≤ i by lia]
        · simp [h, show ¬n - (K + 1) ≤ i by lia])

/-- Element `j` of `tpsvTWith p .upper d ap x` is element `j` of the model `tpsvTUpperM`. -/
public theorem getElem_tpsvTWith_upper_eq (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) :
    (tpsvTWith p .upper d ap x)[j] = tpsvTUpperM p d ap x j := by
  rw [tpsvTWith, getElem_tpsvT_upper' p d ap x n (Nat.le_refl _) j hj, ite_eq_left hj]

/-- Element `j` of `tpsvTWith p .lower d ap x` is element `j` of the model `tpsvTLowerM`. -/
public theorem getElem_tpsvTWith_lower_eq (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) :
    (tpsvTWith p .lower d ap x)[j] = tpsvTLowerM p d ap x j := by
  rw [tpsvTWith, getElem_tpsvT_lower' p d ap x n (Nat.le_refl _) j hj, ite_eq_left (by lia)]

/--
Element `j` of `y = tpsvTWith p .upper d ap x` is `x[j]`, minus the terms `mul (p A[i, j]) y[i]`
for `i = 0, …, j - 1`, divided by `p` of the diagonal element unless the diagonal is unit.
-/
public theorem getElem_tpsvTWith_upper (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) :
    (tpsvTWith p .upper d ap x)[j] = diagDiv d (Nat.fold j (fun t ht s =>
      s - mul (p (ap[tpIdx .upper n t j]'(tpIdx_lt .upper (by simp [InPTri]; lia) (by lia) hj)))
        ((tpsvTWith p .upper d ap x)[t]'(by lia))) x[j])
          (p (ap[tpIdx .upper n j j]'(tpIdx_self_lt .upper hj))) := by
  rw [getElem_tpsvTWith_upper_eq p d ap x j hj, tpsvTUpperM_eq p d ap x hj]
  congr 1; congr 1; funext t ht s
  rw [getElem_tpsvTWith_upper_eq p d ap x _ (by lia),
    pget0_eq .upper ap (by simp [InPTri]; lia) (by lia) hj]

/--
Element `j` of `y = tpsvTWith p .lower d ap x` is `x[j]`, minus the terms `mul (p A[i, j]) y[i]`
for `i = n - 1, …, j + 1`, divided by `p` of the diagonal element unless the diagonal is unit.
-/
public theorem getElem_tpsvTWith_lower (p : ComplexFloat32 → ComplexFloat32) (d : Float32.Diag)
    (ap : Vec (n * (n + 1) / 2)) (x : Vec n) (j : Nat) (hj : j < n) :
    (tpsvTWith p .lower d ap x)[j] = diagDiv d (Nat.fold (n - 1 - j) (fun t ht s =>
      s - mul (p (ap[tpIdx .lower n (n - 1 - t) j]'(tpIdx_lt .lower (by simp [InPTri]; lia)
        (by lia) hj))) ((tpsvTWith p .lower d ap x)[n - 1 - t]'(by lia))) x[j])
          (p (ap[tpIdx .lower n j j]'(tpIdx_self_lt .lower hj))) := by
  rw [getElem_tpsvTWith_lower_eq p d ap x j hj, tpsvTLowerM_eq p d ap x hj]
  congr 1; congr 1; funext t ht s
  rw [getElem_tpsvTWith_lower_eq p d ap x _ (by lia),
    pget0_eq .lower ap (by simp [InPTri]; lia) (by lia) hj]

/-- `tpsvT uplo d ap x` solves `Aᵀ * y = x` for the packed triangular `A` (`ztpsv`, `'T'`). -/
@[expose] public def tpsvT (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : Vec n :=
  tpsvTWith id uplo d ap x

/-- `tpsvC uplo d ap x` solves `Aᴴ * y = x` for the packed triangular `A` (`ztpsv`, `'C'`). -/
@[expose] public def tpsvC (uplo : Float32.Uplo) (d : Float32.Diag) (ap : Vec (n * (n + 1) / 2))
    (x : Vec n) : Vec n :=
  tpsvTWith ComplexFloat32.conj uplo d ap x

/-! ## `hpr` and `hpr2` -/

/-- The elements of `ap` in column `j` of the packed triangle, the diagonal included. -/
@[expose] public def InPCol (uplo : Float32.Uplo) (n j q : Nat) : Prop :=
  Float32.packedStart uplo n j ≤ q ∧ q < Float32.packedStart uplo n j + Float32.packedLen uplo n j

public instance (uplo : Float32.Uplo) (n j q : Nat) : Decidable (InPCol uplo n j q) := by
  unfold InPCol; infer_instance

/-- The row of the element `q` of `ap` in column `j`. -/
@[expose] public def pRow (uplo : Float32.Uplo) (n j q : Nat) : Nat :=
  Float32.packedRow uplo j + (q - Float32.packedStart uplo n j)

public theorem pRow_lt {uplo : Float32.Uplo} {n j q : Nat} (hj : j < n) (h : InPCol uplo n j q) :
    pRow uplo n j q < n := by
  cases uplo <;> simp only [pRow, InPCol, Float32.packedRow, Float32.packedLen] at * <;> lia

private theorem inPCol_unique {uplo : Float32.Uplo} {n j j' q : Nat} (hj : j < n) (hj' : j' < n)
    (h : InPCol uplo n j q) (h' : InPCol uplo n j' q) : j' = j := by
  cases uplo
  · exact packedUp_col_unique h.1 h.2 h'.1 h'.2
  · exact packedLo_col_unique hj hj' h.1 h.2 h'.1 h'.2

private theorem inPCol_tpIdx {uplo : Float32.Uplo} {n i j : Nat} (h : InPTri uplo i j)
    (hi : i < n) : InPCol uplo n j (tpIdx uplo n i j) ∧ pRow uplo n j (tpIdx uplo n i j) = i := by
  cases uplo <;> simp only [InPTri, InPCol, pRow, tpIdx, Float32.packedRow, Float32.packedLen,
    reduceCtorEq, true_and, false_and, or_false, false_or] at * <;> lia

private theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

private theorem dite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a : c → α) (b : ¬c → α) :
    dite c a b = a h := by simp [h]

private theorem dite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a : c → α) (b : ¬c → α) :
    dite c a b = b h := by simp [h]

/-- The step `j` of `hpr`, on `ap`, as `zhpr`. -/
public def hprCol (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (j : Nat) (hj : j < n)
    (ap : Vec (n * (n + 1) / 2)) : Vec (n * (n + 1) / 2) :=
  if isZero x[j] then setReAt (tpIdx uplo n j j) (tpIdx_self_lt uplo hj) id ap
  else
    let t := mul (ofReal α) x[j].conj
    match uplo with
    | .upper =>
      let ap := axpyRAt t x (tpLo .upper j) (tpAr .upper n j) (tpLen .upper n j)
        (tpLo_add_tpLen .upper n j hj) (tpAr_add_tpLen .upper hj) ap
      setReAt (tpIdx .upper n j j) (tpIdx_self_lt .upper hj) (· + (mul x[j] t).re) ap
    | .lower =>
      let ap := setReAt (tpIdx .lower n j j) (tpIdx_self_lt .lower hj) (· + (mul t x[j]).re) ap
      axpyRAt t x (tpLo .lower j) (tpAr .lower n j) (tpLen .lower n j)
        (tpLo_add_tpLen .lower n j hj) (tpAr_add_tpLen .lower hj) ap

private theorem herAt_eq_of_eq (uplo : Float32.Uplo) (α : Float32) (x : Vec n) {i i' j : Nat}
    (e : i = i') (hi : i < n) (hj : j < n) (a : ComplexFloat32) :
    herAt uplo α x i j hi hj a = herAt uplo α x i' j (e ▸ hi) hj a := by
  subst e; rfl

private theorem her2At_eq_of_eq (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n)
    {i i' j : Nat} (e : i = i') (hi : i < n) (hj : j < n) (a : ComplexFloat32) :
    her2At uplo α x y i j hi hj a = her2At uplo α x y i' j (e ▸ hi) hj a := by
  subst e; rfl

private theorem getElem_hprCol (uplo : Float32.Uplo) (α : Float32) (x : Vec n) (j : Nat)
    (hj : j < n) (ap : Vec (n * (n + 1) / 2)) (q : Nat) (hq : q < n * (n + 1) / 2) :
    (hprCol uplo α x j hj ap)[q] =
      if h : InPCol uplo n j q then herAt uplo α x (pRow uplo n j q) j (pRow_lt hj h) hj ap[q]
      else ap[q] := by
  unfold hprCol herAt
  by_cases h : InPCol uplo n j q
  · rw [dite_t h]
    have key : (q = tpIdx uplo n j j) ↔ (pRow uplo n j q = j) := by
      cases uplo <;> simp only [InPCol, pRow, tpIdx, Float32.packedRow, Float32.packedLen] at h ⊢
        <;> lia
    have hT : ¬q = tpIdx uplo n j j → InTri uplo (pRow uplo n j q) j := by
      intro e
      cases uplo <;> simp only [InPCol, pRow, tpIdx, Float32.packedRow, Float32.packedLen, InTri,
        reduceCtorEq, true_and, false_and, or_false, false_or] at h e ⊢ <;> lia
    by_cases hz : isZero x[j]
    · simp only [hz, ↓reduceIte, getElem_setReAt]
      by_cases e : q = tpIdx uplo n j j
      · rw [ite_t e, ite_t (key.1 e)]
        rfl
      · rw [ite_f e, ite_f (mt key.2 e)]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      by_cases e : q = tpIdx uplo n j j
      · have er := key.1 e
        cases uplo
        · have hl : ¬(tpAr .upper n j ≤ q ∧ q < tpAr .upper n j + tpLen .upper n j) := by
            simp only [tpAr, tpLen, tpIdx] at e ⊢; lia
          simp only [getElem_setReAt, ite_t e]
          rw [getElem_axpyRAt, dite_f hl]
          rw [ite_t er]
          rfl
        · have hl : ¬(tpAr .lower n j ≤ q ∧ q < tpAr .lower n j + tpLen .lower n j) := by
            simp only [tpAr, tpLen, tpIdx] at e ⊢; lia
          rw [getElem_axpyRAt, dite_f hl]
          rw [getElem_setReAt, ite_t e, ite_t er]
          rfl
      · have er := mt key.2 e
        have ht := hT e
        cases uplo
        · have hl : tpAr .upper n j ≤ q ∧ q < tpAr .upper n j + tpLen .upper n j := by
            simp only [InPCol, Float32.packedLen, tpAr, tpLen, tpIdx] at h e ⊢; lia
          simp only [getElem_setReAt, ite_f e]
          rw [getElem_axpyRAt, dite_t hl]
          rw [ite_f er, ite_t ht]
          rw [Vec.getElem_eq_of_eq x (show tpLo .upper j + (q - tpAr .upper n j) =
            pRow .upper n j q by simp only [tpLo, tpAr, pRow, Float32.packedRow])]
        · have hl : tpAr .lower n j ≤ q ∧ q < tpAr .lower n j + tpLen .lower n j := by
            simp only [InPCol, Float32.packedLen, tpAr, tpLen, tpIdx] at h e ⊢; lia
          rw [getElem_axpyRAt, dite_t hl]
          rw [getElem_setReAt, ite_f e, ite_f er, ite_t ht]
          rw [Vec.getElem_eq_of_eq x (show tpLo .lower j + (q - tpAr .lower n j) =
            pRow .lower n j q by simp only [tpLo, tpAr, pRow, Float32.packedRow] at hl ⊢; lia)]
  · rw [dite_f h]
    have hd : ¬q = tpIdx uplo n j j := fun e => h (e ▸ (inPCol_tpIdx (inPTri_self uplo j) hj).1)
    by_cases hz : isZero x[j]
    · simp only [hz, ↓reduceIte, getElem_setReAt, ite_f hd]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      cases uplo
      · have hl : ¬(tpAr .upper n j ≤ q ∧ q < tpAr .upper n j + tpLen .upper n j) := by
          simp only [InPCol, Float32.packedLen, tpAr, tpLen] at h ⊢; lia
        simp only [getElem_setReAt, ite_f hd]
        rw [getElem_axpyRAt, dite_f hl]
      · have hl : ¬(tpAr .lower n j ≤ q ∧ q < tpAr .lower n j + tpLen .lower n j) := by
          simp only [InPCol, Float32.packedLen, tpAr, tpLen] at h ⊢; lia
        rw [getElem_axpyRAt, dite_f hl]
        rw [getElem_setReAt, ite_f hd]

/-- A fold whose steps other than the step `j` leave its value unchanged. -/
private theorem fold_single {α : Type _} : ∀ (K : Nat) (f : (l : Nat) → l < K → α → α) (j : Nat)
    (v : α), (∀ l hl w, l ≠ j → f l hl w = w) →
    Nat.fold K f v = if h : j < K then f j h v else v
  | 0, _, _, _, _ => by simp
  | K + 1, f, j, v, hf => by
    rw [Nat.fold_succ, fold_single K (fun l hl w => f l (by lia) w) j v
      (fun l hl w hne => hf l (by lia) w hne)]
    by_cases e : K = j
    · subst e
      simp
    · rw [hf K (by lia) _ e]
      by_cases h : j < K
      · simp [h, show j < K + 1 by lia]
      · simp [h, show ¬j < K + 1 by lia]

/--
`hpr uplo α x ap` is `α * x * xᴴ + A` for a real `α`, on the upper or lower triangle of `A` packed
in `ap`, as `zhpr`: it returns `ap` when `α = 0`, and otherwise runs the steps `hprCol` for each
column in increasing order.
-/
@[expose] public def hpr (uplo : Float32.Uplo) (α : Float32) (x : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : Vec (n * (n + 1) / 2) :=
  if α == 0 then ap else Nat.fold n (fun j hj ap => hprCol uplo α x j hj ap) ap

/--
Element `(i, j)` of the triangle of `hpr uplo α x ap`: `ap[tpIdx uplo n i j]` when `α = 0`, and
`herAt uplo α x i j` of it otherwise.
-/
public theorem getElem_hpr (uplo : Float32.Uplo) (α : Float32) (x : Vec n)
    (ap : Vec (n * (n + 1) / 2)) {i j : Nat} (h : InPTri uplo i j) (hi : i < n) (hj : j < n) :
    (hpr uplo α x ap)[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj) =
      if α == 0 then ap[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj)
      else herAt uplo α x i j hi hj (ap[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj)) := by
  unfold hpr
  split
  · rfl
  · have hc := inPCol_tpIdx h hi
    rw [Vec.getElem_fold_of_pointwise (fun l hl B => hprCol uplo α x l hl B)
      (fun l hl q hq s => if h : InPCol uplo n l q then
        herAt uplo α x (pRow uplo n l q) l (pRow_lt hl h) hl s else s)
      (fun l hl B q hq => getElem_hprCol uplo α x l hl B q hq) ap _ _ n (Nat.le_refl _),
      fold_single n _ j _ (fun l hl w hne => by
        rw [dite_f (fun h' => hne (inPCol_unique hj hl hc.1 h'))])]
    simp only [hj, ↓reduceDIte, hc.1]
    exact herAt_eq_of_eq uplo α x hc.2 _ hj _

/-- The step `j` of `hpr2`, on `ap`, as `zhpr2`. -/
public def hpr2Col (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (j : Nat) (hj : j < n)
    (ap : Vec (n * (n + 1) / 2)) : Vec (n * (n + 1) / 2) :=
  if isZero x[j] && isZero y[j] then setReAt (tpIdx uplo n j j) (tpIdx_self_lt uplo hj) id ap
  else
    let t₁ := mul α y[j].conj
    let t₂ := (mul α x[j]).conj
    let w := (mul x[j] t₁ + mul y[j] t₂).re
    match uplo with
    | .upper =>
      let ap := axpyRAt t₁ x (tpLo .upper j) (tpAr .upper n j) (tpLen .upper n j)
        (tpLo_add_tpLen .upper n j hj) (tpAr_add_tpLen .upper hj) ap
      let ap := axpyRAt t₂ y (tpLo .upper j) (tpAr .upper n j) (tpLen .upper n j)
        (tpLo_add_tpLen .upper n j hj) (tpAr_add_tpLen .upper hj) ap
      setReAt (tpIdx .upper n j j) (tpIdx_self_lt .upper hj) (· + w) ap
    | .lower =>
      let ap := setReAt (tpIdx .lower n j j) (tpIdx_self_lt .lower hj) (· + w) ap
      let ap := axpyRAt t₁ x (tpLo .lower j) (tpAr .lower n j) (tpLen .lower n j)
        (tpLo_add_tpLen .lower n j hj) (tpAr_add_tpLen .lower hj) ap
      axpyRAt t₂ y (tpLo .lower j) (tpAr .lower n j) (tpLen .lower n j)
        (tpLo_add_tpLen .lower n j hj) (tpAr_add_tpLen .lower hj) ap

private theorem getElem_hpr2Col (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n) (j : Nat)
    (hj : j < n) (ap : Vec (n * (n + 1) / 2)) (q : Nat) (hq : q < n * (n + 1) / 2) :
    (hpr2Col uplo α x y j hj ap)[q] =
      if h : InPCol uplo n j q then
        her2At uplo α x y (pRow uplo n j q) j (pRow_lt hj h) hj ap[q]
      else ap[q] := by
  unfold hpr2Col her2At
  by_cases h : InPCol uplo n j q
  · rw [dite_t h]
    have key : (q = tpIdx uplo n j j) ↔ (pRow uplo n j q = j) := by
      cases uplo <;> simp only [InPCol, pRow, tpIdx, Float32.packedRow, Float32.packedLen] at h ⊢
        <;> lia
    have hT : ¬q = tpIdx uplo n j j → InTri uplo (pRow uplo n j q) j := by
      intro e
      cases uplo <;> simp only [InPCol, pRow, tpIdx, Float32.packedRow, Float32.packedLen, InTri,
        reduceCtorEq, true_and, false_and, or_false, false_or] at h e ⊢ <;> lia
    by_cases hz : isZero x[j] && isZero y[j]
    · simp only [hz, ↓reduceIte, getElem_setReAt]
      by_cases e : q = tpIdx uplo n j j
      · rw [ite_t e, ite_t (key.1 e)]
        rfl
      · rw [ite_f e, ite_f (mt key.2 e)]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      by_cases e : q = tpIdx uplo n j j
      · have er := key.1 e
        cases uplo
        · have hl : ¬(tpAr .upper n j ≤ q ∧ q < tpAr .upper n j + tpLen .upper n j) := by
            simp only [tpAr, tpLen, tpIdx] at e ⊢; lia
          simp only [getElem_setReAt, ite_t e]
          rw [getElem_axpyRAt, dite_f hl]
          rw [getElem_axpyRAt, dite_f hl]
          rw [ite_t er]
        · have hl : ¬(tpAr .lower n j ≤ q ∧ q < tpAr .lower n j + tpLen .lower n j) := by
            simp only [tpAr, tpLen, tpIdx] at e ⊢; lia
          rw [getElem_axpyRAt, dite_f hl]
          rw [getElem_axpyRAt, dite_f hl]
          rw [getElem_setReAt, ite_t e, ite_t er]
      · have er := mt key.2 e
        have ht := hT e
        cases uplo
        · have hl : tpAr .upper n j ≤ q ∧ q < tpAr .upper n j + tpLen .upper n j := by
            simp only [InPCol, Float32.packedLen, tpAr, tpLen, tpIdx] at h e ⊢; lia
          simp only [getElem_setReAt, ite_f e]
          rw [getElem_axpyRAt, dite_t hl]
          rw [getElem_axpyRAt, dite_t hl]
          rw [ite_f er, ite_t ht]
          rw [Vec.getElem_eq_of_eq x (show tpLo .upper j + (q - tpAr .upper n j) =
            pRow .upper n j q by simp only [tpLo, tpAr, pRow, Float32.packedRow])]
          rw [Vec.getElem_eq_of_eq y (show tpLo .upper j + (q - tpAr .upper n j) =
            pRow .upper n j q by simp only [tpLo, tpAr, pRow, Float32.packedRow])]
        · have hl : tpAr .lower n j ≤ q ∧ q < tpAr .lower n j + tpLen .lower n j := by
            simp only [InPCol, Float32.packedLen, tpAr, tpLen, tpIdx] at h e ⊢; lia
          rw [getElem_axpyRAt, dite_t hl]
          rw [getElem_axpyRAt, dite_t hl]
          rw [getElem_setReAt, ite_f e, ite_f er, ite_t ht]
          rw [Vec.getElem_eq_of_eq x (show tpLo .lower j + (q - tpAr .lower n j) =
            pRow .lower n j q by simp only [tpLo, tpAr, pRow, Float32.packedRow] at hl ⊢; lia)]
          rw [Vec.getElem_eq_of_eq y (show tpLo .lower j + (q - tpAr .lower n j) =
            pRow .lower n j q by simp only [tpLo, tpAr, pRow, Float32.packedRow] at hl ⊢; lia)]
  · rw [dite_f h]
    have hd : ¬q = tpIdx uplo n j j := fun e => h (e ▸ (inPCol_tpIdx (inPTri_self uplo j) hj).1)
    by_cases hz : isZero x[j] && isZero y[j]
    · simp only [hz, ↓reduceIte, getElem_setReAt, ite_f hd]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      cases uplo
      · have hl : ¬(tpAr .upper n j ≤ q ∧ q < tpAr .upper n j + tpLen .upper n j) := by
          simp only [InPCol, Float32.packedLen, tpAr, tpLen] at h ⊢; lia
        simp only [getElem_setReAt, ite_f hd]
        rw [getElem_axpyRAt, dite_f hl]
        rw [getElem_axpyRAt, dite_f hl]
      · have hl : ¬(tpAr .lower n j ≤ q ∧ q < tpAr .lower n j + tpLen .lower n j) := by
          simp only [InPCol, Float32.packedLen, tpAr, tpLen] at h ⊢; lia
        rw [getElem_axpyRAt, dite_f hl]
        rw [getElem_axpyRAt, dite_f hl]
        rw [getElem_setReAt, ite_f hd]

/--
`hpr2 uplo α x y ap` is `α * x * yᴴ + conj α * y * xᴴ + A` on the upper or lower triangle of `A`
packed in `ap`, as `zhpr2`: it returns `ap` when `α = 0`, and otherwise runs the steps `hpr2Col`
for each column in increasing order.
-/
@[expose] public def hpr2 (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n)
    (ap : Vec (n * (n + 1) / 2)) : Vec (n * (n + 1) / 2) :=
  if isZero α then ap else Nat.fold n (fun j hj ap => hpr2Col uplo α x y j hj ap) ap

/--
Element `(i, j)` of the triangle of `hpr2 uplo α x y ap`: `ap[tpIdx uplo n i j]` when `α = 0`, and
`her2At uplo α x y i j` of it otherwise.
-/
public theorem getElem_hpr2 (uplo : Float32.Uplo) (α : ComplexFloat32) (x y : Vec n)
    (ap : Vec (n * (n + 1) / 2)) {i j : Nat} (h : InPTri uplo i j) (hi : i < n) (hj : j < n) :
    (hpr2 uplo α x y ap)[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj) =
      if isZero α then ap[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj)
      else her2At uplo α x y i j hi hj (ap[tpIdx uplo n i j]'(tpIdx_lt uplo h hi hj)) := by
  unfold hpr2
  split
  · rfl
  · have hc := inPCol_tpIdx h hi
    rw [Vec.getElem_fold_of_pointwise (fun l hl B => hpr2Col uplo α x y l hl B)
      (fun l hl q hq s => if h : InPCol uplo n l q then
        her2At uplo α x y (pRow uplo n l q) l (pRow_lt hl h) hl s else s)
      (fun l hl B q hq => getElem_hpr2Col uplo α x y l hl B q hq) ap _ _ n (Nat.le_refl _),
      fold_single n _ j _ (fun l hl w hne => by
        rw [dite_f (fun h' => hne (inPCol_unique hj hl hc.1 h'))])]
    simp only [hj, ↓reduceDIte, hc.1]
    exact her2At_eq_of_eq uplo α x y hc.2 _ hj _

end Mat

end BLAS.ComplexFloat32
