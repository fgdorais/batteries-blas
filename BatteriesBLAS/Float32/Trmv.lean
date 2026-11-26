/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float32.Trsv
import all BatteriesBLAS.Internal

/-!
# Triangular product

`Mat.trmv uplo diag A x` computes `A * x` and `Mat.trmvT uplo diag A x` computes `Aᵀ * x`, for a
triangular matrix `A`, over `x`, by the loops of the reference BLAS. Each element of the result
reads only elements of `x` that the loops haven't overwritten yet, so the specifications are
folds over `x` itself: element `i` is `x[i] * A[i, i]`, or `x[i]` for a unit diagonal, plus the
terms of the other elements of row `i` (column `i` for `trmvT`) of the triangle, in the order of
the loops.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

/-- `d.mul v a` multiplies `v` by the diagonal element `a`, unless the diagonal is unit. -/
@[expose] public def Diag.mul : Diag → Float32 → Float32 → Float32
  | .unit, v, _ => v
  | .nonUnit, v, a => v * a

namespace Mat

variable {n : Nat}

/-! ## The models -/

/--
Element `i` of `A * x` for the upper triangle of `A`, on the arrays: `x[i] * A[i, i]`, plus the
terms `x[j] * A[i, j]` for `j = i + 1, …, n - 1`.
-/
@[expose] public def trmvUpper (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) : Float32 :=
  Nat.fold (n - 1 - i) (fun t _ s =>
      s + x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
    (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + i]!)

/--
Element `i` of `A * x` for the lower triangle of `A`, on the arrays: `x[i] * A[i, i]`, plus the
terms `x[j] * A[i, j]` for `j = i - 1, …, 0`.
-/
@[expose] public def trmvLower (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) : Float32 :=
  Nat.fold i (fun t _ s =>
      s + x.data[x.off + x.inc * (i - 1 - t)]! * A.data[A.off + A.ld * (i - 1 - t) + i]!)
    (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + i]!)

/--
Element `j` of `Aᵀ * x` for the upper triangle of `A`, on the arrays: `x[j] * A[j, j]`, plus the
terms `A[i, j] * x[i]` for `i = j - 1, …, 0`.
-/
@[expose] public def trmvTUpper (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  Nat.fold j (fun t _ s =>
      s + A.data[A.off + A.ld * j + (j - 1 - t)]! * x.data[x.off + x.inc * (j - 1 - t)]!)
    (d.mul x.data[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)

/--
Element `j` of `Aᵀ * x` for the lower triangle of `A`, on the arrays: `x[j] * A[j, j]`, plus the
terms `A[i, j] * x[i]` for `i = j + 1, …, n - 1`.
-/
@[expose] public def trmvTLower (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  Nat.fold (n - 1 - j) (fun t _ s =>
      s + A.data[A.off + A.ld * j + (j + 1 + t)]! * x.data[x.off + x.inc * (j + 1 + t)]!)
    (d.mul x.data[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)

/-! ## The loops -/

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged and
maps the variable by a fold.
-/
private theorem iterRange_fst (g : Nat → Float32Array → Float32 → Float32) (k : Nat) (t : Float32)
    (a : Float32Array) :
    iterRange (fun i p => (g i p.2 p.1, p.2)) 0 k (t, a) =
      (Nat.fold k (fun i _ s => g i a s) t, a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/-! ## The upper triangle -/

/--
The step `j` of the upper product: multiply element `j` by the diagonal, and add `x[j]` times
column `j` of `A` to the elements above it.
-/
@[expose] public def trmvUpperStep (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat)
    (b : Float32Array) : Float32Array :=
  let t := b[x.off + x.inc * j]!
  b.modifyAt x.stride.idx 0 (j + 1) fun i v =>
    if i = j then d.mul t A.data[A.off + A.ld * j + j]! else v + t * A.data[A.off + A.ld * j + i]!

private theorem lt_of_lt_of_lt {i j n : Nat} (h₁ : i < j) (h₂ : j < n) : i < n :=
  Nat.lt_trans h₁ h₂

/-- The array of the upper product. -/
public def trmvUpperData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        have hk : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let t := a[o + c * j]
        a[o + c * j] := d.mul t (A.uget ao al rfl rfl hs.1 j j hjn hjn)
        for i in 0...j do
          have hi : i.toNat < n := lt_of_lt_of_lt (by assumption) hjn
          have hk' : (o + c * i).toNat < a.size := x.toNat_index_lt hs.2 hi
          a[o + c * i] := a[o + c * i] + t * A.uget ao al rfl rfl hs.1 i j hi hjn
  else iterRange (trmvUpperStep d A x) 0 n x.data

public theorem trmvUpperData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvUpperData d A x = iterRange (trmvUpperStep d A x) 0 n x.data := by
  unfold trmvUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trmvUpperStep d A x) (hF := by simp [trmvUpperStep])]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      simp only [Tail.run_readThen, Tail.run_writeThen]
      have hp : (x.off.toUSize + x.inc.toUSize * j).toNat = x.off + x.inc * j.toNat :=
        x.toNat_index hs.2 hj
      rw [Tail.run_forInFrom_modify (idx := x.stride.idx)
        (he := fun i _ hi => x.toNat_index hs.2 (by lia))
        (G := fun i v => v + a[x.off + x.inc * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + i]!)]
      · congr 1
        rw [trmvUpperStep, USize.toNat_zero,
          set_modifyAt_pred _ (s := x.stride) (N := n) (by rw [h]; exact x.fits) hj _ _ _ hp]
        apply modifyAt_congr_fun
        intro i v _ _
        split
        · simp only [uget_eq_getElem, getElem_def, hp,
            getElem!_pos a (x.off + x.inc * j.toNat)
              (show _ < a.size by rw [h]; exact x.index_lt hj),
            getElem!_pos A.data (A.off + A.ld * j.toNat + j.toNat) (A.index_lt hj hj)]
        · rfl
      · intro i _ hi v
        simp only [uget_eq_getElem, getElem_def, hp,
          getElem!_pos a (x.off + x.inc * j.toNat)
            (show _ < a.size by rw [h]; exact x.index_lt hj),
          getElem!_pos A.data (A.off + A.ld * j.toNat + i.toNat) (A.index_lt (by lia) hj)]
  · rfl

/--
After the steps `l < j`, the elements `i < j` have their diagonal and the terms `l < j`, and the
others are unchanged.
-/
theorem iterRange_trmvUpperStep (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (hj : j ≤ n) :
    iterRange (trmvUpperStep d A x) 0 j x.data = x.data.modifyAt x.stride.idx 0 n fun i v =>
      if i < j then Nat.fold (j - 1 - i) (fun t _ s =>
          s + x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
        (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + i]!)
      else v := by
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trmvUpperStep]
    have ht : (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if i < j then Nat.fold (j - 1 - i) (fun t _ s =>
              s + x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
            (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + i]!)
          else v)[x.off + x.inc * j]! = x.data[x.off + x.inc * j]! := by
      rw [getElem!_pos _ (x.off + x.inc * j) (by simpa using x.index_lt (by lia : j < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        ite_eq_right (Nat.lt_irrefl j),
        getElem!_pos x.data (x.off + x.inc * j) (x.index_lt (by lia))]
    simp only [ht]
    rw [modifyAt_widen (lo := 0) (hi := j + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.le_refl _)
      (Nat.zero_le _) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < j
    · simp only [h₁, show i < j + 1 by lia, show i ≠ j by lia, and_self, ite_true, ite_false,
        Nat.zero_le]
      rw [Nat.fold_congr (show j + 1 - 1 - i = (j - 1 - i) + 1 by lia), Nat.fold_succ,
        show i + 1 + (j - 1 - i) = j by lia]
    · by_cases h₂ : i = j
      · subst h₂
        simp only [Nat.lt_irrefl, Nat.lt_succ_self, ite_true, ite_false, Nat.zero_le, and_self]
        rw [show i + 1 - 1 - i = 0 by lia, Nat.fold_zero]
      · simp [h₁, show ¬i < j + 1 by lia]

/-- The array of the upper product is the array of `x` with its elements multiplied. -/
public theorem trmvUpperData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvUpperData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvUpper d A x i := by
  rw [trmvUpperData_eq_iterRange, iterRange_trmvUpperStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [hi, ite_true, trmvUpper]

/-! ## The lower triangle -/

/--
The step `k` of the lower product: multiply element `j = n - 1 - k` by the diagonal, and add `x[j]`
times column `j` of `A` to the elements below it.
-/
@[expose] public def trmvLowerStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float32Array) : Float32Array :=
  let j := n - 1 - k
  let t := b[x.off + x.inc * j]!
  b.modifyAt x.stride.idx j n fun i v =>
    if i = j then d.mul t A.data[A.off + A.ld * j + j]! else v + t * A.data[A.off + A.ld * j + i]!

private theorem sub_one_sub_add_lt {i k n : Nat} (hk : k < n) (h : i < k) :
    n - 1 - k + 1 + i < n := by lia

/-- The array of the lower product. -/
public def trmvLowerData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    inplace a do
      for k in 0...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let t := a[o + c * (nu - 1 - k)]
        a[o + c * (nu - 1 - k)] :=
          d.mul t (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)
        for i in 0...k do
          have hjk : (nu - 1 - k).toNat + 1 + i.toNat < n := by
            rw [hj]; exact sub_one_sub_add_lt (by lia) (by assumption)
          have hk' : (o + c * (nu - 1 - k + 1) + c * i).toNat < a.size := by
            rw [x.toNat_index_shift hs.2 hjk]
            have := x.index_lt hjk
            rw [Nat.mul_add x.inc ((nu - 1 - k).toNat + 1), Nat.add_assoc] at *
            exact this
          a[o + c * (nu - 1 - k + 1) + c * i] := a[o + c * (nu - 1 - k + 1) + c * i] +
            t * A.uget ao al rfl rfl hs.1 (nu - 1 - k + 1 + i) (nu - 1 - k)
              (by grind [-PUnit]) hjn
  else iterRange (trmvLowerStep d A x) 0 n x.data

public theorem trmvLowerData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvLowerData d A x = iterRange (trmvLowerStep d A x) 0 n x.data := by
  unfold trmvLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trmvLowerStep d A x) (hF := by simp [trmvLowerStep])]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro k _ hk next a h
      rw [hnu] at hk
      simp only [Tail.run_readThen, Tail.run_writeThen]
      have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
      have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
          x.off + x.inc * (n - 1 - k.toNat) := by
        rw [x.toNat_index hs.2 (by lia), hj]
      have hsz := Nat.lt_of_le_of_lt x.le_size hs.2
      rw [Tail.run_forInFrom_modify
        (e := fun i => x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k + 1) + x.inc.toUSize * i)
        (idx := (x.stride.shift (n - 1 - k.toNat + 1)).idx)
        (he := fun i _ hi => by
          rw [x.toNat_index_shift hs.2 (by lia), hj]; simp [Stride.idx, Vec.stride])
        (G := fun i v => v + a[x.off + x.inc * (n - 1 - k.toNat)]! *
          A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + i)]!)]
      · congr 1
        have hs' := set_modifyAt_succ _ x.stride
          (d.mul a[x.off + x.inc * (n - 1 - k.toNat)]!
            A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat)]!)
          (fun i v => v + a[x.off + x.inc * (n - 1 - k.toNat)]! *
            A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + i)]!)
          (show n - 1 - k.toNat < n by lia) _ hp
          (by rw [hp, h]; exact x.index_lt (by lia))
        rw [show n - (n - 1 - k.toNat) - 1 = k.toNat by lia] at hs'
        rw [trmvLowerStep, USize.toNat_zero]
        simp only [uget_eq_getElem, getElem_def, hp, hj,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
            (A.index_lt (by lia) (by lia))] at hs' ⊢
        rw [hs']
        apply modifyAt_congr_fun
        intro i v h₁ h₂
        split
        · rfl
        · rw [show n - 1 - k.toNat + 1 + (i - (n - 1 - k.toNat + 1)) = i by lia]
      · intro i _ hi v
        simp only [uget_eq_getElem, getElem_def, hp, hj,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          show (n.toUSize - 1 - k + 1 + i).toNat = n - 1 - k.toNat + 1 + i.toNat by grind]
        rw [getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + i.toNat))
            (A.index_lt (by lia) (by lia))]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` have their diagonal and the terms of the columns
`n - k, …, i - 1`, and the others are unchanged.
-/
theorem iterRange_trmvLowerStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k ≤ n) :
    iterRange (trmvLowerStep d A x) 0 k x.data = x.data.modifyAt x.stride.idx 0 n fun i v =>
      if n - k ≤ i then Nat.fold (i - (n - k)) (fun t _ s =>
          s + x.data[x.off + x.inc * (i - 1 - t)]! * A.data[A.off + A.ld * (i - 1 - t) + i]!)
        (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + i]!)
      else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trmvLowerStep]
    have ht : (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then Nat.fold (i - (n - k)) (fun t _ s =>
              s + x.data[x.off + x.inc * (i - 1 - t)]! * A.data[A.off + A.ld * (i - 1 - t) + i]!)
            (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + i]!)
          else v)[x.off + x.inc * (n - 1 - k)]! = x.data[x.off + x.inc * (n - 1 - k)]! := by
      rw [getElem!_pos _ (x.off + x.inc * (n - 1 - k))
          (by simpa using x.index_lt (by lia : n - 1 - k < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        ite_eq_right (by lia),
        getElem!_pos x.data (x.off + x.inc * (n - 1 - k)) (x.index_lt (by lia))]
    simp only [ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _)
      (by lia) (Nat.le_refl _), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp only [h₁, show n - (k + 1) ≤ i by lia, show n - 1 - k ≤ i by lia,
        show i ≠ n - 1 - k by lia, hi, and_self, ite_true, ite_false]
      rw [Nat.fold_congr (show i - (n - (k + 1)) = (i - (n - k)) + 1 by lia), Nat.fold_succ,
        show i - 1 - (i - (n - k)) = n - 1 - k by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂
        simp only [show n - 1 - k < n by lia, ite_true, show n - (k + 1) ≤ n - 1 - k by lia]
        rw [show n - 1 - k - (n - (k + 1)) = 0 by lia, Nat.fold_zero,
          ite_eq_left_of_eq_true _ _ (by simp)]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/-- The array of the lower product is the array of `x` with its elements multiplied. -/
public theorem trmvLowerData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvLowerData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvLower d A x i := by
  rw [trmvLowerData_eq_iterRange, iterRange_trmvLowerStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [Nat.sub_self, ite_eq_left_of_eq_true _ _ (eq_true (Nat.zero_le _)), Nat.sub_zero, trmvLower]

/-! ## The transposed upper triangle -/

/--
The step `k` of the transposed upper product: set element `j = n - 1 - k` from the elements above
it, which are still those of `x`.
-/
@[expose] public def trmvTUpperStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float32Array) : Float32Array :=
  let j := n - 1 - k
  let t := Nat.fold j (fun t _ s =>
      s + A.data[A.off + A.ld * j + (j - 1 - t)]! * b[x.off + x.inc * (j - 1 - t)]!)
    (d.mul b[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The value of the step `k` of the transposed upper product, on the array `b`. -/
private def trmvTUpperVal (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat) (b : Float32Array) :
    Float32 :=
  Nat.fold (n - 1 - k) (fun t _ s =>
      s + A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k - 1 - t)]! *
        b[x.off + x.inc * (n - 1 - k - 1 - t)]!)
    (d.mul b[x.off + x.inc * (n - 1 - k)]! A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]!)

private theorem trmvTUpperStep_eq_set! (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTUpperStep d A x =
      fun k b => b.set! (x.off + x.inc * (n - 1 - k)) (trmvTUpperVal d A x k b) := by
  funext k b
  rw [trmvTUpperStep, modifyAt_of_lt _ _ (Nat.lt_succ_self _), modifyAt_self, Vec.idx_stride]
  rfl

/-- The value of a step reads only the elements up to its own. -/
private theorem trmvTUpperVal_congr (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat}
    {b b' : Float32Array}
    (h : ∀ i, i ≤ n - 1 - k → b[x.off + x.inc * i]! = b'[x.off + x.inc * i]!) :
    trmvTUpperVal d A x k b = trmvTUpperVal d A x k b' := by
  unfold trmvTUpperVal
  rw [h _ (Nat.le_refl _)]
  congr 1
  funext t ht s
  rw [h _ (by lia)]

/--
The value of the step `K + r`, for `r < 4`, of the transposed upper product: the terms of the
elements of the steps `K + r + 1` to `K + 3`, then the others.
-/
private theorem trmvTUpperVal_four (d : Diag) (A : Mat n n) (x : Vec n) {K : Nat} (hK : K + 3 < n)
    (b : Float32Array) :
    let w := fun r i => A.data[A.off + A.ld * (n - 1 - (K + r)) + (n - 1 - (K + i))]!
    let y := fun i => b[x.off + x.inc * (n - 1 - (K + i))]!
    let F := fun r t s => s + A.data[A.off + A.ld * (n - 1 - (K + r)) + (n - 1 - (K + 4 + t))]! *
      b[x.off + x.inc * (n - 1 - (K + 4 + t))]!
    trmvTUpperVal d A x K b = Nat.fold (n - 4 - K) (fun t _ s => F 0 t s)
        (((d.mul (y 0) (w 0 0) + w 0 1 * y 1) + w 0 2 * y 2) + w 0 3 * y 3) ∧
      trmvTUpperVal d A x (K + 1) b = Nat.fold (n - 4 - K) (fun t _ s => F 1 t s)
        ((d.mul (y 1) (w 1 1) + w 1 2 * y 2) + w 1 3 * y 3) ∧
      trmvTUpperVal d A x (K + 2) b = Nat.fold (n - 4 - K) (fun t _ s => F 2 t s)
        (d.mul (y 2) (w 2 2) + w 2 3 * y 3) ∧
      trmvTUpperVal d A x (K + 3) b = Nat.fold (n - 4 - K) (fun t _ s => F 3 t s)
        (d.mul (y 3) (w 3 3)) := by
  intro w y F
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold trmvTUpperVal
    rw [fold_split 3 (n - 4 - K) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia
  · unfold trmvTUpperVal
    rw [fold_split 2 (n - 4 - K) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia
  · unfold trmvTUpperVal
    rw [fold_split 1 (n - 4 - K) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia
  · unfold trmvTUpperVal
    rw [Nat.fold_congr (show n - 1 - (K + 3) = n - 4 - K by lia)]
    simp only [w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia

/--
The array of the transposed upper product: four elements per pass, then the rest one at a time.
-/
public def trmvTUpperData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let q4 := nu / 4
    have hq4 : q4.toNat = n / 4 := by simp only [q4, USize.toNat_div, hnu]; simp
    inplace a do
      for g in 0...q4 do
        have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
        have j₀ : (nu - 1 - 4 * g).toNat = n - 1 - 4 * g.toNat := by grind
        have j₁ : (nu - 1 - (4 * g + 1)).toNat = n - 1 - (4 * g.toNat + 1) := by grind
        have j₂ : (nu - 1 - (4 * g + 2)).toNat = n - 1 - (4 * g.toNat + 2) := by grind
        have j₃ : (nu - 1 - (4 * g + 3)).toNat = n - 1 - (4 * g.toNat + 3) := by grind
        have k₀ : (o + c * (nu - 1 - 4 * g)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₁ : (o + c * (nu - 1 - (4 * g + 1))).toNat < a.size :=
          x.toNat_index_lt hs.2 (by lia)
        have k₂ : (o + c * (nu - 1 - (4 * g + 2))).toNat < a.size :=
          x.toNat_index_lt hs.2 (by lia)
        have k₃ : (o + c * (nu - 1 - (4 * g + 3))).toNat < a.size :=
          x.toNat_index_lt hs.2 (by lia)
        let y₀ := a[o + c * (nu - 1 - 4 * g)]
        let y₁ := a[o + c * (nu - 1 - (4 * g + 1))]
        let y₂ := a[o + c * (nu - 1 - (4 * g + 2))]
        let y₃ := a[o + c * (nu - 1 - (4 * g + 3))]
        let w := fun (r i : USize) (hr : (nu - 1 - (4 * g + r)).toNat < n)
          (hi : (nu - 1 - (4 * g + i)).toNat < n) =>
          A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + i)) (nu - 1 - (4 * g + r)) hi hr
        for t in 0...(nu - 4 - 4 * g) with
            (s₀ := ((d.mul y₀ (A.uget ao al rfl rfl hs.1 (nu - 1 - 4 * g) (nu - 1 - 4 * g)
                (by lia) (by lia)) +
              A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 1)) (nu - 1 - 4 * g) (by lia)
                (by lia) * y₁) +
              A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 2)) (nu - 1 - 4 * g) (by lia)
                (by lia) * y₂) +
              A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 3)) (nu - 1 - 4 * g) (by lia)
                (by lia) * y₃)
            (s₁ := (d.mul y₁ (w 1 1 (by lia) (by lia)) + w 1 2 (by lia) (by lia) * y₂) +
              w 1 3 (by lia) (by lia) * y₃)
            (s₂ := d.mul y₂ (w 2 2 (by lia) (by lia)) + w 2 3 (by lia) (by lia) * y₃)
            (s₃ := d.mul y₃ (w 3 3 (by lia) (by lia))) do
          have hi : (nu - 1 - (4 * g + 4 + t)).toNat < n := by grind
          have hk : (o + c * (nu - 1 - (4 * g + 4 + t))).toNat < a.size :=
            x.toNat_index_lt hs.2 hi
          let y := a[o + c * (nu - 1 - (4 * g + 4 + t))]
          s₀ := s₀ + A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 4 + t)) (nu - 1 - 4 * g) hi
            (by lia) * y
          s₁ := s₁ + A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 4 + t)) (nu - 1 - (4 * g + 1))
            hi (by lia) * y
          s₂ := s₂ + A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 4 + t)) (nu - 1 - (4 * g + 2))
            hi (by lia) * y
          s₃ := s₃ + A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 4 + t)) (nu - 1 - (4 * g + 3))
            hi (by lia) * y
        a[o + c * (nu - 1 - 4 * g)] := s₀
        a[o + c * (nu - 1 - (4 * g + 1))] := s₁
        a[o + c * (nu - 1 - (4 * g + 2))] := s₂
        a[o + c * (nu - 1 - (4 * g + 3))] := s₃
      for k in 4 * q4...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        for t in 0...(nu - 1 - k) with
            (s := d.mul v (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)) do
          have hi : (nu - 1 - k - 1 - t).toNat < n := by grind
          have hk' : (o + c * (nu - 1 - k - 1 - t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s + A.uget ao al rfl rfl hs.1 (nu - 1 - k - 1 - t) (nu - 1 - k) hi hjn *
            a[o + c * (nu - 1 - k - 1 - t)]
        a[o + c * (nu - 1 - k)] := s
  else iterRange (trmvTUpperStep d A x) 0 n x.data

public theorem trmvTUpperData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTUpperData d A x = iterRange (trmvTUpperStep d A x) 0 n x.data := by
  unfold trmvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hq4 : (n.toUSize / 4).toNat = n / 4 := by simp only [USize.toNat_div, hnu]; simp
    have h4q : (4 * (n.toUSize / 4)).toNat = 4 * (n / 4) := by grind
    have hF : ∀ j (b : Float32Array), (trmvTUpperStep d A x j b).size = b.size :=
      fun _ _ => size_modifyAt _ _ _ _ _
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit
      (F := fun g b => iterRange (trmvTUpperStep d A x) (4 * g) (4 * g + 4) b)
      (hF := fun _ _ => size_iterRange _ hF _ _ _)]
    · rw [Tail.run_forInFrom_unit (F := trmvTUpperStep d A x) (hF := hF)]
      · simp only [Tail.run_done, hq4, h4q, hnu, USize.toNat_zero]
        rw [iterRange_four, ← iterRange_split _ (Nat.zero_le _) (by lia)]
      · intro k hl hk next a h
        rw [hnu] at hk
        have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
        simp only [Tail.run_readThen]
        rw [Tail.run_forInFrom (f := fun t p =>
            (p.1 + A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat - 1 - t)]! *
              p.2[x.off + x.inc * (n - 1 - k.toNat - 1 - t)]!, p.2))
          (hf := fun _ _ => rfl)]
        · simp only [USize.toNat_zero, Tail.run_writeThen, hj, iterRange_fst (fun t a s =>
            s + A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat - 1 - t)]! *
              a[x.off + x.inc * (n - 1 - k.toNat - 1 - t)]!)]
          congr 1
          have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
              x.off + x.inc * (n - 1 - k.toNat) := by
            rw [x.toNat_index hs.2 (by lia), hj]
          rw [trmvTUpperStep, ← set_eq_modifyAt _ _ _ _
            (by rw [Vec.idx_stride, h]; exact x.index_lt (by lia))]
          simp only [hp, hj, Vec.idx_stride, uget_eq_getElem, getElem_def,
            getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
              (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
            getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
              (A.index_lt (by lia) (by lia))]
        · intro t _ ht next' b a' h'
          simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
          rw [hj] at ht
          have hi : (n.toUSize - 1 - k - 1 - t).toNat = n - 1 - k.toNat - 1 - t.toNat := by
            grind
          have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k - 1 - t)).toNat =
              x.off + x.inc * (n - 1 - k.toNat - 1 - t.toNat) := by
            rw [x.toNat_index hs.2 (by lia), hi]
          simp only [hp, hi, hj, getElem!_pos a' (x.off + x.inc * (n - 1 - k.toNat - 1 - t.toNat))
              (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
            getElem!_pos A.data
              (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat - 1 - t.toNat))
              (A.index_lt (by lia) (by lia))]
    · intro g _ hg next a h
      rw [hq4] at hg
      have hg4 : 4 * g.toNat + 3 < n := by lia
      have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
      have j₀ : (n.toUSize - 1 - 4 * g).toNat = n - 1 - 4 * g.toNat := by grind
      have j₁ : (n.toUSize - 1 - (4 * g + 1)).toNat = n - 1 - (4 * g.toNat + 1) := by grind
      have j₂ : (n.toUSize - 1 - (4 * g + 2)).toNat = n - 1 - (4 * g.toNat + 2) := by grind
      have j₃ : (n.toUSize - 1 - (4 * g + 3)).toNat = n - 1 - (4 * g.toNat + 3) := by grind
      have hm : (n.toUSize - 4 - 4 * g).toNat = n - 4 - 4 * g.toNat := by grind
      have t₀ := x.toNat_index hs.2 (i := n.toUSize - 1 - 4 * g) (by lia)
      have t₁ := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 1)) (by lia)
      have t₂ := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 2)) (by lia)
      have t₃ := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 3)) (by lia)
      rw [j₀] at t₀
      rw [j₁] at t₁
      rw [j₂] at t₂
      rw [j₃] at t₃
      simp only [Tail.run_readThen, Tail.forIn4_eq]
      rw [run_forIn4From_read
        (f₀ := fun t s => s + A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 0)) +
          (n - 1 - (4 * g.toNat + 4 + t))]! * a[x.off + x.inc * (n - 1 - (4 * g.toNat + 4 + t))]!)
        (f₁ := fun t s => s + A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 1)) +
          (n - 1 - (4 * g.toNat + 4 + t))]! * a[x.off + x.inc * (n - 1 - (4 * g.toNat + 4 + t))]!)
        (f₂ := fun t s => s + A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 2)) +
          (n - 1 - (4 * g.toNat + 4 + t))]! * a[x.off + x.inc * (n - 1 - (4 * g.toNat + 4 + t))]!)
        (f₃ := fun t s => s + A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 3)) +
          (n - 1 - (4 * g.toNat + 4 + t))]! * a[x.off + x.inc * (n - 1 - (4 * g.toNat + 4 + t))]!)]
      · simp only [Tail.run_writeThen, USize.toNat_zero, hm, iterRange_eq_fold]
        apply run_congr
        rw [trmvTUpperStep_eq_set!, iterRange_set!_four _ _ _ (fun r hr c c' hc =>
          trmvTUpperVal_congr d A x fun i hi => hc _ fun r' hr' =>
            idx_ne_of_ne x.inc_pos (by lia) (by lia) (by lia)) a]
        obtain ⟨v₀, v₁, v₂, v₃⟩ := trmvTUpperVal_four d A x hg4 a
        rw [v₀, v₁, v₂, v₃]
        simp only [t₀, t₁, t₂, t₃, set_eq_set!, getElem_eq_getElem!, uget_eq_getElem,
          getElem_def, j₀, j₁, j₂, j₃, Nat.add_zero]
      · intro t _ ht next' s₀ s₁ s₂ s₃
        rw [hm] at ht
        have hi : (n.toUSize - 1 - (4 * g + 4 + t)).toNat =
            n - 1 - (4 * g.toNat + 4 + t.toNat) := by
          grind
        have hp := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 4 + t)) (by lia)
        rw [hi] at hp
        simp only [Tail.run_readThen, hp, hi, getElem_eq_getElem!, uget_eq_getElem, getElem_def,
          j₀, j₁, j₂, j₃, Nat.add_zero]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are multiplied, and the others are unchanged.
-/
theorem iterRange_trmvTUpperStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k ≤ n) :
    iterRange (trmvTUpperStep d A x) 0 k x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v =>
        if n - k ≤ i then trmvTUpper d A x i else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, i ≤ n - 1 - k → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trmvTUpper d A x i else v)[x.off + x.inc * i]! =
        x.data[x.off + x.inc * i]! := by
      intro i hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt (by lia : i < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        ite_eq_right (by lia), getElem!_pos x.data _ (x.index_lt (by lia))]
    have ht : Nat.fold (n - 1 - k) (fun t _ s =>
          s + A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k - 1 - t)]! *
            (x.data.modifyAt x.stride.idx 0 n fun i v =>
              if n - k ≤ i then trmvTUpper d A x i else v)[x.off + x.inc * (n - 1 - k - 1 - t)]!)
          (d.mul (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if n - k ≤ i then trmvTUpper d A x i else v)[x.off + x.inc * (n - 1 - k)]!
            A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]!) = trmvTUpper d A x (n - 1 - k) := by
      rw [hr (n - 1 - k) (Nat.le_refl _), trmvTUpper]
      congr 1
      funext t ht s
      rw [hr (n - 1 - k - 1 - t) (by lia)]
    simp only [trmvTUpperStep, ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _
      (Nat.zero_le _) (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/-- The array of the transposed upper product is the array of `x` with its elements multiplied. -/
public theorem trmvTUpperData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTUpperData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvTUpper d A x i := by
  rw [trmvTUpperData_eq_iterRange, iterRange_trmvTUpperStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-! ## The transposed lower triangle -/

/--
The step `j` of the transposed lower product: set element `j` from the elements below it, which are
still those of `x`.
-/
@[expose] public def trmvTLowerStep (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat)
    (b : Float32Array) : Float32Array :=
  let t := Nat.fold (n - 1 - j) (fun t _ s =>
      s + A.data[A.off + A.ld * j + (j + 1 + t)]! * b[x.off + x.inc * (j + 1 + t)]!)
    (d.mul b[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The value of the step `j` of the transposed lower product, on the array `b`. -/
private def trmvTLowerVal (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (b : Float32Array) :
    Float32 :=
  Nat.fold (n - 1 - j) (fun t _ s =>
      s + A.data[A.off + A.ld * j + (j + 1 + t)]! * b[x.off + x.inc * (j + 1 + t)]!)
    (d.mul b[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)

private theorem trmvTLowerStep_eq_set! (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTLowerStep d A x = fun j b => b.set! (x.off + x.inc * j) (trmvTLowerVal d A x j b) := by
  funext j b
  rw [trmvTLowerStep, modifyAt_of_lt _ _ (Nat.lt_succ_self _), modifyAt_self, Vec.idx_stride]
  rfl

/-- The value of a step reads only the elements from its own on. -/
private theorem trmvTLowerVal_congr (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat}
    {b b' : Float32Array} (hj : j < n)
    (h : ∀ i, j ≤ i → i < n → b[x.off + x.inc * i]! = b'[x.off + x.inc * i]!) :
    trmvTLowerVal d A x j b = trmvTLowerVal d A x j b' := by
  unfold trmvTLowerVal
  rw [h _ (Nat.le_refl _) hj]
  congr 1
  funext t ht s
  rw [h _ (by lia) (by lia)]

/--
The value of the step `K + r`, for `r < 4`, of the transposed lower product: the terms of the
elements of the steps `K + r + 1` to `K + 3`, then the others.
-/
private theorem trmvTLowerVal_four (d : Diag) (A : Mat n n) (x : Vec n) {K : Nat} (hK : K + 3 < n)
    (b : Float32Array) :
    let w := fun r i => A.data[A.off + A.ld * (K + r) + (K + i)]!
    let y := fun i => b[x.off + x.inc * (K + i)]!
    let F := fun r t s => s + A.data[A.off + A.ld * (K + r) + (K + 4 + t)]! *
      b[x.off + x.inc * (K + 4 + t)]!
    trmvTLowerVal d A x K b = Nat.fold (n - 4 - K) (fun t _ s => F 0 t s)
        (((d.mul (y 0) (w 0 0) + w 0 1 * y 1) + w 0 2 * y 2) + w 0 3 * y 3) ∧
      trmvTLowerVal d A x (K + 1) b = Nat.fold (n - 4 - K) (fun t _ s => F 1 t s)
        ((d.mul (y 1) (w 1 1) + w 1 2 * y 2) + w 1 3 * y 3) ∧
      trmvTLowerVal d A x (K + 2) b = Nat.fold (n - 4 - K) (fun t _ s => F 2 t s)
        (d.mul (y 2) (w 2 2) + w 2 3 * y 3) ∧
      trmvTLowerVal d A x (K + 3) b = Nat.fold (n - 4 - K) (fun t _ s => F 3 t s)
        (d.mul (y 3) (w 3 3)) := by
  intro w y F
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold trmvTLowerVal
    rw [fold_split 3 (n - 4 - K) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia
  · unfold trmvTLowerVal
    rw [fold_split 2 (n - 4 - K) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia
  · unfold trmvTLowerVal
    rw [fold_split 1 (n - 4 - K) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, w, y, F]
    congr 1
    funext t ht s; congr 4 <;> lia
  · unfold trmvTLowerVal
    rw [Nat.fold_congr (show n - 1 - (K + 3) = n - 4 - K by lia)]

/--
The array of the transposed lower product: four elements per pass, then the rest one at a time.
-/
public def trmvTLowerData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let q4 := nu / 4
    have hq4 : q4.toNat = n / 4 := by simp only [q4, USize.toNat_div, hnu]; simp
    inplace a do
      for g in 0...q4 do
        have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
        have j₀ : (4 * g).toNat = 4 * g.toNat := by grind
        have j₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
        have j₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
        have j₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
        have k₀ : (o + c * (4 * g)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₁ : (o + c * (4 * g + 1)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₂ : (o + c * (4 * g + 2)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₃ : (o + c * (4 * g + 3)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        let y₀ := a[o + c * (4 * g)]
        let y₁ := a[o + c * (4 * g + 1)]
        let y₂ := a[o + c * (4 * g + 2)]
        let y₃ := a[o + c * (4 * g + 3)]
        let w := fun (r i : USize) (hr : (4 * g + r).toNat < n) (hi : (4 * g + i).toNat < n) =>
          A.uget ao al rfl rfl hs.1 (4 * g + i) (4 * g + r) hi hr
        for t in 0...(nu - 4 - 4 * g) with
            (s₀ := ((d.mul y₀ (A.uget ao al rfl rfl hs.1 (4 * g) (4 * g) (by lia) (by lia)) +
              w 0 1 (by grind) (by lia) * y₁) + w 0 2 (by grind) (by lia) * y₂) +
              w 0 3 (by grind) (by lia) * y₃)
            (s₁ := (d.mul y₁ (w 1 1 (by lia) (by lia)) + w 1 2 (by lia) (by lia) * y₂) +
              w 1 3 (by lia) (by lia) * y₃)
            (s₂ := d.mul y₂ (w 2 2 (by lia) (by lia)) + w 2 3 (by lia) (by lia) * y₃)
            (s₃ := d.mul y₃ (w 3 3 (by lia) (by lia))) do
          have hi : (4 * g + 4 + t).toNat < n := by grind
          have hk : (o + c * (4 * g + 4 + t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          let y := a[o + c * (4 * g + 4 + t)]
          s₀ := s₀ + A.uget ao al rfl rfl hs.1 (4 * g + 4 + t) (4 * g) hi (by lia) * y
          s₁ := s₁ + A.uget ao al rfl rfl hs.1 (4 * g + 4 + t) (4 * g + 1) hi (by lia) * y
          s₂ := s₂ + A.uget ao al rfl rfl hs.1 (4 * g + 4 + t) (4 * g + 2) hi (by lia) * y
          s₃ := s₃ + A.uget ao al rfl rfl hs.1 (4 * g + 4 + t) (4 * g + 3) hi (by lia) * y
        a[o + c * (4 * g)] := s₀
        a[o + c * (4 * g + 1)] := s₁
        a[o + c * (4 * g + 2)] := s₂
        a[o + c * (4 * g + 3)] := s₃
      for j in 4 * q4...nu do
        have hjn : j.toNat < n := by lia
        have hk : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * j]
        for t in 0...(nu - 1 - j) with (s := d.mul v (A.uget ao al rfl rfl hs.1 j j hjn hjn)) do
          have hi : (j + 1 + t).toNat < n := by grind
          have hk' : (o + c * (j + 1 + t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s + A.uget ao al rfl rfl hs.1 (j + 1 + t) j hi hjn * a[o + c * (j + 1 + t)]
        a[o + c * j] := s
  else iterRange (trmvTLowerStep d A x) 0 n x.data

public theorem trmvTLowerData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTLowerData d A x = iterRange (trmvTLowerStep d A x) 0 n x.data := by
  unfold trmvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hq4 : (n.toUSize / 4).toNat = n / 4 := by simp only [USize.toNat_div, hnu]; simp
    have h4q : (4 * (n.toUSize / 4)).toNat = 4 * (n / 4) := by grind
    have hF : ∀ j (b : Float32Array), (trmvTLowerStep d A x j b).size = b.size :=
      fun _ _ => size_modifyAt _ _ _ _ _
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit
      (F := fun g b => iterRange (trmvTLowerStep d A x) (4 * g) (4 * g + 4) b)
      (hF := fun _ _ => size_iterRange _ hF _ _ _)]
    · rw [Tail.run_forInFrom_unit (F := trmvTLowerStep d A x) (hF := hF)]
      · simp only [Tail.run_done, hq4, h4q, hnu, USize.toNat_zero]
        rw [iterRange_four, ← iterRange_split _ (Nat.zero_le _) (by lia)]
      · intro j hl hj next a h
        rw [hnu] at hj
        have hr : (n.toUSize - 1 - j).toNat = n - 1 - j.toNat := by grind
        simp only [Tail.run_readThen]
        rw [Tail.run_forInFrom (f := fun t p =>
            (p.1 + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + t)]! *
              p.2[x.off + x.inc * (j.toNat + 1 + t)]!, p.2))
          (hf := fun _ _ => rfl)]
        · simp only [USize.toNat_zero, Tail.run_writeThen, hr, iterRange_fst (fun t a s =>
            s + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + t)]! *
              a[x.off + x.inc * (j.toNat + 1 + t)]!)]
          congr 1
          have hp := x.toNat_index hs.2 hj
          rw [trmvTLowerStep,
            ← set_eq_modifyAt _ _ _ _ (by rw [Vec.idx_stride, h]; exact x.index_lt hj)]
          simp only [hp, Vec.idx_stride, uget_eq_getElem, getElem_def,
            getElem!_pos a (x.off + x.inc * j.toNat)
              (show _ < a.size by rw [h]; exact x.index_lt hj),
            getElem!_pos A.data (A.off + A.ld * j.toNat + j.toNat) (A.index_lt hj hj)]
        · intro t _ ht next' b a' h'
          simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
          rw [hr] at ht
          have hi : (j + 1 + t).toNat = j.toNat + 1 + t.toNat := by grind
          have hp : (x.off.toUSize + x.inc.toUSize * (j + 1 + t)).toNat =
              x.off + x.inc * (j.toNat + 1 + t.toNat) := by
            rw [x.toNat_index hs.2 (by lia), hi]
          simp only [hp, hi, getElem!_pos a' (x.off + x.inc * (j.toNat + 1 + t.toNat))
              (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
            getElem!_pos A.data (A.off + A.ld * j.toNat + (j.toNat + 1 + t.toNat))
              (A.index_lt (by lia) hj)]
    · intro g _ hg next a h
      rw [hq4] at hg
      have hg4 : 4 * g.toNat + 3 < n := by lia
      have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
      have j₀ : (4 * g).toNat = 4 * g.toNat := by grind
      have j₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
      have j₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
      have j₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
      have hm : (n.toUSize - 4 - 4 * g).toNat = n - 4 - 4 * g.toNat := by grind
      have t₀ := x.toNat_index hs.2 (i := 4 * g) (by lia)
      have t₁ := x.toNat_index hs.2 (i := 4 * g + 1) (by lia)
      have t₂ := x.toNat_index hs.2 (i := 4 * g + 2) (by lia)
      have t₃ := x.toNat_index hs.2 (i := 4 * g + 3) (by lia)
      rw [j₀] at t₀
      rw [j₁] at t₁
      rw [j₂] at t₂
      rw [j₃] at t₃
      simp only [Tail.run_readThen, Tail.forIn4_eq]
      rw [run_forIn4From_read
        (f₀ := fun t s => s + A.data[A.off + A.ld * (4 * g.toNat + 0) + (4 * g.toNat + 4 + t)]! *
          a[x.off + x.inc * (4 * g.toNat + 4 + t)]!)
        (f₁ := fun t s => s + A.data[A.off + A.ld * (4 * g.toNat + 1) + (4 * g.toNat + 4 + t)]! *
          a[x.off + x.inc * (4 * g.toNat + 4 + t)]!)
        (f₂ := fun t s => s + A.data[A.off + A.ld * (4 * g.toNat + 2) + (4 * g.toNat + 4 + t)]! *
          a[x.off + x.inc * (4 * g.toNat + 4 + t)]!)
        (f₃ := fun t s => s + A.data[A.off + A.ld * (4 * g.toNat + 3) + (4 * g.toNat + 4 + t)]! *
          a[x.off + x.inc * (4 * g.toNat + 4 + t)]!)]
      · simp only [Tail.run_writeThen, USize.toNat_zero, hm, iterRange_eq_fold]
        apply run_congr
        rw [trmvTLowerStep_eq_set!, iterRange_set!_four _ _ _ (fun r hr c c' hc =>
          trmvTLowerVal_congr d A x (by lia) fun i hi hin => hc _ fun r' hr' =>
            idx_ne_of_ne x.inc_pos (by lia) (by lia) (by lia)) a]
        obtain ⟨v₀, v₁, v₂, v₃⟩ := trmvTLowerVal_four d A x hg4 a
        rw [v₀, v₁, v₂, v₃]
        have j₀' : (4 * g + 0).toNat = 4 * g.toNat := by grind
        simp only [t₀, t₁, t₂, t₃, set_eq_set!, getElem_eq_getElem!, uget_eq_getElem,
          getElem_def, j₀, j₀', j₁, j₂, j₃, Nat.add_zero]
      · intro t _ ht next' s₀ s₁ s₂ s₃
        rw [hm] at ht
        have hi : (4 * g + 4 + t).toNat = 4 * g.toNat + 4 + t.toNat := by grind
        have hp := x.toNat_index hs.2 (i := 4 * g + 4 + t) (by lia)
        rw [hi] at hp
        simp only [Tail.run_readThen, hp, hi, getElem_eq_getElem!, uget_eq_getElem, getElem_def,
          j₀, j₁, j₂, j₃, Nat.add_zero]
  · rfl

/-- After the steps `i < j`, the elements `i < j` are multiplied, and the others are unchanged. -/
theorem iterRange_trmvTLowerStep (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (hj : j ≤ n) :
    iterRange (trmvTLowerStep d A x) 0 j x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v => if i < j then trmvTLower d A x i else v := by
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, j ≤ i → i < n → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if i < j then trmvTLower d A x i else v)[x.off + x.inc * i]! =
        x.data[x.off + x.inc * i]! := by
      intro i hi hn
      rw [getElem!_pos _ _ (by simpa using x.index_lt hn),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) hn,
        ite_eq_right (by lia), getElem!_pos x.data _ (x.index_lt hn)]
    have ht : Nat.fold (n - 1 - j) (fun t _ s => s + A.data[A.off + A.ld * j + (j + 1 + t)]! *
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if i < j then trmvTLower d A x i else v)[x.off + x.inc * (j + 1 + t)]!)
          (d.mul (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if i < j then trmvTLower d A x i else v)[x.off + x.inc * j]!
            A.data[A.off + A.ld * j + j]!) = trmvTLower d A x j := by
      rw [hr j (Nat.le_refl _) (by lia), trmvTLower]
      congr 1
      funext t ht s
      rw [hr (j + 1 + t) (by lia) (by lia)]
    simp only [trmvTLowerStep, ht]
    rw [modifyAt_widen (lo := j) (hi := j + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _)
      (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < j
    · simp [h₁, show i < j + 1 by lia, show ¬j ≤ i by lia]
    · by_cases h₂ : i = j
      · subst h₂; simp
      · simp [h₁, show ¬i < j + 1 by lia]

/-- The array of the transposed lower product is the array of `x` with its elements multiplied. -/
public theorem trmvTLowerData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTLowerData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvTLower d A x i := by
  rw [trmvTLowerData_eq_iterRange, iterRange_trmvTLowerStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp [hi]

/-! ## `trmv` and `trmvT` -/

/-- The product `A * x` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trmvProd (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Nat → Float32 :=
  match uplo with
  | .upper => trmvUpper d A x
  | .lower => trmvLower d A x

/-- The array of `trmv`. -/
@[expose] public def trmvData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  match uplo with
  | .upper => trmvUpperData d A x
  | .lower => trmvLowerData d A x

public theorem trmvData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvData uplo d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvProd uplo d A x i := by
  cases uplo
  · exact trmvUpperData_eq d A x
  · exact trmvLowerData_eq d A x

/--
`trmv uplo d A x` is `A * x` for the triangle `uplo` of `A`, with a unit diagonal if `d` is
`.unit`, by the column-oriented loops of the reference BLAS. For the upper triangle, it adds `x[j]`
times column `j` of `A` to the elements above `j` and multiplies element `j` by `A[j, j]`, for
`j = 0, …, n - 1`; for the lower triangle, it does the same from `j = n - 1` down to `0`, with the
elements below. It updates `x` in place when its array is not shared, and leaves the elements of
the array outside `x` unchanged. It reads only the triangle `uplo` of `A`, and not its diagonal
when `d` is `.unit`.
-/
@[expose] public def trmv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Vec n where
  data := trmvData uplo d A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [trmvData_eq, size_modifyAt]; exact x.bound

/-- The array of `trmv uplo d A x` is the array of `x` with its elements multiplied. -/
public theorem data_trmv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trmv uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvProd uplo d A x i :=
  trmvData_eq uplo d A x

@[simp] public theorem off_trmv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trmv uplo d A x).off = x.off := rfl

@[simp] public theorem inc_trmv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trmv uplo d A x).inc = x.inc := rfl

/-- Element `i` of `trmv uplo d A x` is element `i` of the model. -/
public theorem getElem_trmv (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (h : i < n) : (trmv uplo d A x)[i] = trmvProd uplo d A x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_trmv uplo d A x) rfl rfl i h

/--
Element `i` of `trmv .upper d A x` is `x[i] * A[i, i]`, or `x[i]` for a unit diagonal, plus the
terms `x[j] * A[i, j]` for `j = i + 1, …, n - 1`.
-/
public theorem getElem_trmv_upper (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) (h : i < n) :
    (trmv .upper d A x)[i] = Nat.fold (n - 1 - i) (fun t _ s =>
      s + x[i + 1 + t]'(by lia) * A[(i, i + 1 + t)]'⟨h, by lia⟩) (d.mul x[i] A[(i, i)]) := by
  rw [getElem_trmv _ _ _ _ _ h, trmvProd, trmvUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt h (by lia))]
  rfl

/--
Element `i` of `trmv .lower d A x` is `x[i] * A[i, i]`, or `x[i]` for a unit diagonal, plus the
terms `x[j] * A[i, j]` for `j = i - 1, …, 0`.
-/
public theorem getElem_trmv_lower (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat) (h : i < n) :
    (trmv .lower d A x)[i] = Nat.fold i (fun t _ s =>
      s + x[i - 1 - t]'(by lia) * A[(i, i - 1 - t)]'⟨h, by lia⟩) (d.mul x[i] A[(i, i)]) := by
  rw [getElem_trmv _ _ _ _ _ h, trmvProd, trmvLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt h (by lia))]
  rfl

/-- The product `Aᵀ * x` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trmvTProd (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Nat → Float32 :=
  match uplo with
  | .upper => trmvTUpper d A x
  | .lower => trmvTLower d A x

/-- The array of `trmvT`. -/
@[expose] public def trmvTData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Float32Array :=
  match uplo with
  | .upper => trmvTUpperData d A x
  | .lower => trmvTLowerData d A x

public theorem trmvTData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTData uplo d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvTProd uplo d A x i := by
  cases uplo
  · exact trmvTUpperData_eq d A x
  · exact trmvTLowerData_eq d A x

/--
`trmvT uplo d A x` is `Aᵀ * x` for the triangle `uplo` of `A`, with a unit diagonal if `d` is
`.unit`, by the loops of the reference BLAS for `TRANS = 'T'`. For the upper triangle, it sets
element `j` to `x[j] * A[j, j]` plus the dot product of the elements `j - 1, …, 0` of column `j` of
`A` and of `x`, for `j = n - 1` down to `0`; for the lower triangle, it does the same for
`j = 0, …, n - 1`, with the elements `j + 1, …, n - 1`. It updates `x` in place when its array is
not shared, and leaves the elements of the array outside `x` unchanged. It reads only the triangle
`uplo` of `A`, and not its diagonal when `d` is `.unit`.
-/
@[expose] public def trmvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Vec n where
  data := trmvTData uplo d A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [trmvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `trmvT uplo d A x` is the array of `x` with its elements multiplied. -/
public theorem data_trmvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trmvT uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => trmvTProd uplo d A x i :=
  trmvTData_eq uplo d A x

@[simp] public theorem off_trmvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trmvT uplo d A x).off = x.off := rfl

@[simp] public theorem inc_trmvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trmvT uplo d A x).inc = x.inc := rfl

/-- Element `j` of `trmvT uplo d A x` is element `j` of the model. -/
public theorem getElem_trmvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat)
    (h : j < n) : (trmvT uplo d A x)[j] = trmvTProd uplo d A x j :=
  Vec.getElem_of_data_eq_modifyAt _ (data_trmvT uplo d A x) rfl rfl j h

/--
Element `j` of `trmvT .upper d A x` is `x[j] * A[j, j]`, or `x[j]` for a unit diagonal, plus the
terms `A[i, j] * x[i]` for `i = j - 1, …, 0`.
-/
public theorem getElem_trmvT_upper (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (h : j < n) :
    (trmvT .upper d A x)[j] = Nat.fold j (fun t _ s =>
      s + A[(j - 1 - t, j)]'⟨by lia, h⟩ * x[j - 1 - t]'(by lia)) (d.mul x[j] A[(j, j)]) := by
  rw [getElem_trmvT _ _ _ _ _ h, trmvTProd, trmvTUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
Element `j` of `trmvT .lower d A x` is `x[j] * A[j, j]`, or `x[j]` for a unit diagonal, plus the
terms `A[i, j] * x[i]` for `i = j + 1, …, n - 1`.
-/
public theorem getElem_trmvT_lower (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (h : j < n) :
    (trmvT .lower d A x)[j] = Nat.fold (n - 1 - j) (fun t _ s =>
      s + A[(j + 1 + t, j)]'⟨by lia, h⟩ * x[j + 1 + t]'(by lia)) (d.mul x[j] A[(j, j)]) := by
  rw [getElem_trmvT _ _ _ _ _ h, trmvTProd, trmvTLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

end Mat

end BLAS.Float32
