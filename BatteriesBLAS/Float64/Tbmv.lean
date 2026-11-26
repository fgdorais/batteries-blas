/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float64.Gbmv
public import BatteriesBLAS.Float64.Trmv
import all BatteriesBLAS.Internal

/-!
# Triangular band matrix-vector product

A triangular band matrix with `k` off-diagonals is stored as in the reference BLAS, in a matrix
`A : Mat (k + 1) n`: for the upper triangle, the element in row `i` and column `j`, for
`j - k ≤ i ≤ j`, is in row `k + i - j` of column `j` of `A`, so that the diagonal is row `k`; for
the lower triangle, the element for `j ≤ i ≤ j + k` is in row `i - j`, so that the diagonal is row
`0`. The other elements of `A` are not part of the matrix, and the routines don't read them.

`Mat.tbmv uplo d A x` computes `A * x` and `Mat.tbmvT uplo d A x` computes `Aᵀ * x`, over `x`, by
the loops of the reference BLAS (`dtbmv`), as `Mat.trmv` and `Mat.trmvT` do for a full triangle:
each element of the result is its diagonal term, `x[i] * A[i, i]` or `x[i]` for a unit diagonal,
plus the terms of the other elements of its row (its column for `tbmvT`) in the band, in the order
of the loops, which read only elements of `x` that they haven't overwritten yet.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {n : Nat}

/-! ## The loops -/

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged.
-/
private theorem iterRange_fst (g : Nat → Float64Array → Float → Float) (k : Nat) (t : Float)
    (a : Float64Array) :
    iterRange (fun i p => (g i p.2 p.1, p.2)) 0 k (t, a) =
      (Nat.fold k (fun i _ s => g i a s) t, a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/-- The `USize` index of the row `j - min j k + l` above the diagonal of column `j`. -/
private theorem above_index (x : Vec n) (hs : x.data.size < USize.size) {k : Nat} {j l : USize}
    (hj : j.toNat < n) (hl : l.toNat < (bandAbove k j).toNat) :
    (x.off.toUSize + x.inc.toUSize * (j - bandAbove k j + l)).toNat =
      x.off + x.inc * (j.toNat - min j.toNat k + l.toNat) := by
  have h := toNat_sub_bandAbove_add hl
  rw [x.toNat_index hs (by rw [h.1]; lia), h.1]

/-- The `USize` index of the row `j + 1 + l` below the diagonal of column `j`. -/
private theorem below_index (x : Vec n) (hs : x.data.size < USize.size) {k : Nat} {j l : USize}
    (hj : j.toNat < n) (hl : l.toNat < (bandBelow n k j).toNat) :
    (x.off.toUSize + x.inc.toUSize * (j + 1 + l)).toNat = x.off + x.inc * (j.toNat + 1 + l.toNat) :=
  by
  have h := toNat_bandBelow_add (Nat.lt_of_le_of_lt x.le_size hs) hj hl
  rw [x.toNat_index hs (by rw [h.1]; exact h.2), h.1]

/-! ## The upper triangle -/

/--
The map of step `j` of the upper product on element `i`, when `x[j]` is `t` as the step starts:
multiply element `j` by the diagonal, and add `t` times column `j` of the band to the elements
above it.
-/
@[expose] public def tbmvUpperG (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (t : Float)
    (i : Nat) (v : Float) : Float :=
  if i = j then d.mul v A.data[A.off + A.ld * j + k]!
  else if j - min j k ≤ i ∧ i < j - min j k + min j k then
    v + t * A.data[A.off + A.ld * j + (k + i - j)]!
  else v

/-- The step `j` of the upper product. -/
@[expose] public def tbmvUpperStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n (tbmvUpperG d k A j c[x.stride.idx j]!)

/-- The array of the upper product. -/
public def tbmvUpperData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let ku := k.toUSize
    inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        have hku : ku.toNat = k := toNat_toUSize_of_lt (by
          have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
        have hq : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let t := a[o + c * j]
        let lo := j - bandAbove k j
        let r0 := ku - bandAbove k j
        for l in 0...bandAbove k j do
          have hl := toNat_sub_bandAbove_add (by assumption)
          have hr := toNat_sub_bandAbove_add' hku (by assumption)
          have hi : (lo + l).toNat < n := hl.1 ▸ Nat.lt_trans hl.2 hjn
          have hq' : (o + c * (lo + l)).toNat < a.size := x.toNat_index_lt hs.2 hi
          a[o + c * (lo + l)] :=
            a[o + c * (lo + l)] + t * A.uget ao al rfl rfl hs.1 (r0 + l) j (by rw [hr.1]; lia) hjn
        a[o + c * j] := d.mul a[o + c * j] (A.uget ao al rfl rfl hs.1 ku j (by lia) hjn)
  else iterRange (tbmvUpperStep d k A x) 0 n x.data

public theorem tbmvUpperData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvUpperData d k A x = iterRange (tbmvUpperStep d k A x) 0 n x.data := by
  unfold tbmvUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbmvUpperStep d k A x)
      (hF := fun _ _ => by unfold tbmvUpperStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hku : k.toUSize.toNat = k :=
        toNat_toUSize_of_lt (by have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
      have hp := x.toNat_index hs.2 hj
      have hab := toNat_bandAbove k j
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom_modify
        (idx := fun l => x.off + x.inc * (j.toNat - min j.toNat k + l))
        (he := fun l _ hl => above_index x hs.2 hj hl)
        (G := fun l v => v + a[x.off + x.inc * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]!)]
      · simp only [Tail.run_readThen, Tail.run_writeThen]
        congr 1
        simp only [USize.toNat_zero, hab, uget_eq_getElem, getElem_def, hp, hku]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_modifyAt_band x a h (j.toNat - min j.toNat k) (min j.toNat k) j.toNat (by lia) hj
          (by lia) _ (fun v => d.mul v A.data[A.off + A.ld * j.toNat + k]!), tbmvUpperStep]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [tbmvUpperG, Vec.idx_stride]
        by_cases h₁ : i = j.toNat
        · simp only [h₁, ↓reduceIte]
        · simp only [h₁, ↓reduceIte]
          split
          · rw [show k - min j.toNat k + (i - (j.toNat - min j.toNat k)) = k + i - j.toNat by lia]
          · rfl
      · intro l _ hl v
        have hr := toNat_sub_bandAbove_add' hku hl
        simp only [uget_eq_getElem, getElem_def, hp, hr.1, getElem_eq_getElem!]
  · rfl

/--
Element `i` of `A * x` for the upper band of `A`, on the arrays: `x[i] * A[k, i]`, or `x[i]` for a
unit diagonal, plus the terms `x[j] * A[k + i - j, j]` for `j = i + 1, …, i + min (n - 1 - i) k`.
-/
@[expose] public def tbmvUpper (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (i : Nat) :
    Float :=
  Nat.fold (min (n - 1 - i) k) (fun t _ s =>
      s + x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + (k - 1 - t)]!)
    (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i + k]!)

/-- The array of the upper product is the array of `x` with its elements multiplied. -/
public theorem tbmvUpperData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvUpperData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvUpper d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbmvUpperData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) n (fun j hj => hj) (tbmvUpperG d k A)).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  apply modifyAt_congr_fun
  intro i v _ hi
  have hread : ∀ j, j < n → selfRead x.data x.stride.idx (fun j => j) (tbmvUpperG d k A) j =
      x.data[x.off + x.inc * j]! := fun j _ =>
    selfRead_eq_of_fix _ _ _ _ fun j' hj' t v => by
      simp only [tbmvUpperG]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
        ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
  rw [show (fun j (hj : j < n) v => tbmvUpperG d k A j
        (selfRead x.data x.stride.idx (fun j => j) (tbmvUpperG d k A) j) i v) =
      fun j _ v => tbmvUpperG d k A j x.data[x.off + x.inc * j]! i v from by
    funext j hj v; rw [hread j hj]]
  simp only [tbmvUpperG]
  rw [fold_upper_band hi k (fun j s => d.mul s A.data[A.off + A.ld * j + k]!)
    (fun j s => s + x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (k + i - j)]!),
    tbmvUpper]
  congr 1
  funext t ht s
  rw [show k + i - (i + 1 + t) = k - 1 - t by lia]

/-! ## The lower triangle -/

/--
The map of step `j` of the lower product on element `i`, when `x[j]` is `t` as the step starts:
multiply element `j` by the diagonal, and add `t` times column `j` of the band to the elements
below it.
-/
@[expose] public def tbmvLowerG (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (t : Float)
    (i : Nat) (v : Float) : Float :=
  if i = j then d.mul v A.data[A.off + A.ld * j]!
  else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then
    v + t * A.data[A.off + A.ld * j + (i - j)]!
  else v

/-- The step `kk` of the lower product, for the column `n - 1 - kk`. -/
@[expose] public def tbmvLowerStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (kk : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n (tbmvLowerG d k A (n - 1 - kk) c[x.stride.idx (n - 1 - kk)]!)

/-- The array of the lower product. -/
public def tbmvLowerData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    inplace a do
      for kk in 0...nu do
        have hj : (nu - 1 - kk).toNat = n - 1 - kk.toNat := by grind
        have hjn : (nu - 1 - kk).toNat < n := by lia
        have hq : (o + c * (nu - 1 - kk)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let t := a[o + c * (nu - 1 - kk)]
        for l in 0...bandBelow n k (nu - 1 - kk) do
          have hl := toNat_bandBelow_add hn hjn (by assumption)
          have hr := toNat_one_add_bandBelow (k := k) hn (by assumption)
          have hi : (nu - 1 - kk + 1 + l).toNat < n := hl.1 ▸ hl.2
          have hq' : (o + c * (nu - 1 - kk + 1 + l)).toNat < a.size := x.toNat_index_lt hs.2 hi
          a[o + c * (nu - 1 - kk + 1 + l)] := a[o + c * (nu - 1 - kk + 1 + l)] +
            t * A.uget ao al rfl rfl hs.1 (1 + l) (nu - 1 - kk) (hr.1 ▸ hr.2) hjn
        a[o + c * (nu - 1 - kk)] :=
          d.mul a[o + c * (nu - 1 - kk)]
            (A.uget ao al rfl rfl hs.1 0 (nu - 1 - kk) (by simp) hjn)
  else iterRange (tbmvLowerStep d k A x) 0 n x.data

public theorem tbmvLowerData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvLowerData d k A x = iterRange (tbmvLowerStep d k A x) 0 n x.data := by
  unfold tbmvLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbmvLowerStep d k A x)
      (hF := fun _ _ => by unfold tbmvLowerStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
          x.off + x.inc * (n - 1 - kk.toNat) := by
        rw [x.toNat_index hs.2 hjn, hj]
      have hbe := toNat_bandBelow hn k (n.toUSize - 1 - kk)
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk + 1 + l))
        (idx := fun l => x.off + x.inc * (n - 1 - kk.toNat + 1 + l))
        (he := fun l _ hl => by rw [below_index (k := k) x hs.2 hjn hl, hj])
        (G := fun l v => v + a[x.off + x.inc * (n - 1 - kk.toNat)]! *
          A.data[A.off + A.ld * (n - 1 - kk.toNat) + (1 + l)]!)]
      · simp only [Tail.run_readThen, Tail.run_writeThen]
        congr 1
        simp only [USize.toNat_zero, hbe, hj, uget_eq_getElem, getElem_def, hp, USize.toNat_zero,
          Nat.add_zero]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_modifyAt_band x a h (n - 1 - kk.toNat + 1) (min (n - 1 - (n - 1 - kk.toNat)) k)
          (n - 1 - kk.toNat) (by lia) (by lia) (by lia) _
          (fun v => d.mul v A.data[A.off + A.ld * (n - 1 - kk.toNat)]!), tbmvLowerStep]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [tbmvLowerG, Vec.idx_stride]
        by_cases h₁ : i = n - 1 - kk.toNat
        · simp only [h₁, ↓reduceIte]
        · simp only [h₁, ↓reduceIte]
          split
          · rw [show 1 + (i - (n - 1 - kk.toNat + 1)) = i - (n - 1 - kk.toNat) by lia]
          · rfl
      · intro l _ hl v
        have hr := toNat_one_add_bandBelow (k := k) hn hl
        simp only [uget_eq_getElem, getElem_def, hp, hr.1, hj, getElem_eq_getElem!]
  · rfl

/--
Element `i` of `A * x` for the lower band of `A`, on the arrays: `x[i] * A[0, i]`, or `x[i]` for a
unit diagonal, plus the terms `x[j] * A[i - j, j]` for `j = i - 1, …, i - min i k`.
-/
@[expose] public def tbmvLower (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (i : Nat) :
    Float :=
  Nat.fold (min i k) (fun t _ s =>
      s + x.data[x.off + x.inc * (i - 1 - t)]! * A.data[A.off + A.ld * (i - 1 - t) + (1 + t)]!)
    (d.mul x.data[x.off + x.inc * i]! A.data[A.off + A.ld * i]!)

/-- The array of the lower product is the array of `x` with its elements multiplied. -/
public theorem tbmvLowerData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvLowerData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvLower d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbmvLowerData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) n (fun kk hkk => by lia)
    (fun kk => tbmvLowerG d k A (n - 1 - kk))).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  apply modifyAt_congr_fun
  intro i v _ hi
  have hread : ∀ kk, kk < n → selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
      (fun kk => tbmvLowerG d k A (n - 1 - kk)) kk = x.data[x.off + x.inc * (n - 1 - kk)]! :=
    fun kk _ => selfRead_eq_of_fix _ _ _ _ fun kk' hkk' t v => by
      simp only [tbmvLowerG]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
        ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
  rw [show (fun kk (hkk : kk < n) v => tbmvLowerG d k A (n - 1 - kk)
        (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
          (fun kk => tbmvLowerG d k A (n - 1 - kk)) kk) i v) =
      fun kk _ v => tbmvLowerG d k A (n - 1 - kk) x.data[x.off + x.inc * (n - 1 - kk)]! i v from by
    funext kk hkk v; rw [hread kk hkk]]
  simp only [tbmvLowerG]
  rw [fold_lower_band_rev hi k (fun j s => d.mul s A.data[A.off + A.ld * j]!)
    (fun j s => s + x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (i - j)]!),
    tbmvLower]
  congr 1
  funext t ht s
  rw [show i - (i - 1 - t) = 1 + t by lia]

/-! ## The transposed upper triangle -/

/--
The value that the step for column `j` of the transposed upper product writes at element `j`, from
the elements `get q` of `x`: `get j * A[k, j]`, or `get j` for a unit diagonal, plus the terms
`A[k + i - j, j] * get i` for `i = j - 1, …, j - min j k`.
-/
@[expose] public def tbmvTUpperH (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat)
    (get : Nat → Float) : Float :=
  Nat.fold (min j k) (fun t _ s => s + A.data[A.off + A.ld * j + (k - 1 - t)]! * get (j - 1 - t))
    (d.mul (get j) A.data[A.off + A.ld * j + k]!)

/-- The step `kk` of the transposed upper product, for the column `n - 1 - kk`. -/
@[expose] public def tbmvTUpperStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (kk : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = n - 1 - kk then tbmvTUpperH d k A (n - 1 - kk) (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed upper product. -/
public def tbmvTUpperData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let ku := k.toUSize
    inplace a do
      for kk in 0...nu do
        have hj : (nu - 1 - kk).toNat = n - 1 - kk.toNat := by grind
        have hjn : (nu - 1 - kk).toNat < n := by lia
        have hku : ku.toNat = k := toNat_toUSize_of_lt (by
          have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
        have hq : (o + c * (nu - 1 - kk)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - kk)]
        for t in 0...bandAbove k (nu - 1 - kk) with
            (s := d.mul v (A.uget ao al rfl rfl hs.1 ku (nu - 1 - kk) (by lia) hjn)) do
          have ht := toNat_sub_one_sub_bandAbove (by assumption)
          have hr := toNat_sub_one_sub_bandAbove' hku (by assumption)
          have hi : (nu - 1 - kk - 1 - t).toNat < n := ht.1 ▸ Nat.lt_trans ht.2 hjn
          have hq' : (o + c * (nu - 1 - kk - 1 - t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s + A.uget ao al rfl rfl hs.1 (ku - 1 - t) (nu - 1 - kk) (by rw [hr.1]; lia) hjn *
            a[o + c * (nu - 1 - kk - 1 - t)]
        a[o + c * (nu - 1 - kk)] := s
  else iterRange (tbmvTUpperStep d k A x) 0 n x.data

public theorem tbmvTUpperData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvTUpperData d k A x = iterRange (tbmvTUpperStep d k A x) 0 n x.data := by
  unfold tbmvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbmvTUpperStep d k A x)
      (hF := fun _ _ => by unfold tbmvTUpperStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hku : k.toUSize.toNat = k :=
        toNat_toUSize_of_lt (by have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
      have hab := toNat_bandAbove k (n.toUSize - 1 - kk)
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 + A.data[A.off + A.ld * (n - 1 - kk.toNat) + (k - 1 - t)]! *
            p.2[x.off + x.inc * (n - 1 - kk.toNat - 1 - t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hab, hj, iterRange_fst (fun t a s =>
          s + A.data[A.off + A.ld * (n - 1 - kk.toNat) + (k - 1 - t)]! *
            a[x.off + x.inc * (n - 1 - kk.toNat - 1 - t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat) := by
          rw [x.toNat_index hs.2 hjn, hj]
        simp only [hp, uget_eq_getElem, getElem_def, hj, hku]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h (by lia), tbmvTUpperStep]
        rfl
      · intro t _ ht next' b a' h'
        rw [hab] at ht
        have ht' := toNat_sub_one_sub_bandAbove (k := k) (j := n.toUSize - 1 - kk) (t := t)
          (by rw [hab]; exact ht)
        have hr := toNat_sub_one_sub_bandAbove' (k := k) (j := n.toUSize - 1 - kk) (t := t) hku
          (by rw [hab]; exact ht)
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk - 1 - t)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat - 1 - t.toNat) := by
          rw [x.toNat_index hs.2 (by rw [ht'.1]; lia), ht'.1, hj]
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def, hp, hr.1, hj,
          getElem_eq_getElem!]
  · rfl

/--
Element `j` of `Aᵀ * x` for the upper band of `A`, on the arrays: `x[j] * A[k, j]`, or `x[j]` for a
unit diagonal, plus the terms `A[k + i - j, j] * x[i]` for `i = j - 1, …, j - min j k`.
-/
@[expose] public def tbmvTUpper (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat) :
    Float :=
  tbmvTUpperH d k A j fun q => x.data[x.off + x.inc * q]!

/-- The array of the transposed upper product is the array of `x` with its elements multiplied. -/
public theorem tbmvTUpperData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvTUpperData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvTUpper d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbmvTUpperData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) (fun q => n - 1 - q) (fun kk hkk => by lia) (fun q hq => by lia)
    (fun kk => tbmvTUpperH d k A (n - 1 - kk)) (fun kk hkk get get' hget => by
      simp only [tbmvTUpperH]
      rw [hget _ (by lia)]
      congr 1
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)), writeRead,
    show n - 1 - (n - 1 - i) = i by lia, tbmvTUpper, tbmvTUpperH, tbmvTUpperH,
    dite_eq_right (show ¬n - 1 - i < n - 1 - i by lia)]
  congr 1
  funext t ht s
  rw [dite_eq_right (show ¬n - 1 - (i - 1 - t) < n - 1 - i by lia)]
  rfl

/-! ## The transposed lower triangle -/

/--
The value that the step for column `j` of the transposed lower product writes at element `j`, from
the elements `get q` of `x`: `get j * A[0, j]`, or `get j` for a unit diagonal, plus the terms
`A[i - j, j] * get i` for `i = j + 1, …, j + min (n - 1 - j) k`.
-/
@[expose] public def tbmvTLowerH (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat)
    (get : Nat → Float) : Float :=
  Nat.fold (min (n - 1 - j) k) (fun t _ s =>
      s + A.data[A.off + A.ld * j + (1 + t)]! * get (j + 1 + t))
    (d.mul (get j) A.data[A.off + A.ld * j]!)

/-- The step `j` of the transposed lower product. -/
@[expose] public def tbmvTLowerStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = j then tbmvTLowerH d k A j (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed lower product. -/
public def tbmvTLowerData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    inplace a do
      for j in 0...nu do
        have hjn : j.toNat < n := by lia
        have hq : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * j]
        for t in 0...bandBelow n k j with
            (s := d.mul v (A.uget ao al rfl rfl hs.1 0 j (by simp) hjn)) do
          have hl := toNat_bandBelow_add hn hjn (by assumption)
          have hr := toNat_one_add_bandBelow (k := k) hn (by assumption)
          have hi : (j + 1 + t).toNat < n := hl.1 ▸ hl.2
          have hq' : (o + c * (j + 1 + t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s + A.uget ao al rfl rfl hs.1 (1 + t) j (hr.1 ▸ hr.2) hjn * a[o + c * (j + 1 + t)]
        a[o + c * j] := s
  else iterRange (tbmvTLowerStep d k A x) 0 n x.data

public theorem tbmvTLowerData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvTLowerData d k A x = iterRange (tbmvTLowerStep d k A x) 0 n x.data := by
  unfold tbmvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbmvTLowerStep d k A x)
      (hF := fun _ _ => by unfold tbmvTLowerStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hbe := toNat_bandBelow hn k j
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 + A.data[A.off + A.ld * j.toNat + (1 + t)]! *
            p.2[x.off + x.inc * (j.toNat + 1 + t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hbe, iterRange_fst (fun t a s =>
          s + A.data[A.off + A.ld * j.toNat + (1 + t)]! * a[x.off + x.inc * (j.toNat + 1 + t)]!)]
        congr 1
        have hp := x.toNat_index hs.2 hj
        simp only [hp, uget_eq_getElem, getElem_def, USize.toNat_zero, Nat.add_zero]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h hj, tbmvTLowerStep]
        rfl
      · intro t _ ht next' b a' h'
        rw [hbe] at ht
        have hl := toNat_bandBelow_add (k := k) hn hj (l := t) (by rw [hbe]; exact ht)
        have hr := toNat_one_add_bandBelow (k := k) hn (j := j) (l := t) (by rw [hbe]; exact ht)
        have hp : (x.off.toUSize + x.inc.toUSize * (j + 1 + t)).toNat =
            x.off + x.inc * (j.toNat + 1 + t.toNat) := below_index x hs.2 hj (by rw [hbe]; exact ht)
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def, hp, hr.1, getElem_eq_getElem!]
  · rfl

/--
Element `j` of `Aᵀ * x` for the lower band of `A`, on the arrays: `x[j] * A[0, j]`, or `x[j]` for a
unit diagonal, plus the terms `A[i - j, j] * x[i]` for `i = j + 1, …, j + min (n - 1 - j) k`.
-/
@[expose] public def tbmvTLower (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat) :
    Float :=
  tbmvTLowerH d k A j fun q => x.data[x.off + x.inc * q]!

/-- The array of the transposed lower product is the array of `x` with its elements multiplied. -/
public theorem tbmvTLowerData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvTLowerData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvTLower d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbmvTLowerData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) (fun q => q) (fun j _ => rfl) (fun q _ => rfl)
    (fun j => tbmvTLowerH d k A j) (fun j hj get get' hget => by
      simp only [tbmvTLowerH]
      rw [hget _ hj]
      congr 1
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi), writeRead, tbmvTLower, tbmvTLowerH, tbmvTLowerH,
    dite_eq_right (Nat.lt_irrefl i)]
  congr 1
  funext t ht s
  rw [dite_eq_right (show ¬i + 1 + t < i by lia)]
  rfl

/-! ## `tbmv` and `tbmvT` -/

/-- The product `A * x` for the band of the triangle `uplo` of `A`, element by element. -/
@[expose] public def tbmvProd (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => tbmvUpper d k A x
  | .lower => tbmvLower d k A x

/-- The array of `tbmv`. -/
@[expose] public def tbmvData (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => tbmvUpperData d k A x
  | .lower => tbmvLowerData d k A x

public theorem tbmvData_eq (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvData uplo d k A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvProd uplo d k A x i := by
  cases uplo
  · exact tbmvUpperData_eq d k A x
  · exact tbmvLowerData_eq d k A x

/--
`tbmv uplo d A x` is `A * x` for the triangular band matrix with `k` off-diagonals stored by its
triangle `uplo` in `A : Mat (k + 1) n`, with a unit diagonal if `d` is `.unit`, by the
column-oriented loops of the reference BLAS (`dtbmv` with `TRANS = 'N'`). For the upper triangle,
it adds `x[j]` times column `j` of the band to the elements above `j` and multiplies element `j` by
the diagonal, for `j = 0, …, n - 1`; for the lower triangle, it does the same from `j = n - 1` down
to `0`, with the elements below. It updates `x` in place when its array is not shared, leaves the
elements of the array outside `x` unchanged, and reads only the band, and not its diagonal when `d`
is `.unit`.
-/
@[expose] public def tbmv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    Vec n where
  data := tbmvData uplo d k A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tbmvData_eq, size_modifyAt]; exact x.bound

/-- The array of `tbmv uplo d A x` is the array of `x` with its elements multiplied. -/
public theorem data_tbmv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    (tbmv uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvProd uplo d k A x i :=
  tbmvData_eq uplo d k A x

@[simp] public theorem off_tbmv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbmv uplo d A x).off = x.off := rfl

@[simp] public theorem inc_tbmv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbmv uplo d A x).inc = x.inc := rfl

/-- Element `i` of `tbmv uplo d A x` is element `i` of the model. -/
public theorem getElem_tbmv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (h : i < n) : (tbmv uplo d A x)[i] = tbmvProd uplo d k A x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tbmv uplo d A x) rfl rfl i h

/--
Element `i` of `tbmv .upper d A x` is `x[i] * A[k, i]`, or `x[i]` for a unit diagonal, plus the
terms `x[i + 1 + t] * A[k - 1 - t, i + 1 + t]` for `t < min (n - 1 - i) k`.
-/
public theorem getElem_tbmv_upper (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tbmv .upper d A x)[i] = Nat.fold (min (n - 1 - i) k) (fun t _ s =>
      s + x[i + 1 + t]'(by lia) * A[(k - 1 - t, i + 1 + t)]'⟨by lia, by lia⟩)
      (d.mul x[i] (A[(k, i)]'⟨by lia, h⟩)) := by
  rw [getElem_tbmv _ _ _ _ _ h, tbmvProd, tbmvUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt (by lia) h)]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)),
    getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
  rfl

/--
Element `i` of `tbmv .lower d A x` is `x[i] * A[0, i]`, or `x[i]` for a unit diagonal, plus the
terms `x[i - 1 - t] * A[1 + t, i - 1 - t]` for `t < min i k`.
-/
public theorem getElem_tbmv_lower (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tbmv .lower d A x)[i] = Nat.fold (min i k) (fun t _ s =>
      s + x[i - 1 - t]'(by lia) * A[(1 + t, i - 1 - t)]'⟨by lia, by lia⟩)
      (d.mul x[i] (A[(0, i)]'⟨by lia, h⟩)) := by
  rw [getElem_tbmv _ _ _ _ _ h, tbmvProd, tbmvLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data (A.off + A.ld * i)
      (by have := A.index_lt (i := 0) (by lia) h; simpa using this)]
  congr 1
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)),
    getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
  rfl

/-- The product `Aᵀ * x` for the band of the triangle `uplo` of `A`, element by element. -/
@[expose] public def tbmvTProd (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => tbmvTUpper d k A x
  | .lower => tbmvTLower d k A x

/-- The array of `tbmvT`. -/
@[expose] public def tbmvTData (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n)
    (x : Vec n) : Float64Array :=
  match uplo with
  | .upper => tbmvTUpperData d k A x
  | .lower => tbmvTLowerData d k A x

public theorem tbmvTData_eq (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbmvTData uplo d k A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvTProd uplo d k A x i := by
  cases uplo
  · exact tbmvTUpperData_eq d k A x
  · exact tbmvTLowerData_eq d k A x

/--
`tbmvT uplo d A x` is `Aᵀ * x` for the triangular band matrix with `k` off-diagonals stored by its
triangle `uplo` in `A : Mat (k + 1) n`, with a unit diagonal if `d` is `.unit`, by the loops of the
reference BLAS (`dtbmv` with `TRANS = 'T'`). For the upper triangle, it sets element `j` to its
diagonal term plus the dot product of the band of column `j` above the diagonal, from the diagonal
up, and of `x`, for `j = n - 1` down to `0`; for the lower triangle, it does the same for
`j = 0, …, n - 1`, with the band below the diagonal, from the diagonal down. It updates `x` in place
when its array is not shared, leaves the elements of the array outside `x` unchanged, and reads only
the band, and not its diagonal when `d` is `.unit`.
-/
@[expose] public def tbmvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    Vec n where
  data := tbmvTData uplo d k A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tbmvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `tbmvT uplo d A x` is the array of `x` with its elements multiplied. -/
public theorem data_tbmvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    (tbmvT uplo d A x).data =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tbmvTProd uplo d k A x i :=
  tbmvTData_eq uplo d k A x

@[simp] public theorem off_tbmvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbmvT uplo d A x).off = x.off := rfl

@[simp] public theorem inc_tbmvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbmvT uplo d A x).inc = x.inc := rfl

/-- Element `j` of `tbmvT uplo d A x` is element `j` of the model. -/
public theorem getElem_tbmvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (h : j < n) : (tbmvT uplo d A x)[j] = tbmvTProd uplo d k A x j :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tbmvT uplo d A x) rfl rfl j h

/--
Element `j` of `tbmvT .upper d A x` is `x[j] * A[k, j]`, or `x[j]` for a unit diagonal, plus the
terms `A[k - 1 - t, j] * x[j - 1 - t]` for `t < min j k`.
-/
public theorem getElem_tbmvT_upper (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tbmvT .upper d A x)[j] = Nat.fold (min j k) (fun t _ s =>
      s + A[(k - 1 - t, j)]'⟨by lia, h⟩ * x[j - 1 - t]'(by lia))
      (d.mul x[j] (A[(k, j)]'⟨by lia, h⟩)) := by
  rw [getElem_tbmvT _ _ _ _ _ h, tbmvTProd, tbmvTUpper, tbmvTUpperH,
    getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt (by lia) h)]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
Element `j` of `tbmvT .lower d A x` is `x[j] * A[0, j]`, or `x[j]` for a unit diagonal, plus the
terms `A[1 + t, j] * x[j + 1 + t]` for `t < min (n - 1 - j) k`.
-/
public theorem getElem_tbmvT_lower (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tbmvT .lower d A x)[j] = Nat.fold (min (n - 1 - j) k) (fun t _ s =>
      s + A[(1 + t, j)]'⟨by lia, h⟩ * x[j + 1 + t]'(by lia))
      (d.mul x[j] (A[(0, j)]'⟨by lia, h⟩)) := by
  rw [getElem_tbmvT _ _ _ _ _ h, tbmvTProd, tbmvTLower, tbmvTLowerH,
    getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data (A.off + A.ld * j)
      (by have := A.index_lt (i := 0) (by lia) h; simpa using this)]
  congr 1
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

end Mat

end BLAS.Float64
