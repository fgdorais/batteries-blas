/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float32.Tbmv
public import BatteriesBLAS.Float32.Trsv
import all BatteriesBLAS.Internal

/-!
# Triangular band solve

`Mat.tbsv uplo d A x` solves `A * y = x` and `Mat.tbsvT uplo d A x` solves `Aᵀ * y = x`, over `x`,
for the triangular band matrix with `k` off-diagonals stored in `A : Mat (k + 1) n` as for
`Mat.tbmv`, by the loops of the reference BLAS (`dtbsv`), as `Mat.trsv` and `Mat.trsvT` do for a
full triangle. As there, the reference BLAS doesn't test for singularity: a zero on the diagonal
gives infinities or NaNs. The reference BLAS master doesn't skip the columns with a zero element of
the solution either, so neither do these.

The specification of each element of the solution is recursive, in the solution: the element `i` is
`x[i]`, minus the terms of the other elements of its row (its column for `tbsvT`) in the band, times
the elements of the solution that they multiply, in the order of the loops, divided by the diagonal
unless it is unit.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n : Nat}

/-! ## The loops -/

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged.
-/
private theorem iterRange_fst (g : Nat → Float32Array → Float32 → Float32) (k : Nat) (t : Float32)
    (a : Float32Array) :
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

/-! ## The models -/

/--
Element `i` of the solution of `A * y = x` for the upper band of `A`, on the arrays: `x[i]`, minus
the terms `y[j] * A[k + i - j, j]` for `j = i + min (n - 1 - i) k` down to `i + 1`, divided by
`A[k, i]` unless the diagonal is unit.
-/
public def tbsvUpper (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (i : Nat) : Float32 :=
  d.apply (Nat.fold (min (n - 1 - i) k) (fun t _ht s =>
      s - tbsvUpper d k A x (i + min (n - 1 - i) k - t) *
        A.data[A.off + A.ld * (i + min (n - 1 - i) k - t) + (k - min (n - 1 - i) k + t)]!)
    x.data[x.off + x.inc * i]!) A.data[A.off + A.ld * i + k]!
termination_by n - i
decreasing_by lia

/--
Element `i` of the solution of `A * y = x` for the lower band of `A`, on the arrays: `x[i]`, minus
the terms `y[j] * A[i - j, j]` for `j = i - min i k, …, i - 1`, divided by `A[0, i]` unless the
diagonal is unit.
-/
public def tbsvLower (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (i : Nat) : Float32 :=
  d.apply (Nat.fold (min i k) (fun t _ht s =>
      s - tbsvLower d k A x (i - min i k + t) *
        A.data[A.off + A.ld * (i - min i k + t) + (min i k - t)]!)
    x.data[x.off + x.inc * i]!) A.data[A.off + A.ld * i]!
termination_by i
decreasing_by lia

/--
Element `j` of the solution of `Aᵀ * y = x` for the upper band of `A`, on the arrays: `x[j]`, minus
the terms `A[k + i - j, j] * y[i]` for `i = j - min j k, …, j - 1`, divided by `A[k, j]` unless the
diagonal is unit.
-/
public def tbsvTUpper (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat) : Float32 :=
  d.apply (Nat.fold (min j k) (fun t _ht s =>
      s - A.data[A.off + A.ld * j + (k - min j k + t)]! * tbsvTUpper d k A x (j - min j k + t))
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + k]!
termination_by j
decreasing_by lia

/--
Element `j` of the solution of `Aᵀ * y = x` for the lower band of `A`, on the arrays: `x[j]`, minus
the terms `A[i - j, j] * y[i]` for `i = j + min (n - 1 - j) k` down to `j + 1`, divided by `A[0, j]`
unless the diagonal is unit.
-/
public def tbsvTLower (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat) : Float32 :=
  d.apply (Nat.fold (min (n - 1 - j) k) (fun t _ht s =>
      s - A.data[A.off + A.ld * j + (min (n - 1 - j) k - t)]! *
        tbsvTLower d k A x (j + min (n - 1 - j) k - t))
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j]!
termination_by n - j
decreasing_by lia

/-! ## The upper triangle -/

/--
The map of step `j` of the upper solve on element `i`, when `x[j]` is `t` as the step starts:
divide element `j` by the diagonal, and subtract the quotient times column `j` of the band from the
elements above it.
-/
@[expose] public def tbsvUpperG (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (t : Float32)
    (i : Nat) (v : Float32) : Float32 :=
  if i = j then d.apply v A.data[A.off + A.ld * j + k]!
  else if j - min j k ≤ i ∧ i < j - min j k + min j k then
    v - d.apply t A.data[A.off + A.ld * j + k]! * A.data[A.off + A.ld * j + (k + i - j)]!
  else v

/-- The step `kk` of the upper solve, for the column `n - 1 - kk`. -/
@[expose] public def tbsvUpperStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (kk : Nat) (c : Float32Array) : Float32Array :=
  c.modifyAt x.stride.idx 0 n (tbsvUpperG d k A (n - 1 - kk) c[x.stride.idx (n - 1 - kk)]!)

/-- The array of the upper solve. -/
public def tbsvUpperData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float32Array :=
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
        let s := d.apply a[o + c * (nu - 1 - kk)]
          (A.uget ao al rfl rfl hs.1 ku (nu - 1 - kk) (by lia) hjn)
        a[o + c * (nu - 1 - kk)] := s
        let lo := nu - 1 - kk - bandAbove k (nu - 1 - kk)
        let r0 := ku - bandAbove k (nu - 1 - kk)
        for l in 0...bandAbove k (nu - 1 - kk) do
          have hl := toNat_sub_bandAbove_add (by assumption)
          have hr := toNat_sub_bandAbove_add' hku (by assumption)
          have hi : (lo + l).toNat < n := hl.1 ▸ Nat.lt_trans hl.2 hjn
          have hq' : (o + c * (lo + l)).toNat < a.size := x.toNat_index_lt hs.2 hi
          a[o + c * (lo + l)] := a[o + c * (lo + l)] -
            s * A.uget ao al rfl rfl hs.1 (r0 + l) (nu - 1 - kk) (by rw [hr.1]; lia) hjn
  else iterRange (tbsvUpperStep d k A x) 0 n x.data

public theorem tbsvUpperData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvUpperData d k A x = iterRange (tbsvUpperStep d k A x) 0 n x.data := by
  unfold tbsvUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbsvUpperStep d k A x)
      (hF := fun _ _ => by unfold tbsvUpperStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hku : k.toUSize.toNat = k :=
        toNat_toUSize_of_lt (by have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
      have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
          x.off + x.inc * (n - 1 - kk.toNat) := by
        rw [x.toNat_index hs.2 hjn, hj]
      have hab := toNat_bandAbove k (n.toUSize - 1 - kk)
      simp only [Tail.run_readThen, Tail.run_writeThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize *
          (n.toUSize - 1 - kk - bandAbove k (n.toUSize - 1 - kk) + l))
        (idx := fun l => x.off + x.inc * (n - 1 - kk.toNat - min (n - 1 - kk.toNat) k + l))
        (he := fun l _ hl => by rw [above_index x hs.2 hjn hl, hj])
        (G := fun l v => v - d.apply a[x.off + x.inc * (n - 1 - kk.toNat)]!
          A.data[A.off + A.ld * (n - 1 - kk.toNat) + k]! *
          A.data[A.off + A.ld * (n - 1 - kk.toNat) + (k - min (n - 1 - kk.toNat) k + l)]!)]
      · congr 1
        simp only [USize.toNat_zero, hab, hj, uget_eq_getElem, getElem_def, hp, hku]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [modifyAt_band_set! x a h (n - 1 - kk.toNat - min (n - 1 - kk.toNat) k)
          (min (n - 1 - kk.toNat) k) (n - 1 - kk.toNat) (by lia) (by lia) (by lia) _
          (fun v => d.apply v A.data[A.off + A.ld * (n - 1 - kk.toNat) + k]!), tbsvUpperStep]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [tbsvUpperG, Vec.idx_stride]
        by_cases h₁ : i = n - 1 - kk.toNat
        · simp only [h₁, ↓reduceIte]
        · simp only [h₁, ↓reduceIte]
          split
          · rw [show k - min (n - 1 - kk.toNat) k + (i - (n - 1 - kk.toNat -
                min (n - 1 - kk.toNat) k)) = k + i - (n - 1 - kk.toNat) by lia]
          · rfl
      · intro l _ hl v
        have hr := toNat_sub_bandAbove_add' hku hl
        simp only [uget_eq_getElem, getElem_def, hp, hr.1, hj, hku, getElem_eq_getElem!]
  · rfl

/-- The array of the upper solve is the array of `x` with its elements solved. -/
public theorem tbsvUpperData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvUpperData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvUpper d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbsvUpperData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) n (fun kk hkk => by lia)
    (fun kk => tbsvUpperG d k A (n - 1 - kk))).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  -- the values that the steps read are the elements of the solution
  have hsol : ∀ m j, n - 1 - j < m → j < n →
      d.apply (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
        (fun kk => tbsvUpperG d k A (n - 1 - kk)) (n - 1 - j)) A.data[A.off + A.ld * j + k]! =
        tbsvUpper d k A x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [selfRead, show n - 1 - (n - 1 - j) = j by lia]
      rw [show (fun kk (_ : kk < n - 1 - j) v => tbsvUpperG d k A (n - 1 - kk)
            (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
              (fun kk => tbsvUpperG d k A (n - 1 - kk)) kk) j v) =
          fun kk _ v => if j = n - 1 - kk then d.apply v A.data[A.off + A.ld * (n - 1 - kk) + k]!
            else if n - 1 - kk - min (n - 1 - kk) k ≤ j ∧
                j < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k then
              (fun c s => s - tbsvUpper d k A x c * A.data[A.off + A.ld * c + (k + j - c)]!)
                (n - 1 - kk) v
            else v from by
        funext kk hkk v
        simp only [tbsvUpperG]
        rw [← ih (n - 1 - kk) (by lia) (by lia), show n - 1 - (n - 1 - kk) = kk by lia]]
      rw [fold_upper_band_rev_pre hj k (fun c s => d.apply s A.data[A.off + A.ld * c + k]!)
        (fun c s => s - tbsvUpper d k A x c * A.data[A.off + A.ld * c + (k + j - c)]!),
        tbsvUpper]
      congr 1
      congr 1
      funext t ht s
      rw [show k + j - (j + min (n - 1 - j) k - t) = k - min (n - 1 - j) k + t by lia]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [show (fun kk (hkk : kk < n) v => tbsvUpperG d k A (n - 1 - kk)
        (selfRead x.data x.stride.idx (fun kk => n - 1 - kk)
          (fun kk => tbsvUpperG d k A (n - 1 - kk)) kk) i v) =
      fun kk _ v => if i = n - 1 - kk then d.apply v A.data[A.off + A.ld * (n - 1 - kk) + k]!
        else if n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
            i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k then
          (fun c s => s - tbsvUpper d k A x c * A.data[A.off + A.ld * c + (k + i - c)]!)
            (n - 1 - kk) v
        else v from by
    funext kk hkk v
    simp only [tbsvUpperG]
    rw [← hsol _ (n - 1 - kk) (Nat.lt_succ_self _) (by lia), show n - 1 - (n - 1 - kk) = kk by lia]]
  rw [fold_upper_band_rev hi k (fun c s => d.apply s A.data[A.off + A.ld * c + k]!)
    (fun c s => s - tbsvUpper d k A x c * A.data[A.off + A.ld * c + (k + i - c)]!), tbsvUpper]
  congr 1
  congr 1
  funext t ht s
  rw [show k + i - (i + min (n - 1 - i) k - t) = k - min (n - 1 - i) k + t by lia]

/-! ## The lower triangle -/

/--
The map of step `j` of the lower solve on element `i`, when `x[j]` is `t` as the step starts:
divide element `j` by the diagonal, and subtract the quotient times column `j` of the band from the
elements below it.
-/
@[expose] public def tbsvLowerG (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat) (t : Float32)
    (i : Nat) (v : Float32) : Float32 :=
  if i = j then d.apply v A.data[A.off + A.ld * j]!
  else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then
    v - d.apply t A.data[A.off + A.ld * j]! * A.data[A.off + A.ld * j + (i - j)]!
  else v

/-- The step `j` of the lower solve. -/
@[expose] public def tbsvLowerStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (c : Float32Array) : Float32Array :=
  c.modifyAt x.stride.idx 0 n (tbsvLowerG d k A j c[x.stride.idx j]!)

/-- The array of the lower solve. -/
public def tbsvLowerData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float32Array :=
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
        let s := d.apply a[o + c * j] (A.uget ao al rfl rfl hs.1 0 j (by simp) hjn)
        a[o + c * j] := s
        for l in 0...bandBelow n k j do
          have hl := toNat_bandBelow_add hn hjn (by assumption)
          have hr := toNat_one_add_bandBelow (k := k) hn (by assumption)
          have hi : (j + 1 + l).toNat < n := hl.1 ▸ hl.2
          have hq' : (o + c * (j + 1 + l)).toNat < a.size := x.toNat_index_lt hs.2 hi
          a[o + c * (j + 1 + l)] := a[o + c * (j + 1 + l)] -
            s * A.uget ao al rfl rfl hs.1 (1 + l) j (hr.1 ▸ hr.2) hjn
  else iterRange (tbsvLowerStep d k A x) 0 n x.data

public theorem tbsvLowerData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvLowerData d k A x = iterRange (tbsvLowerStep d k A x) 0 n x.data := by
  unfold tbsvLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbsvLowerStep d k A x)
      (hF := fun _ _ => by unfold tbsvLowerStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hp := x.toNat_index hs.2 hj
      have hbe := toNat_bandBelow hn k j
      simp only [Tail.run_readThen, Tail.run_writeThen]
      rw [Tail.run_forInFrom_modify
        (e := fun l => x.off.toUSize + x.inc.toUSize * (j + 1 + l))
        (idx := fun l => x.off + x.inc * (j.toNat + 1 + l))
        (he := fun l _ hl => below_index (k := k) x hs.2 hj hl)
        (G := fun l v => v - d.apply a[x.off + x.inc * j.toNat]! A.data[A.off + A.ld * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + (1 + l)]!)]
      · congr 1
        simp only [USize.toNat_zero, hbe, uget_eq_getElem, getElem_def, hp, Nat.add_zero]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [modifyAt_band_set! x a h (j.toNat + 1) (min (n - 1 - j.toNat) k) j.toNat (by lia) hj
          (by lia) _ (fun v => d.apply v A.data[A.off + A.ld * j.toNat]!), tbsvLowerStep]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [tbsvLowerG, Vec.idx_stride]
        by_cases h₁ : i = j.toNat
        · simp only [h₁, ↓reduceIte]
        · simp only [h₁, ↓reduceIte]
          split
          · rw [show 1 + (i - (j.toNat + 1)) = i - j.toNat by lia]
          · rfl
      · intro l _ hl v
        have hr := toNat_one_add_bandBelow (k := k) hn hl
        simp only [uget_eq_getElem, getElem_def, hp, hr.1, USize.toNat_zero, Nat.add_zero,
          getElem_eq_getElem!]
  · rfl

/-- The array of the lower solve is the array of `x` with its elements solved. -/
public theorem tbsvLowerData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvLowerData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvLower d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbsvLowerData_eq_iterRange]
  refine (iterRange_modifyAt_self x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) n (fun j hj => hj) (tbsvLowerG d k A)).trans ?_
  rw [modifyAt_eq_read _ _ hinj (fun i _ hi => x.index_lt hi)]
  -- the values that the steps read are the elements of the solution
  have hsol : ∀ m j, j < m → j < n →
      d.apply (selfRead x.data x.stride.idx (fun j => j) (tbsvLowerG d k A) j)
        A.data[A.off + A.ld * j]! = tbsvLower d k A x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [selfRead]
      rw [show (fun j' (_ : j' < j) v => tbsvLowerG d k A j'
            (selfRead x.data x.stride.idx (fun j => j) (tbsvLowerG d k A) j') j v) =
          fun j' _ v => if j = j' then d.apply v A.data[A.off + A.ld * j']!
            else if j' + 1 ≤ j ∧ j < j' + 1 + min (n - 1 - j') k then
              (fun c s => s - tbsvLower d k A x c * A.data[A.off + A.ld * c + (j - c)]!) j' v
            else v from by
        funext j' hj' v
        simp only [tbsvLowerG]
        rw [← ih j' (by lia) (by lia)]]
      rw [fold_lower_band_pre hj k (fun c s => d.apply s A.data[A.off + A.ld * c]!)
        (fun c s => s - tbsvLower d k A x c * A.data[A.off + A.ld * c + (j - c)]!), tbsvLower]
      congr 1
      congr 1
      funext t ht s
      rw [show j - (j - min j k + t) = min j k - t by lia]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [show (fun j (hj : j < n) v => tbsvLowerG d k A j
        (selfRead x.data x.stride.idx (fun j => j) (tbsvLowerG d k A) j) i v) =
      fun j _ v => if i = j then d.apply v A.data[A.off + A.ld * j]!
        else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then
          (fun c s => s - tbsvLower d k A x c * A.data[A.off + A.ld * c + (i - c)]!) j v
        else v from by
    funext j hj v
    simp only [tbsvLowerG]
    rw [← hsol _ j (Nat.lt_succ_self _) hj]]
  rw [fold_lower_band hi k (fun c s => d.apply s A.data[A.off + A.ld * c]!)
    (fun c s => s - tbsvLower d k A x c * A.data[A.off + A.ld * c + (i - c)]!), tbsvLower]
  congr 1
  congr 1
  funext t ht s
  rw [show i - (i - min i k + t) = min i k - t by lia]

/-! ## The transposed upper triangle -/

/--
The value that the step for column `j` of the transposed upper solve writes at element `j`, from
the elements `get q` of `x`: `get j`, minus the terms `A[k + i - j, j] * get i` for
`i = j - min j k, …, j - 1`, divided by `A[k, j]` unless the diagonal is unit.
-/
@[expose] public def tbsvTUpperH (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat)
    (get : Nat → Float32) : Float32 :=
  d.apply (Nat.fold (min j k) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (k - min j k + t)]! * get (j - min j k + t)) (get j))
    A.data[A.off + A.ld * j + k]!

/-- The step `j` of the transposed upper solve. -/
@[expose] public def tbsvTUpperStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (c : Float32Array) : Float32Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = j then tbsvTUpperH d k A j (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed upper solve. -/
public def tbsvTUpperData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float32Array :=
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
        let v := a[o + c * j]
        let lo := j - bandAbove k j
        let r0 := ku - bandAbove k j
        for l in 0...bandAbove k j with (s := v) do
          have hl := toNat_sub_bandAbove_add (by assumption)
          have hr := toNat_sub_bandAbove_add' hku (by assumption)
          have hi : (lo + l).toNat < n := hl.1 ▸ Nat.lt_trans hl.2 hjn
          have hq' : (o + c * (lo + l)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s -
            A.uget ao al rfl rfl hs.1 (r0 + l) j (by rw [hr.1]; lia) hjn * a[o + c * (lo + l)]
        a[o + c * j] := d.apply s (A.uget ao al rfl rfl hs.1 ku j (by lia) hjn)
  else iterRange (tbsvTUpperStep d k A x) 0 n x.data

public theorem tbsvTUpperData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvTUpperData d k A x = iterRange (tbsvTUpperStep d k A x) 0 n x.data := by
  unfold tbsvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbsvTUpperStep d k A x)
      (hF := fun _ _ => by unfold tbsvTUpperStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hku : k.toUSize.toNat = k :=
        toNat_toUSize_of_lt (by have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
      have hp := x.toNat_index hs.2 hj
      have hab := toNat_bandAbove k j
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun l p =>
          (p.1 - A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]! *
            p.2[x.off + x.inc * (j.toNat - min j.toNat k + l)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hab, iterRange_fst (fun l a s =>
          s - A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]! *
            a[x.off + x.inc * (j.toNat - min j.toNat k + l)]!)]
        congr 1
        simp only [hp, uget_eq_getElem, getElem_def, hku]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h hj, tbsvTUpperStep]
        rfl
      · intro l _ hl next' b a' h'
        rw [hab] at hl
        have hl' := toNat_sub_bandAbove_add (k := k) (j := j) (l := l) (by rw [hab]; exact hl)
        have hr := toNat_sub_bandAbove_add' (k := k) (j := j) (l := l) hku (by rw [hab]; exact hl)
        have hp' := above_index x hs.2 hj (k := k) (l := l) (by rw [hab]; exact hl)
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def, hp', hr.1,
          getElem_eq_getElem!]
  · rfl

/-- The array of the transposed upper solve is the array of `x` with its elements solved. -/
public theorem tbsvTUpperData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvTUpperData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvTUpper d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbsvTUpperData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun j => j) (fun q => q) (fun j _ => rfl) (fun q _ => rfl)
    (fun j => tbsvTUpperH d k A j) (fun j hj get get' hget => by
      simp only [tbsvTUpperH]
      rw [hget _ hj]
      congr 2
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  have hsol : ∀ m j, j < m → j < n →
      writeRead x.data x.stride.idx (fun q => q) (fun j => tbsvTUpperH d k A j) j =
        tbsvTUpper d k A x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [writeRead, tbsvTUpper, tbsvTUpperH, dite_eq_right (Nat.lt_irrefl j)]
      congr 2
      funext t ht s
      rw [dite_eq_left (show j - min j k + t < j by lia), ih _ (by lia) (by lia)]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi), hsol _ i (Nat.lt_succ_self _) hi]

/-! ## The transposed lower triangle -/

/--
The value that the step for column `j` of the transposed lower solve writes at element `j`, from
the elements `get q` of `x`: `get j`, minus the terms `A[i - j, j] * get i` for
`i = j + min (n - 1 - j) k` down to `j + 1`, divided by `A[0, j]` unless the diagonal is unit.
-/
@[expose] public def tbsvTLowerH (d : Diag) (k : Nat) (A : Mat (k + 1) n) (j : Nat)
    (get : Nat → Float32) : Float32 :=
  d.apply (Nat.fold (min (n - 1 - j) k) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (min (n - 1 - j) k - t)]! * get (j + min (n - 1 - j) k - t))
    (get j)) A.data[A.off + A.ld * j]!

/-- The step `kk` of the transposed lower solve, for the column `n - 1 - kk`. -/
@[expose] public def tbsvTLowerStep (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n)
    (kk : Nat) (c : Float32Array) : Float32Array :=
  c.modifyAt x.stride.idx 0 n fun i v =>
    if i = n - 1 - kk then tbsvTLowerH d k A (n - 1 - kk) (fun q => c[x.stride.idx q]!) else v

/-- The array of the transposed lower solve. -/
public def tbsvTLowerData (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) : Float32Array :=
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
        let v := a[o + c * (nu - 1 - kk)]
        let cnt := bandBelow n k (nu - 1 - kk)
        for t in 0...cnt with (s := v) do
          have hi := toNat_add_bandBelow_sub hn hjn (by assumption)
          have hr := toNat_bandBelow_sub (k := k) hn (by assumption)
          have hq' : (o + c * (nu - 1 - kk + cnt - t)).toNat < a.size :=
            x.toNat_index_lt hs.2 (hi.1 ▸ hi.2)
          s := s - A.uget ao al rfl rfl hs.1 (cnt - t) (nu - 1 - kk) (hr.1 ▸ hr.2) hjn *
            a[o + c * (nu - 1 - kk + cnt - t)]
        a[o + c * (nu - 1 - kk)] :=
          d.apply s (A.uget ao al rfl rfl hs.1 0 (nu - 1 - kk) (by simp) hjn)
  else iterRange (tbsvTLowerStep d k A x) 0 n x.data

public theorem tbsvTLowerData_eq_iterRange (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvTLowerData d k A x = iterRange (tbsvTLowerStep d k A x) 0 n x.data := by
  unfold tbsvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := tbsvTLowerStep d k A x)
      (hF := fun _ _ => by unfold tbsvTLowerStep; exact size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro kk _ hkk next a h
      rw [hnu] at hkk
      have hj : (n.toUSize - 1 - kk).toNat = n - 1 - kk.toNat := by grind
      have hjn : (n.toUSize - 1 - kk).toNat < n := by lia
      have hbe := toNat_bandBelow hn k (n.toUSize - 1 - kk)
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 - A.data[A.off + A.ld * (n - 1 - kk.toNat) +
              (min (n - 1 - (n - 1 - kk.toNat)) k - t)]! *
            p.2[x.off + x.inc * (n - 1 - kk.toNat + min (n - 1 - (n - 1 - kk.toNat)) k - t)]!,
            p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hbe, hj, iterRange_fst (fun t a s =>
          s - A.data[A.off + A.ld * (n - 1 - kk.toNat) +
              (min (n - 1 - (n - 1 - kk.toNat)) k - t)]! *
            a[x.off + x.inc * (n - 1 - kk.toNat + min (n - 1 - (n - 1 - kk.toNat)) k - t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - kk)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat) := by
          rw [x.toNat_index hs.2 hjn, hj]
        simp only [hp, uget_eq_getElem, getElem_def, hj, USize.toNat_zero, Nat.add_zero]
        rw [set_eq_set!]
        simp only [getElem_eq_getElem!]
        rw [set!_eq_modifyAt_ite x a h (by lia), tbsvTLowerStep]
        rfl
      · intro t _ ht next' b a' h'
        rw [hbe] at ht
        have hi := toNat_add_bandBelow_sub (k := k) hn hjn (t := t) (by rw [hbe]; exact ht)
        have hr := toNat_bandBelow_sub (k := k) hn (j := n.toUSize - 1 - kk) (t := t)
          (by rw [hbe]; exact ht)
        have hp : (x.off.toUSize + x.inc.toUSize *
              (n.toUSize - 1 - kk + bandBelow n k (n.toUSize - 1 - kk) - t)).toNat =
            x.off + x.inc * (n - 1 - kk.toNat + min (n - 1 - (n - 1 - kk.toNat)) k - t.toNat) := by
          rw [x.toNat_index hs.2 (hi.1 ▸ hi.2), hi.1, hj]
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def, hp, hr.1, hj,
          getElem_eq_getElem!]
  · rfl

/-- The array of the transposed lower solve is the array of `x` with its elements solved. -/
public theorem tbsvTLowerData_eq (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvTLowerData d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvTLower d k A x i := by
  have hinj := x.fits.injOn (lo := 0) (Nat.le_refl _)
  rw [tbsvTLowerData_eq_iterRange]
  refine (iterRange_write x.data x.stride.idx hinj (fun i hi => x.index_lt hi)
    (fun kk => n - 1 - kk) (fun q => n - 1 - q) (fun kk hkk => by lia) (fun q hq => by lia)
    (fun kk => tbsvTLowerH d k A (n - 1 - kk)) (fun kk hkk get get' hget => by
      simp only [tbsvTLowerH]
      rw [hget _ (by lia)]
      congr 2
      funext t ht s
      rw [hget _ (by lia)]) (Nat.le_refl n)).trans ?_
  have hsol : ∀ m j, n - 1 - j < m → j < n →
      writeRead x.data x.stride.idx (fun q => n - 1 - q) (fun kk => tbsvTLowerH d k A (n - 1 - kk))
        (n - 1 - j) = tbsvTLower d k A x j := by
    intro m
    induction m with
    | zero => intro j h; lia
    | succ m ih =>
      intro j hm hj
      rw [writeRead, show n - 1 - (n - 1 - j) = j by lia, tbsvTLower, tbsvTLowerH,
        dite_eq_right (Nat.lt_irrefl (n - 1 - j))]
      congr 2
      funext t ht s
      rw [dite_eq_left (show n - 1 - (j + min (n - 1 - j) k - t) < n - 1 - j by lia),
        ih _ (by lia) (by lia)]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)), hsol _ i (Nat.lt_succ_self _) hi]

/-! ## `tbsv` and `tbsvT` -/

/-- The solution of `A * y = x` for the band of the triangle `uplo` of `A`, element by element. -/
@[expose] public def tbsvSol (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    Nat → Float32 :=
  match uplo with
  | .upper => tbsvUpper d k A x
  | .lower => tbsvLower d k A x

/-- The array of `tbsv`. -/
@[expose] public def tbsvData (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    Float32Array :=
  match uplo with
  | .upper => tbsvUpperData d k A x
  | .lower => tbsvLowerData d k A x

public theorem tbsvData_eq (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvData uplo d k A x = x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvSol uplo d k A x i := by
  cases uplo
  · exact tbsvUpperData_eq d k A x
  · exact tbsvLowerData_eq d k A x

/--
`tbsv uplo d A x` is the solution `y` of `A * y = x` for the triangular band matrix with `k`
off-diagonals stored by its triangle `uplo` in `A : Mat (k + 1) n`, with a unit diagonal if `d` is
`.unit`, by the column-oriented loops of the reference BLAS (`dtbsv` with `TRANS = 'N'`). For the
upper triangle, it divides element `j` by the diagonal and subtracts the quotient times column `j`
of the band from the elements above `j`, for `j = n - 1` down to `0`; for the lower triangle, it
does the same for `j = 0, …, n - 1`, with the elements below. It updates `x` in place when its array
is not shared, leaves the elements of the array outside `x` unchanged, and reads only the band, and
not its diagonal when `d` is `.unit`.
-/
@[expose] public def tbsv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    Vec n where
  data := tbsvData uplo d k A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tbsvData_eq, size_modifyAt]; exact x.bound

/-- The array of `tbsv uplo d A x` is the array of `x` with its elements solved. -/
public theorem data_tbsv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    (tbsv uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvSol uplo d k A x i :=
  tbsvData_eq uplo d k A x

@[simp] public theorem off_tbsv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbsv uplo d A x).off = x.off := rfl

@[simp] public theorem inc_tbsv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbsv uplo d A x).inc = x.inc := rfl

/-- Element `i` of `tbsv uplo d A x` is element `i` of the model. -/
public theorem getElem_tbsv (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (i : Nat) (h : i < n) : (tbsv uplo d A x)[i] = tbsvSol uplo d k A x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tbsv uplo d A x) rfl rfl i h

/--
Element `i` of `y = tbsv .upper d A x` is `x[i]`, minus the terms `y[j] * A[k + i - j, j]` for
`j = i + min (n - 1 - i) k` down to `i + 1`, divided by `A[k, i]` unless the diagonal is unit: back
substitution, in the order of the loops.
-/
public theorem getElem_tbsv_upper (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tbsv .upper d A x)[i] = d.apply (Nat.fold (min (n - 1 - i) k) (fun t _ s =>
      s - (tbsv .upper d A x)[i + min (n - 1 - i) k - t]'(by lia) *
        A[(k - min (n - 1 - i) k + t, i + min (n - 1 - i) k - t)]'⟨by lia, by lia⟩) x[i])
      (A[(k, i)]'⟨by lia, h⟩) := by
  rw [getElem_tbsv _ _ _ _ _ h, tbsvSol, tbsvUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt (by lia) h)]
  congr 2
  funext t ht s
  rw [getElem_tbsv _ _ _ _ _ (by lia), tbsvSol,
    getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
  rfl

/--
Element `i` of `y = tbsv .lower d A x` is `x[i]`, minus the terms `y[j] * A[i - j, j]` for
`j = i - min i k, …, i - 1`, divided by `A[0, i]` unless the diagonal is unit: forward
substitution, in the order of the loops.
-/
public theorem getElem_tbsv_lower (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (i : Nat)
    (h : i < n) :
    (tbsv .lower d A x)[i] = d.apply (Nat.fold (min i k) (fun t _ s =>
      s - (tbsv .lower d A x)[i - min i k + t]'(by lia) *
        A[(min i k - t, i - min i k + t)]'⟨by lia, by lia⟩) x[i])
      (A[(0, i)]'⟨by lia, h⟩) := by
  rw [getElem_tbsv _ _ _ _ _ h, tbsvSol, tbsvLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data (A.off + A.ld * i)
      (by have := A.index_lt (i := 0) (by lia) h; simpa using this)]
  congr 2
  funext t ht s
  rw [getElem_tbsv _ _ _ _ _ (by lia), tbsvSol,
    getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
  rfl

/-- The solution of `Aᵀ * y = x` for the band of the triangle `uplo` of `A`, element by element. -/
@[expose] public def tbsvTSol (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    Nat → Float32 :=
  match uplo with
  | .upper => tbsvTUpper d k A x
  | .lower => tbsvTLower d k A x

/-- The array of `tbsvT`. -/
@[expose] public def tbsvTData (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n)
    (x : Vec n) : Float32Array :=
  match uplo with
  | .upper => tbsvTUpperData d k A x
  | .lower => tbsvTLowerData d k A x

public theorem tbsvTData_eq (uplo : Uplo) (d : Diag) (k : Nat) (A : Mat (k + 1) n) (x : Vec n) :
    tbsvTData uplo d k A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvTSol uplo d k A x i := by
  cases uplo
  · exact tbsvTUpperData_eq d k A x
  · exact tbsvTLowerData_eq d k A x

/--
`tbsvT uplo d A x` is the solution `y` of `Aᵀ * y = x` for the triangular band matrix with `k`
off-diagonals stored by its triangle `uplo` in `A : Mat (k + 1) n`, with a unit diagonal if `d` is
`.unit`, by the loops of the reference BLAS (`dtbsv` with `TRANS = 'T'`). For the upper triangle,
it sets element `j` to `x[j]` minus the dot product of the band of column `j` above the diagonal,
from the top down, and of the solution, divided by the diagonal, for `j = 0, …, n - 1`; for the
lower triangle, it does the same for `j = n - 1` down to `0`, with the band below the diagonal, from
the bottom up. It updates `x` in place when its array is not shared, leaves the elements of the
array outside `x` unchanged, and reads only the band, and not its diagonal when `d` is `.unit`.
-/
@[expose] public def tbsvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    Vec n where
  data := tbsvTData uplo d k A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [tbsvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `tbsvT uplo d A x` is the array of `x` with its elements solved. -/
public theorem data_tbsvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) :
    (tbsvT uplo d A x).data =
      x.data.modifyAt x.stride.idx 0 n fun i _ => tbsvTSol uplo d k A x i :=
  tbsvTData_eq uplo d k A x

@[simp] public theorem off_tbsvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbsvT uplo d A x).off = x.off := rfl

@[simp] public theorem inc_tbsvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n)
    (x : Vec n) : (tbsvT uplo d A x).inc = x.inc := rfl

/-- Element `j` of `tbsvT uplo d A x` is element `j` of the model. -/
public theorem getElem_tbsvT (uplo : Uplo) (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n)
    (j : Nat) (h : j < n) : (tbsvT uplo d A x)[j] = tbsvTSol uplo d k A x j :=
  Vec.getElem_of_data_eq_modifyAt _ (data_tbsvT uplo d A x) rfl rfl j h

/--
Element `j` of `y = tbsvT .upper d A x` is `x[j]`, minus the terms `A[k + i - j, j] * y[i]` for
`i = j - min j k, …, j - 1`, divided by `A[k, j]` unless the diagonal is unit: forward
substitution, in the order of the loops.
-/
public theorem getElem_tbsvT_upper (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tbsvT .upper d A x)[j] = d.apply (Nat.fold (min j k) (fun t _ s =>
      s - A[(k - min j k + t, j)]'⟨by lia, h⟩ * (tbsvT .upper d A x)[j - min j k + t]'(by lia))
      x[j]) (A[(k, j)]'⟨by lia, h⟩) := by
  rw [getElem_tbsvT _ _ _ _ _ h, tbsvTSol, tbsvTUpper, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data _ (A.index_lt (by lia) h)]
  congr 2
  funext t ht s
  rw [getElem_tbsvT _ _ _ _ _ (by lia), tbsvTSol, getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
Element `j` of `y = tbsvT .lower d A x` is `x[j]`, minus the terms `A[i - j, j] * y[i]` for
`i = j + min (n - 1 - j) k` down to `j + 1`, divided by `A[0, j]` unless the diagonal is unit: back
substitution, in the order of the loops.
-/
public theorem getElem_tbsvT_lower (d : Diag) {k : Nat} (A : Mat (k + 1) n) (x : Vec n) (j : Nat)
    (h : j < n) :
    (tbsvT .lower d A x)[j] = d.apply (Nat.fold (min (n - 1 - j) k) (fun t _ s =>
      s - A[(min (n - 1 - j) k - t, j)]'⟨by lia, h⟩ *
        (tbsvT .lower d A x)[j + min (n - 1 - j) k - t]'(by lia)) x[j])
      (A[(0, j)]'⟨by lia, h⟩) := by
  rw [getElem_tbsvT _ _ _ _ _ h, tbsvTSol, tbsvTLower, getElem!_pos x.data _ (x.index_lt h),
    getElem!_pos A.data (A.off + A.ld * j)
      (by have := A.index_lt (i := 0) (by lia) h; simpa using this)]
  congr 2
  funext t ht s
  rw [getElem_tbsvT _ _ _ _ _ (by lia), tbsvTSol, getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

end Mat

end BLAS.Float32
