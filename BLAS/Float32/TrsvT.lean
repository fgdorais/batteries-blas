/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Trsv
import all BLAS.Internal

/-!
# Transposed triangular solve

`Mat.trsvT uplo diag A x` solves `Aᵀ * y = x` for a triangular matrix `A`, over `x`, by the loops
of the reference BLAS for `TRANS = 'T'`. These loops are dot products: element `j` is `x[j]`, minus
the terms `A[i, j] * y[i]` of the elements of column `j` that are already solved, divided by
`A[j, j]` unless the diagonal is unit. Its specification is the recursive model `trsvTUpper` or
`trsvTLower`, which subtracts the terms in the order the loops do.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n : Nat}

/-! ## The models -/

/--
Element `j` of the solution of `Aᵀ * y = x` for the upper triangle of `A`, on the arrays: `x[j]`,
minus the terms `A[i, j] * y[i]` for `i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal
is unit.
-/
public def trsvTUpper (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  d.apply (Nat.fold j (fun i _hi s => s - A.data[A.off + A.ld * j + i]! * trsvTUpper d A x i)
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
termination_by j
decreasing_by exact _hi

/--
Element `j` of the solution of `Aᵀ * y = x` for the lower triangle of `A`, on the arrays: `x[j]`,
minus the terms `A[i, j] * y[i]` for `i = n - 1, …, j + 1`, divided by `A[j, j]` unless the
diagonal is unit.
-/
public def trsvTLower (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (n - 1 - t)]! * trsvTLower d A x (n - 1 - t))
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/--
Element `j < n` of the solution of `Aᵀ * y = x` for the upper triangle of `A` is `x[j]`, minus the
terms `A[i, j] * y[i]` for `i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal is unit.
-/
public theorem trsvTUpper_eq (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (h : j < n) :
    trsvTUpper d A x j =
      d.apply (Nat.fold j (fun i hi s => s - A[(i, j)]'⟨by lia, h⟩ * trsvTUpper d A x i) x[j])
        A[(j, j)] := by
  rw [trsvTUpper, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext i hi s
  rw [getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
Element `j < n` of the solution of `Aᵀ * y = x` for the lower triangle of `A` is `x[j]`, minus the
terms `A[i, j] * y[i]` for `i = n - 1, …, j + 1`, divided by `A[j, j]` unless the diagonal is
unit.
-/
public theorem trsvTLower_eq (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (h : j < n) :
    trsvTLower d A x j =
      d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
          s - A[(n - 1 - t, j)]'⟨by lia, h⟩ * trsvTLower d A x (n - 1 - t)) x[j])
        A[(j, j)] := by
  rw [trsvTLower, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/-! ## The loops -/

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged and
maps the variable by a fold.
-/
theorem iterRange_fst (g : Nat → Float32Array → Float32 → Float32) (k : Nat) (t : Float32)
    (a : Float32Array) :
    iterRange (fun i p => (g i p.2 p.1, p.2)) 0 k (t, a) =
      (Nat.fold k (fun i _ s => g i a s) t, a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/-- The step `j` of the upper solve: solve for element `j` from the elements above it. -/
@[expose] public def trsvTUpperStep (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat)
    (b : Float32Array) : Float32Array :=
  let t := d.apply (Nat.fold j (fun i _ s =>
      s - A.data[A.off + A.ld * j + i]! * b[x.off + x.inc * i]!) b[x.off + x.inc * j]!)
    A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The array of the upper solve. -/
public def trsvTUpperData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for j in 0...nu do
        have hk : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        let v := a[o + c * j]
        for i in 0...j with (t := v) do
          have hi : (o + c * i).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
          t := t - A.uget ao al rfl rfl hs.1 i j (by lia) (by lia) * a[o + c * i]
        a[o + c * j] := d.apply t (A.uget ao al rfl rfl hs.1 j j (by lia) (by lia))).2
  else iterRange (trsvTUpperStep d A x) 0 n x.data

public theorem trsvTUpperData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTUpperData d A x = iterRange (trsvTUpperStep d A x) 0 n x.data := by
  unfold trsvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsvTUpperStep d A x)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj next a h
      rw [hnu] at hj
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun i p =>
          (p.1 - A.data[A.off + A.ld * j.toNat + i]! * p.2[x.off + x.inc * i]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun i a s =>
          s - A.data[A.off + A.ld * j.toNat + i]! * a[x.off + x.inc * i]!)]
        congr 1
        have hp := x.toNat_index hs.2 hj
        rw [trsvTUpperStep,
          ← set_eq_modifyAt _ _ _ _ (by rw [Vec.idx_stride, h]; exact x.index_lt hj)]
        simp only [hp, Vec.idx_stride, uget_eq_getElem, getElem_def,
          getElem!_pos a (x.off + x.inc * j.toNat) (show _ < a.size by rw [h]; exact x.index_lt hj),
          getElem!_pos A.data (A.off + A.ld * j.toNat + j.toNat) (A.index_lt hj hj)]
      · intro i _ hi next' b a' h'
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
        have hp := x.toNat_index hs.2 (Nat.lt_trans hi hj)
        simp only [hp, getElem!_pos a' (x.off + x.inc * i.toNat)
            (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * j.toNat + i.toNat) (A.index_lt (by lia) hj)]
  · rfl

/-- After the steps `i < j`, the elements `i < j` are solved, and the others are unchanged. -/
theorem iterRange_trsvTUpperStep (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (hj : j ≤ n) :
    iterRange (trsvTUpperStep d A x) 0 j x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v => if i < j then trsvTUpper d A x i else v := by
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, i ≤ j → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if i < j then trsvTUpper d A x i else v)[x.off + x.inc * i]! =
        if i < j then trsvTUpper d A x i else x.data[x.off + x.inc * i]! := by
      intro i hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt (by lia : i < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        getElem!_pos x.data _ (x.index_lt (by lia))]
    have ht : d.apply (Nat.fold j (fun i _ s => s - A.data[A.off + A.ld * j + i]! *
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if i < j then trsvTUpper d A x i else v)[x.off + x.inc * i]!)
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if i < j then trsvTUpper d A x i else v)[x.off + x.inc * j]!)
          A.data[A.off + A.ld * j + j]! = trsvTUpper d A x j := by
      rw [hr j (Nat.le_refl _), ite_eq_right (Nat.lt_irrefl j), trsvTUpper]
      congr 2
      funext i hi s
      rw [hr i (by lia), ite_eq_left hi]
    simp only [trsvTUpperStep, ht]
    rw [modifyAt_widen (lo := j) (hi := j + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _)
      (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < j
    · simp [h₁, show i < j + 1 by lia, show ¬j ≤ i by lia]
    · by_cases h₂ : i = j
      · subst h₂; simp
      · simp [h₁, show ¬i < j + 1 by lia]

/-- The array of the upper solve is the array of `x` with its elements solved. -/
public theorem trsvTUpperData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTUpperData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTUpper d A x i := by
  rw [trsvTUpperData_eq_iterRange, iterRange_trsvTUpperStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp [hi]

/-! ## The lower triangle -/

/--
The step `k` of the lower solve: solve for element `j = n - 1 - k` from the elements below it.
-/
@[expose] public def trsvTLowerStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float32Array) : Float32Array :=
  let j := n - 1 - k
  let t := d.apply (Nat.fold k (fun t _ s =>
      s - A.data[A.off + A.ld * j + (n - 1 - t)]! * b[x.off + x.inc * (n - 1 - t)]!)
      b[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The array of the lower solve. -/
public def trsvTLowerData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for k in 0...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        for t in 0...k with (s := v) do
          have hi : (nu - 1 - t).toNat < n := by grind
          have hk' : (o + c * (nu - 1 - t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s - A.uget ao al rfl rfl hs.1 (nu - 1 - t) (nu - 1 - k) hi hjn *
            a[o + c * (nu - 1 - t)]
        a[o + c * (nu - 1 - k)] :=
          d.apply s (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)).2
  else iterRange (trsvTLowerStep d A x) 0 n x.data

public theorem trsvTLowerData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerData d A x = iterRange (trsvTLowerStep d A x) 0 n x.data := by
  unfold trsvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsvTLowerStep d A x)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro k _ hk next a h
      rw [hnu] at hk
      have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - t)]! *
            p.2[x.off + x.inc * (n - 1 - t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun t a s =>
          s - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - t)]! *
            a[x.off + x.inc * (n - 1 - t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
            x.off + x.inc * (n - 1 - k.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hj]
        rw [trsvTLowerStep, ← set_eq_modifyAt _ _ _ _
          (by rw [Vec.idx_stride, h]; exact x.index_lt (by lia))]
        simp only [hp, hj, Vec.idx_stride, uget_eq_getElem, getElem_def,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
            (A.index_lt (by lia) (by lia))]
      · intro t _ ht next' b a' h'
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
        have hi : (n.toUSize - 1 - t).toNat = n - 1 - t.toNat := by grind
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - t)).toNat =
            x.off + x.inc * (n - 1 - t.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hi]
        simp only [hp, hi, hj, getElem!_pos a' (x.off + x.inc * (n - 1 - t.toNat))
            (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - t.toNat))
            (A.index_lt (by lia) (by lia))]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are solved, and the others are unchanged.
-/
theorem iterRange_trsvTLowerStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k ≤ n) :
    iterRange (trsvTLowerStep d A x) 0 k x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v =>
        if n - k ≤ i then trsvTLower d A x i else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, n - 1 - k ≤ i → i < n → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trsvTLower d A x i else v)[x.off + x.inc * i]! =
        if n - k ≤ i then trsvTLower d A x i else x.data[x.off + x.inc * i]! := by
      intro i _ hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt hi),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) hi,
        getElem!_pos x.data _ (x.index_lt hi)]
    have ht : d.apply (Nat.fold k (fun t _ s =>
          s - A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - t)]! *
            (x.data.modifyAt x.stride.idx 0 n fun i v =>
              if n - k ≤ i then trsvTLower d A x i else v)[x.off + x.inc * (n - 1 - t)]!)
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if n - k ≤ i then trsvTLower d A x i else v)[x.off + x.inc * (n - 1 - k)]!)
          A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]! = trsvTLower d A x (n - 1 - k) := by
      rw [hr (n - 1 - k) (Nat.le_refl _) (by lia), ite_eq_right (by lia),
        trsvTLower.eq_1 d A x (n - 1 - k), Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
      congr 2
      funext t ht s
      rw [hr (n - 1 - t) (by lia) (by lia), ite_eq_left (by lia)]
    simp only [trsvTLowerStep, ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _
      (Nat.zero_le _) (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/-- The array of the lower solve is the array of `x` with its elements solved. -/
public theorem trsvTLowerData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTLower d A x i := by
  rw [trsvTLowerData_eq_iterRange, iterRange_trsvTLowerStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-! ## The lower triangle, with the terms in increasing order -/

/-!
The reference `trsm` solves `Aᵀ * X = α * B` for a lower triangle with the loops of `trsv`, except
that it subtracts the terms of element `j` in increasing order, `i = j + 1, …, n - 1`, where `trsv`
subtracts them from `i = n - 1` down. `trsvTLowerAsc` is that solve, for the columns of `trsmT`.
-/

/--
Element `j` of the solution of `Aᵀ * y = x` for the lower triangle of `A`, on the arrays: `x[j]`,
minus the terms `A[i, j] * y[i]` for `i = j + 1, …, n - 1`, divided by `A[j, j]` unless the
diagonal is unit.
-/
public def trsvTLowerAsc (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * trsvTLowerAsc d A x (j + 1 + t))
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/--
Element `j < n` of `trsvTLowerAsc d A x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = j + 1, …, n - 1`, divided by `A[j, j]` unless the diagonal is unit.
-/
public theorem trsvTLowerAsc_eq (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (h : j < n) :
    trsvTLowerAsc d A x j =
      d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
          s - A[(j + 1 + t, j)]'⟨by lia, h⟩ * trsvTLowerAsc d A x (j + 1 + t)) x[j])
        A[(j, j)] := by
  rw [trsvTLowerAsc, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
The step `k` of the lower solve in increasing order: solve for element `j = n - 1 - k` from the
elements below it.
-/
@[expose] public def trsvTLowerAscStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float32Array) : Float32Array :=
  let j := n - 1 - k
  let t := d.apply (Nat.fold k (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * b[x.off + x.inc * (j + 1 + t)]!)
      b[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The array of the lower solve in increasing order. -/
public def trsvTLowerAscData (d : Diag) (A : Mat n n) (x : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for k in 0...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        for t in 0...k with (s := v) do
          have hi : (nu - 1 - k + 1 + t).toNat < n := by grind
          have hk' : (o + c * (nu - 1 - k + 1 + t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s - A.uget ao al rfl rfl hs.1 (nu - 1 - k + 1 + t) (nu - 1 - k) hi hjn *
            a[o + c * (nu - 1 - k + 1 + t)]
        a[o + c * (nu - 1 - k)] :=
          d.apply s (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)).2
  else iterRange (trsvTLowerAscStep d A x) 0 n x.data

public theorem trsvTLowerAscData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerAscData d A x = iterRange (trsvTLowerAscStep d A x) 0 n x.data := by
  unfold trsvTLowerAscData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsvTLowerAscStep d A x)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro k _ hk next a h
      rw [hnu] at hk
      have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + t)]! *
            p.2[x.off + x.inc * (n - 1 - k.toNat + 1 + t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun t a s =>
          s - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + t)]! *
            a[x.off + x.inc * (n - 1 - k.toNat + 1 + t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
            x.off + x.inc * (n - 1 - k.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hj]
        rw [trsvTLowerAscStep, ← set_eq_modifyAt _ _ _ _
          (by rw [Vec.idx_stride, h]; exact x.index_lt (by lia))]
        simp only [hp, hj, Vec.idx_stride, uget_eq_getElem, getElem_def,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
            (A.index_lt (by lia) (by lia))]
      · intro t _ ht next' b a' h'
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
        have hi : (n.toUSize - 1 - k + 1 + t).toNat = n - 1 - k.toNat + 1 + t.toNat := by grind
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k + 1 + t)).toNat =
            x.off + x.inc * (n - 1 - k.toNat + 1 + t.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hi]
        simp only [hp, hi, hj, getElem!_pos a' (x.off + x.inc * (n - 1 - k.toNat + 1 + t.toNat))
            (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + t.toNat))
            (A.index_lt (by lia) (by lia))]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are solved, and the others are unchanged.
-/
theorem iterRange_trsvTLowerAscStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat}
    (hk : k ≤ n) :
    iterRange (trsvTLowerAscStep d A x) 0 k x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v =>
        if n - k ≤ i then trsvTLowerAsc d A x i else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, n - 1 - k ≤ i → i < n → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trsvTLowerAsc d A x i else v)[x.off + x.inc * i]! =
        if n - k ≤ i then trsvTLowerAsc d A x i else x.data[x.off + x.inc * i]! := by
      intro i _ hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt hi),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) hi,
        getElem!_pos x.data _ (x.index_lt hi)]
    have ht : d.apply (Nat.fold k (fun t _ s =>
          s - A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k + 1 + t)]! *
            (x.data.modifyAt x.stride.idx 0 n fun i v =>
              if n - k ≤ i then trsvTLowerAsc d A x i else v)[x.off + x.inc * (n - 1 - k + 1 + t)]!)
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if n - k ≤ i then trsvTLowerAsc d A x i else v)[x.off + x.inc * (n - 1 - k)]!)
          A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]! =
        trsvTLowerAsc d A x (n - 1 - k) := by
      rw [hr (n - 1 - k) (Nat.le_refl _) (by lia), ite_eq_right (by lia),
        trsvTLowerAsc.eq_1 d A x (n - 1 - k),
        Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
      congr 2
      funext t ht s
      rw [hr (n - 1 - k + 1 + t) (by lia) (by lia), ite_eq_left (by lia)]
    simp only [trsvTLowerAscStep, ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _
      (Nat.zero_le _) (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/--
The array of the lower solve in increasing order is the array of `x` with its elements solved.
-/
public theorem trsvTLowerAscData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerAscData d A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTLowerAsc d A x i := by
  rw [trsvTLowerAscData_eq_iterRange, iterRange_trsvTLowerAscStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-- The column solve of `trsmT`: `trsvTUpper`, or `trsvTLowerAsc` for the lower triangle. -/
@[expose] public def trsvTAscSol (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Nat → Float32 :=
  match uplo with
  | .upper => trsvTUpper d A x
  | .lower => trsvTLowerAsc d A x

/-- The array of the column solve of `trsmT`. -/
@[expose] public def trsvTAscData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Float32Array :=
  match uplo with
  | .upper => trsvTUpperData d A x
  | .lower => trsvTLowerAscData d A x

public theorem trsvTAscData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTAscData uplo d A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTAscSol uplo d A x i := by
  cases uplo
  · exact trsvTUpperData_eq d A x
  · exact trsvTLowerAscData_eq d A x

/-! ## `trsvT` -/

/-- The solution of `Aᵀ * y = x` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trsvTSol (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Nat → Float32 :=
  match uplo with
  | .upper => trsvTUpper d A x
  | .lower => trsvTLower d A x

/-- The array of `trsvT`. -/
@[expose] public def trsvTData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Float32Array :=
  match uplo with
  | .upper => trsvTUpperData d A x
  | .lower => trsvTLowerData d A x

public theorem trsvTData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTData uplo d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTSol uplo d A x i := by
  cases uplo
  · exact trsvTUpperData_eq d A x
  · exact trsvTLowerData_eq d A x

/--
`trsvT uplo d A x` solves `Aᵀ * y = x` for the triangle `uplo` of `A`, with a unit diagonal if `d`
is `.unit`, by the loops of the reference BLAS for `TRANS = 'T'`. For the upper triangle, it sets
`y[j]` to `x[j]` minus the dot product of the elements `0, …, j - 1` of column `j` of `A` and of
`y`, divided by `A[j, j]`, for `j = 0, …, n - 1`; for the lower triangle, it does the same from
`j = n - 1` down to `0`, with the elements below the diagonal, from the last one up. It updates `x`
in place when its array is not shared, and leaves the elements of the array outside `x` unchanged.
It reads only the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`. Like the
reference BLAS, it doesn't check for a zero on the diagonal.
-/
@[expose] public def trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Vec n where
  data := trsvTData uplo d A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [trsvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `trsvT uplo d A x` is the array of `x` with its elements solved. -/
public theorem data_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsvT uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTSol uplo d A x i :=
  trsvTData_eq uplo d A x

@[simp] public theorem off_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsvT uplo d A x).off = x.off := rfl

@[simp] public theorem inc_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsvT uplo d A x).inc = x.inc := rfl

/-- Element `i` of `trsvT uplo d A x` is element `i` of the model. -/
public theorem getElem_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (h : i < n) : (trsvT uplo d A x)[i] = trsvTSol uplo d A x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_trsvT uplo d A x) rfl rfl i h

/--
Element `j` of `y = trsvT .upper d A x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal is unit: forward substitution with
`Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsvT_upper (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (h : j < n) :
    (trsvT .upper d A x)[j] = d.apply (Nat.fold j (fun i hi s =>
      s - A[(i, j)]'⟨by lia, h⟩ * (trsvT .upper d A x)[i]'(by lia)) x[j]) A[(j, j)] := by
  rw [getElem_trsvT _ _ _ _ _ h, trsvTSol, trsvTUpper_eq d A x h]
  congr
  funext i hi s
  rw [getElem_trsvT _ _ _ _ _ (by lia), trsvTSol]

/--
Element `j` of `y = trsvT .lower d A x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = n - 1, …, j + 1`, divided by `A[j, j]` unless the diagonal is unit: back substitution with
`Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsvT_lower (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (h : j < n) :
    (trsvT .lower d A x)[j] = d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A[(n - 1 - t, j)]'⟨by lia, h⟩ * (trsvT .lower d A x)[n - 1 - t]'(by lia)) x[j])
        A[(j, j)] := by
  rw [getElem_trsvT _ _ _ _ _ h, trsvTSol, trsvTLower_eq d A x h]
  congr
  funext t ht s
  rw [getElem_trsvT _ _ _ _ _ (by lia), trsvTSol]

end Mat

end BLAS.Float32
