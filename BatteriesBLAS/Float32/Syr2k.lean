/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float32.Syrk
import all BatteriesBLAS.Float32.Syrk
import all BatteriesBLAS.Internal

/-!
# Symmetric rank-2k updates

`Mat.syr2k uplo α A B β C` computes `α * A * Bᵀ + α * B * Aᵀ + β * C` and
`Mat.syr2kT uplo α A B β C` computes `α * Aᵀ * B + α * Bᵀ * A + β * C`, on the triangle `uplo` of
`C`, by the loops of the reference BLAS, as `syrk` and `syrkT` do for `α * A * Aᵀ + β * C` and
`α * Aᵀ * A + β * C`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n k : Nat}

/-! ## `syr2k` -/

/--
The term `l` of the loops of `syr2k` at `(i, j)`, added to `s`, on the arrays: `s` when `α = 0` or
`A[j, l] = B[j, l] = 0`, which the reference BLAS skips, and
`s + A[i, l] * (α * B[j, l]) + B[i, l] * (α * A[j, l])` otherwise.
-/
@[expose] public def syr2kTerm (α : Float32) (A B : Mat n k) (l i j : Nat) (s : Float32) : Float32 :=
  if α == 0 || (A.data[A.off + A.ld * l + j]! == 0 && B.data[B.off + B.ld * l + j]! == 0) then s
  else s + A.data[A.off + A.ld * l + i]! * (α * B.data[B.off + B.ld * l + j]!) +
    B.data[B.off + B.ld * l + i]! * (α * A.data[A.off + A.ld * l + j]!)

/-- The value of the loops of `syr2k` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def syr2kAt (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  if uplo.contains i j then Nat.fold k (fun l _ s => syr2kTerm α A B l i j s) (betaMul β v)
  else v

/--
The array of `C` with column `j` of `syr2k` done: the triangle's part of the column scaled by `β`,
then the terms of each `l = 0, …, k - 1` added to it.
-/
public def syr2kColData (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (C : Mat n n)
    (j : Nat) (hj : j < n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ C.data.size < USize.size ∧
      n < USize.size ∧ k < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let ku := k.toUSize
    have hku : ku.toNat = k := by grind
    let ju := j.toUSize
    have hju : ju.toNat = j := by grind
    let c := C.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    let cj := C.off.toUSize + C.ld.toUSize * ju
    let lo := uplo.loU ju
    let hi := uplo.hiU nu ju
    inplace c do
      for i in lo...hi do
        have hk : (cj + 1 * i).toNat < c.size :=
          C.toNat_col_index_lt hs.2.2.1
            (lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by assumption)) (by lia)
        c[cj + 1 * i] := betaMul β c[cj + 1 * i]
      for l in 0...ku do
        let ajl := A.uget ao al rfl rfl hs.1 ju l (by lia) (by lia)
        let bjl := B.uget bo bl rfl rfl hs.2.1 ju l (by lia) (by lia)
        let t1 := α * bjl
        let t2 := α * ajl
        -- A skipped term runs an empty loop: an `if` would allocate a closure per term.
        let hi' := syrkRows lo hi (α == 0 || (ajl == 0 && bjl == 0))
        have hh : hi'.toNat ≤ hi.toNat := syrkRows_le (uplo.loU_le_hiU hnu (by lia)) _
        for i in lo...hi' do
          have hi : i.toNat < n := lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by lia)
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.2.1 hi (by lia)
          c[cj + 1 * i] := c[cj + 1 * i] + A.uget ao al rfl rfl hs.1 i l hi (by lia) * t1 +
            B.uget bo bl rfl rfl hs.2.1 i l hi (by lia) * t2
  else C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v =>
    syr2kAt uplo α A B β i j v

public theorem syr2kColData_eq (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) (j : Nat) (hj : j < n) :
    syr2kColData uplo α A B β C j hj =
      C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v =>
        syr2kAt uplo α A B β i j v := by
  unfold syr2kColData
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    have hku : k.toUSize.toNat = k := by grind
    have hju : j.toUSize.toNat = j := by grind
    have hj' : j.toUSize.toNat < n := by lia
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v)
      (idx := (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx)
      (he := fun i _ hi => C.toNat_col_index hs.2.2.1 (lt_of_hiU (u := uplo) hnu hj' hi) hj')]
    · rw [Tail.run_forInFrom_unit (F := fun l c =>
        c.modifyAt (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx (uplo.lo j.toUSize.toNat)
          (uplo.hi n j.toUSize.toNat) fun i v => syr2kTerm α A B l i j.toUSize.toNat v)
          (hF := by simp)]
      · simp only [Tail.run_done, USize.toNat_zero, hku, uplo.toNat_loU, uplo.toNat_hiU hnu hj',
          hju]
        rw [iterRange_modifyAt _ _ (col_injOn _ _ _), modifyAt_modifyAt _ _ (col_injOn _ _ _),
          modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
            (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [syr2kAt]
        by_cases hc : uplo.contains i j = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro l _ hl next' a' h'
        rw [hku] at hl
        have hajl := getElem!_pos A.data (A.off + A.ld * l.toNat + j.toUSize.toNat)
          (A.index_lt hj' hl)
        have hbjl := getElem!_pos B.data (B.off + B.ld * l.toNat + j.toUSize.toNat)
          (B.index_lt hj' hl)
        rw [Tail.run_forInFrom_modify
          (G := fun i v => v + A.data[A.off + A.ld * l.toNat + i]! *
              (α * B.data[B.off + B.ld * l.toNat + j.toUSize.toNat]!) +
            B.data[B.off + B.ld * l.toNat + i]! *
              (α * A.data[A.off + A.ld * l.toNat + j.toUSize.toNat]!))
          (idx := (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx)
          (he := fun i _ hi => C.toNat_col_index hs.2.2.1 (lt_of_hiU (u := uplo) hnu hj'
            (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj') _))) hj')]
        · apply run_congr
          simp only [syrkRows, uplo.toNat_loU, Mat.uget_eq_getElem, Mat.getElem_def, ← hajl,
            ← hbjl]
          split
          next h0 =>
            rw [uplo.toNat_loU, modifyAt_of_le _ _ (Nat.le_refl _),
              modifyAt_congr_fun _ _ (g' := fun _ v => v)
                (fun i v _ _ => by rw [hju] at h0; simp [syr2kTerm, hju, h0]), modifyAt_id]
          next h0 =>
            rw [uplo.toNat_hiU hnu hj']
            apply modifyAt_congr_fun
            intro i v _ _
            rw [hju] at h0
            simp [syr2kTerm, hju, h0]
        · intro i _ hi v
          have hi' : i.toNat < n := lt_of_hiU (u := uplo) hnu hj'
            (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj') _))
          simp only [Mat.uget_eq_getElem, Mat.getElem_def, ← hajl, ← hbjl,
            getElem!_pos A.data (A.off + A.ld * l.toNat + i.toNat) (A.index_lt hi' hl),
            getElem!_pos B.data (B.off + B.ld * l.toNat + i.toNat) (B.index_lt hi' hl)]
    · intro _ _ _ _; rfl
  · rfl

/--
The loops of `syr2k` over the columns from `j` of the matrix at the offset `off` with the leading
dimension `ld` in the array `c` of size `sz`. It takes them rather than the matrix, so that the
array isn't shared, and `syr2kColData` updates it in place.
-/
public def syr2kLoop (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (off ld sz : Nat)
    (hld : n ≤ ld) (hsz : n = 0 ∨ n = 0 ∨ off + ld * (n - 1) + n ≤ sz) (j : Nat)
    (c : Float32Array) (hc : c.size = sz) : Float32Array :=
  if hj : j < n then
    syr2kLoop uplo α A B β off ld sz hld hsz (j + 1)
      (syr2kColData uplo α A B β ⟨c, off, ld, hld, by rw [hc]; exact hsz⟩ j hj)
      (by rw [syr2kColData_eq, size_modifyAt]; exact hc)
  else c
termination_by n - j

private theorem syr2kLoop_eq (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) (j : Nat) (hj : j ≤ n) (c : Float32Array) (hc : c.size = C.data.size)
    (hinv : c = mapMat C.data C.off C.ld n 0 j (syr2kAt uplo α A B β)) :
    syr2kLoop uplo α A B β C.off C.ld C.data.size C.le_ld C.bound j c hc =
      mapMat C.data C.off C.ld n 0 n (syr2kAt uplo α A B β) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j c with
  | ind e ih =>
    rw [syr2kLoop]
    split
    · rename_i hjn
      refine ih (n - (j + 1)) (by lia) (j + 1) hjn _ _ ?_ rfl
      rw [syr2kColData_eq]
      dsimp only
      rw [hinv]
      exact modifyAt_col_mapMat _ _ _ C.le_ld j _
    · rename_i hjn
      obtain rfl : j = n := by lia
      exact hinv

/-- The array of `syr2k`. -/
public def syr2kData (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (C : Mat n n) :
    Float32Array :=
  syr2kLoop uplo α A B β C.off C.ld C.data.size C.le_ld C.bound 0 C.data rfl

public theorem syr2kData_eq (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (C : Mat n n) :
    syr2kData uplo α A B β C = mapMat C.data C.off C.ld n 0 n (syr2kAt uplo α A B β) :=
  syr2kLoop_eq uplo α A B β C 0 (Nat.zero_le _) _ rfl
    (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm

/--
`syr2k uplo α A B β C` is `α * A * Bᵀ + α * B * Aᵀ + β * C`, on the triangle `uplo` of `C`, by the
loops of the reference BLAS: for each column `j`, it scales the triangle's part of the column by
`β`, or sets it to `0` without reading it when `β = 0`, then adds column `l` of `A` times
`α * B[j, l]` and column `l` of `B` times `α * A[j, l]` to it, for `l = 0, …, k - 1`. As in the
reference BLAS, it skips the terms with `A[j, l] = B[j, l] = 0`, and only scales `C` when `α = 0`.
It updates `C` in place when its array is not shared, and leaves the elements of the array outside
the triangle unchanged.
-/
@[expose] public def syr2k (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (C : Mat n n) :
    Mat n n where
  data := syr2kData uplo α A B β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [syr2kData_eq, size_mapMat]; exact C.bound

public theorem data_syr2k (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32) (C : Mat n n) :
    (syr2k uplo α A B β C).data = mapMat C.data C.off C.ld n 0 n (syr2kAt uplo α A B β) :=
  syr2kData_eq uplo α A B β C

@[simp] public theorem off_syr2k (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) : (syr2k uplo α A B β C).off = C.off := rfl

@[simp] public theorem ld_syr2k (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) : (syr2k uplo α A B β C).ld = C.ld := rfl

/--
Element `(i, j)` of `syr2k uplo α A B β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, and otherwise `betaMul β C[i, j]`, plus the terms
`A[i, l] * (α * B[j, l]) + B[i, l] * (α * A[j, l])` for `l = 0, …, k - 1`, added from the left,
except those with `A[j, l] = B[j, l] = 0`. The other elements are those of `C`.
-/
public theorem getElem_syr2k (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (syr2k uplo α A B β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else Nat.fold k (fun l hl s =>
            if A[(j, l)]'⟨h.2, hl⟩ == 0 && B[(j, l)]'⟨h.2, hl⟩ == 0 then s
            else s + A[(i, l)]'⟨h.1, hl⟩ * (α * B[(j, l)]'⟨h.2, hl⟩) +
              B[(i, l)]'⟨h.1, hl⟩ * (α * A[(j, l)]'⟨h.2, hl⟩))
          (betaMul β C[(i, j)])
      else C[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_syr2k uplo α A B β C) rfl rfl i j h, syr2kAt]
  cases hc : uplo.contains i j
  · rfl
  · simp only [↓reduceIte]
    cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext l hl s
      rw [syr2kTerm, getElem!_pos A.data _ (A.index_lt h.2 hl),
        getElem!_pos A.data _ (A.index_lt h.1 hl), getElem!_pos B.data _ (B.index_lt h.2 hl),
        getElem!_pos B.data _ (B.index_lt h.1 hl)]
      simp [hα, getElem_def]
    · simp only [syr2kTerm, hα, Bool.true_or, ↓reduceIte, fold_id]

/-! ## `syr2kT` -/

/-- The sum of the products `A[l, i] * B[l, j]` for `l = 0, …, k - 1`, from the left. -/
@[expose] public def syr2kTSum (A B : Mat k n) (i j : Nat) : Float32 :=
  Nat.fold k (fun l _ s => s + A.data[A.off + A.ld * i + l]! * B.data[B.off + B.ld * j + l]!) 0

/--
The value of the loops of `syr2kT` at an element of the triangle, from the sums `t₁` and `t₂` of
its products and its old value `v`: `α * t₁ + α * t₂` when `β = 0`, without reading `v`, and
`β * v + α * t₁ + α * t₂` otherwise.
-/
@[inline, expose] public def syr2kTVal (α β t₁ t₂ v : Float32) : Float32 :=
  if β == 0 then α * t₁ + α * t₂ else β * v + α * t₁ + α * t₂

/-- The value of the loops of `syr2kT` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def syr2kTAt (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  if uplo.contains i j then syr2kTVal α β (syr2kTSum A B i j) (syr2kTSum B A i j) v else v

/-- The sums of `colsOf` with `colVec` are those of `syr2kT`. -/
private theorem gemvTSum_colsOf₂ (A B : Mat k n) (lo w : Nat) (h : lo + w ≤ n) (j : Nat)
    (hj : j < n) (q : Nat) :
    gemvTSum (colsOf A lo w h) (colVec B j hj) q = syr2kTSum A B (lo + q) j := by
  simp only [gemvTSum, syr2kTSum, colsOf, colVec, Nat.one_mul, Nat.mul_add, Nat.add_assoc]

/--
The sums `syr2kTSum A B i j` for the rows `i` of column `j` in the triangle `uplo`, from the first,
by the loops of `gemvT`.
-/
def syr2kTSums (uplo : Uplo) (A B : Mat k n)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (hk : k < USize.size)
    (hn : n < USize.size) (j : Nat) (hj : j < n) : Float32Array :=
  let lo := uplo.lo j
  let w := uplo.hi n j - lo
  have hw : lo + w ≤ n := by have := uplo.lo_le_hi hj; have := uplo.hi_le hj; lia
  gemvTSums (colsOf A lo w hw) (colVec B j hj) _ _ _ _ rfl rfl rfl rfl hs (by lia)
    k.toUSize (by grind) w.toUSize (by grind) 0 (by simp) (Float32Array.emptyWithCapacity w)

theorem syr2kTSums_spec (uplo : Uplo) (A B : Mat k n)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (hk : k < USize.size)
    (hn : n < USize.size) (j : Nat) (hj : j < n) :
    (syr2kTSums uplo A B hs hk hn j hj).size = uplo.hi n j - uplo.lo j ∧
      ∀ q (h : q < (syr2kTSums uplo A B hs hk hn j hj).size),
        (syr2kTSums uplo A B hs hk hn j hj)[q] = syr2kTSum A B (uplo.lo j + q) j := by
  have hw : uplo.lo j + (uplo.hi n j - uplo.lo j) ≤ n := by
    have := uplo.lo_le_hi hj; have := uplo.hi_le hj; lia
  have := gemvTSums_spec (colsOf A (uplo.lo j) _ hw) (colVec B j hj) _ _ _ _ rfl rfl rfl rfl
    hs (by lia) k.toUSize (by grind) (uplo.hi n j - uplo.lo j).toUSize (by grind) 0
    (by simp) (Float32Array.emptyWithCapacity (uplo.hi n j - uplo.lo j)) (by simp) (by simp)
  refine ⟨this.1, fun q h => ?_⟩
  rw [← gemvTSum_colsOf₂ A B _ _ hw j hj]
  exact this.2 q h

/-- An element of the sums of `syr2kTSums`, by its row `i` in the triangle. -/
private theorem getElem!_syr2kTSums (uplo : Uplo) (A B : Mat k n)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (hk : k < USize.size)
    (hn : n < USize.size) {j : USize} (hj : j.toNat < n) {i nu : USize} (hnu : nu.toNat = n)
    (hlo : (uplo.loU j).toNat ≤ i.toNat) (hhi : i.toNat < (uplo.hiU nu j).toNat) :
    (syr2kTSums uplo A B hs hk hn j.toNat hj)[(i - uplo.loU j).toNat]! =
      syr2kTSum A B i.toNat j.toNat := by
  have hsp := syr2kTSums_spec uplo A B hs hk hn _ hj
  have hq : i.toNat - uplo.lo j.toNat < (syr2kTSums uplo A B hs hk hn _ hj).size := by
    rw [hsp.1, ← uplo.toNat_loU, ← uplo.toNat_hiU hnu hj]; lia
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hlo), uplo.toNat_loU,
    getElem!_pos (syr2kTSums uplo A B hs hk hn _ hj) _ hq, hsp.2,
    Nat.add_sub_cancel' (by rw [← uplo.toNat_loU]; exact hlo)]

/-- The array of `syr2kT`, for `α ≠ 0`. -/
public def syr2kTData (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (C : Mat n n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ C.data.size < USize.size ∧
      n < USize.size ∧ k < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let c := C.data
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    inplace c do
      for j in 0...nu do
        let cj := co + cl * j
        let lo := uplo.loU j
        let s₁ := syr2kTSums uplo A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.2 hs.2.2.2.1 j.toNat (by lia)
        let s₂ := syr2kTSums uplo B A ⟨hs.2.1, hs.1⟩ hs.2.2.2.2 hs.2.2.2.1 j.toNat (by lia)
        for i in lo...uplo.hiU nu j do
          have hi : i.toNat < n := lt_of_hiU (u := uplo) (j := j) hnu (by lia) (by lia)
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.2.1 hi (by lia)
          c[cj + 1 * i] :=
            syr2kTVal α β s₁[(i - lo).toNat]! s₂[(i - lo).toNat]! c[cj + 1 * i]
  else mapMat C.data C.off C.ld n 0 n (syr2kTAt uplo α A B β)

public theorem syr2kTData_eq (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) :
    syr2kTData uplo α A B β C = mapMat C.data C.off C.ld n 0 n (syr2kTAt uplo α A B β) := by
  unfold syr2kTData
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v => syr2kTAt uplo α A B β i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ C.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify
        (G := fun i v => syr2kTVal α β (syr2kTSum A B i j.toNat) (syr2kTSum B A i j.toNat) v)
        (idx := (Stride.mk (C.off + C.ld * j.toNat) 1).idx)
        (he := fun i _ hi => C.toNat_col_index hs.2.2.1 (lt_of_hiU (u := uplo) hnu hj hi) hj)]
      · apply run_congr
        simp only [uplo.toNat_loU, uplo.toNat_hiU hnu hj]
        rw [modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
          (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [syr2kTAt]
        by_cases hc : uplo.contains i j.toNat = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro i hlo hhi v
        rw [getElem!_syr2kTSums uplo A B _ _ _ hj hnu hlo hhi,
          getElem!_syr2kTSums uplo B A _ _ _ hj hnu hlo hhi]
  · rfl

/--
The value of `syr2kT` in the triangle `uplo`, and the old value elsewhere, with the special cases
of the reference BLAS: `betaMul β v` when `α = 0`, and `v` when `k = 0` and `β = 1`.
-/
@[expose] public def syr2kTEntryAt (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (i j : Nat) (v : Float32) : Float32 :=
  if α == 0 then scalTriAt uplo β i j v
  else if k == 0 && β == 1 then v
  else syr2kTAt uplo α A B β i j v

/--
`syr2kT uplo α A B β C` is `α * Aᵀ * B + α * Bᵀ * A + β * C`, on the triangle `uplo` of `C`, by
the loops of the reference BLAS: for each element `(i, j)` of the triangle, it sums the products
`A[l, i] * B[l, j]` into `t₁` and `B[l, i] * A[l, j]` into `t₂`, for `l = 0, …, k - 1` from the
left, then writes `β * C[i, j] + α * t₁ + α * t₂`, or `α * t₁ + α * t₂` without reading `C[i, j]`
when `β = 0`. It computes the sums of four elements of a column at a time, by the loops of `gemvT`,
which gives the same sums. As in the reference BLAS, it only scales `C` when `α = 0`, and returns
`C` when `k = 0` and `β = 1`. It updates `C` in place when its array is not shared, and leaves the
elements of the array outside the triangle unchanged.
-/
@[expose] public def syr2kT (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (C : Mat n n) :
    Mat n n :=
  if α == 0 then
    { data := scalTriData uplo β C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalTriData_eq, size_mapMat]; exact C.bound }
  else if k == 0 && β == 1 then C
  else
    { data := syr2kTData uplo α A B β C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [syr2kTData_eq, size_mapMat]; exact C.bound }

public theorem data_syr2kT (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (C : Mat n n) :
    (syr2kT uplo α A B β C).data =
      mapMat C.data C.off C.ld n 0 n (syr2kTEntryAt uplo α A B β) := by
  unfold syr2kT syr2kTEntryAt
  cases hα : α == 0
  · cases hq : (k == 0 && β == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, syr2kTData_eq]
    · simp only [Bool.false_eq_true, ↓reduceIte, mapMat_id]
  · simp only [↓reduceIte, scalTriData_eq]

@[simp] public theorem off_syr2kT (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) : (syr2kT uplo α A B β C).off = C.off := by
  unfold syr2kT; split
  · rfl
  · split <;> rfl

@[simp] public theorem ld_syr2kT (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) : (syr2kT uplo α A B β C).ld = C.ld := by
  unfold syr2kT; split
  · rfl
  · split <;> rfl

/--
Element `(i, j)` of `syr2kT uplo α A B β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, `C[i, j]` when `k = 0` and `β = 1`, and otherwise `α * t₁ + α * t₂`, when `β = 0`, or
`β * C[i, j] + α * t₁ + α * t₂`, where `t₁` and `t₂` are the sums of the products
`A[l, i] * B[l, j]` and `B[l, i] * A[l, j]` for `l = 0, …, k - 1`, from the left. The other
elements are those of `C`.
-/
public theorem getElem_syr2kT (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (syr2kT uplo α A B β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else if k == 0 && β == 1 then C[(i, j)]
        else
          let t₁ := Nat.fold k (fun l hl s => s + A[(l, i)]'⟨hl, h.1⟩ * B[(l, j)]'⟨hl, h.2⟩) 0
          let t₂ := Nat.fold k (fun l hl s => s + B[(l, i)]'⟨hl, h.1⟩ * A[(l, j)]'⟨hl, h.2⟩) 0
          if β == 0 then α * t₁ + α * t₂ else β * C[(i, j)] + α * t₁ + α * t₂
      else C[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_syr2kT uplo α A B β C) (off_syr2kT ..) (ld_syr2kT ..)
    i j h, syr2kTEntryAt]
  have e : ∀ X Y : Mat k n, syr2kTSum X Y i j =
      Nat.fold k (fun l hl s => s + X[(l, i)]'⟨hl, h.1⟩ * Y[(l, j)]'⟨hl, h.2⟩) 0 := by
    intro X Y
    unfold syr2kTSum
    congr
    funext l hl s
    rw [getElem!_pos X.data _ (X.index_lt hl h.1), getElem!_pos Y.data _ (Y.index_lt hl h.2)]
    rfl
  cases hα : α == 0 <;> cases hq : (k == 0 && β == 1) <;> cases hc : uplo.contains i j <;>
    simp [scalTriAt, syr2kTAt, syr2kTVal, hc, e]

end Mat

end BLAS.Float32
