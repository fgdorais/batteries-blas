/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Syr2k
public import BLAS.Float32.GemmT
import all BLAS.Float32.Syrk
import all BLAS.Float32.Syr2k
import all BLAS.Internal

/-!
# Matrix-matrix products on a triangle

`Mat.gemmtr uplo α A B β C` computes `α * A * B + β * C` on the triangle `uplo` of `C` only, by the
loops of the reference `dgemmtr`, and `gemmtrTN`, `gemmtrNT` and `gemmtrTT` do so for `Aᵀ * B`,
`A * Bᵀ` and `Aᵀ * Bᵀ`. As in the reference BLAS, they only scale the triangle by `β` when `α = 0`,
and don't read `C` when `β = 0`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n k : Nat}

/-! ## `gemmtr` -/

/--
The value of the loops of `gemmtr` in the triangle `uplo`, from the old value `v`, and the old value
elsewhere: `betaMul β v`, plus the terms `α * B[l, j] * A[i, l]` for `l = 0, …, k - 1`.
-/
@[expose] public def gemmtrAt (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (i j : Nat) (v : Float32) : Float32 :=
  if uplo.contains i j then
    Nat.fold k (fun l _ s =>
      s + α * B.data[B.off + B.ld * j + l]! * A.data[A.off + A.ld * l + i]!) (betaMul β v)
  else v

/--
The array of `C` with column `j` of `gemmtr` done: the triangle's part of the column scaled by `β`,
then column `l` of `A` times `α * B[l, j]` added to it, for `l = 0, …, k - 1`.
-/
public def gemmtrColData (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) (j : Nat) (hj : j < n) : Float32Array :=
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
    (inplace c do
      for i in lo...hi do
        have hk : (cj + 1 * i).toNat < c.size :=
          C.toNat_col_index_lt hs.2.2.1
            (lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by assumption)) (by lia)
        c[cj + 1 * i] := betaMul β c[cj + 1 * i]
      for l in 0...ku do
        let t := α * B.uget bo bl rfl rfl hs.2.1 l ju (by lia) (by lia)
        for i in lo...hi do
          have hi : i.toNat < n := lt_of_hiU (u := uplo) (j := ju) hnu (by lia) (by lia)
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.2.1 hi (by lia)
          c[cj + 1 * i] := c[cj + 1 * i] + t * A.uget ao al rfl rfl hs.1 i l hi (by lia)).2
  else C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v =>
    gemmtrAt uplo α A B β i j v

public theorem gemmtrColData_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) (j : Nat) (hj : j < n) :
    gemmtrColData uplo α A B β C j hj =
      C.data.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v =>
        gemmtrAt uplo α A B β i j v := by
  unfold gemmtrColData
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
          (uplo.hi n j.toUSize.toNat) fun i v =>
            v + α * B.data[B.off + B.ld * j.toUSize.toNat + l]! * A.data[A.off + A.ld * l + i]!)
          (hF := by simp)]
      · simp only [Tail.run_done, USize.toNat_zero, hku, uplo.toNat_loU, uplo.toNat_hiU hnu hj',
          hju]
        rw [iterRange_modifyAt _ _ (col_injOn _ _ _), modifyAt_modifyAt _ _ (col_injOn _ _ _),
          modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
            (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [gemmtrAt]
        by_cases hc : uplo.contains i j = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro l _ hl next' a' h'
        rw [hku] at hl
        have hblj := getElem!_pos B.data (B.off + B.ld * j.toUSize.toNat + l.toNat)
          (B.index_lt hl hj')
        rw [Tail.run_forInFrom_modify
          (G := fun i v => v + α * B.data[B.off + B.ld * j.toUSize.toNat + l.toNat]! *
            A.data[A.off + A.ld * l.toNat + i]!)
          (idx := (Stride.mk (C.off + C.ld * j.toUSize.toNat) 1).idx)
          (he := fun i _ hi => C.toNat_col_index hs.2.2.1 (lt_of_hiU (u := uplo) hnu hj' hi) hj')]
        · simp only [uplo.toNat_loU, uplo.toNat_hiU hnu hj']
        · intro i _ hi v
          have hi' : i.toNat < n := lt_of_hiU (u := uplo) hnu hj' hi
          simp only [Mat.uget_eq_getElem, Mat.getElem_def, ← hblj,
            getElem!_pos A.data (A.off + A.ld * l.toNat + i.toNat) (A.index_lt hi' hl)]
    · intro _ _ _ _; rfl
  · rfl

/--
The loops of `gemmtr` over the columns from `j` of the matrix at the offset `off` with the leading
dimension `ld` in the array `c` of size `sz`, which `gemmtrColData` updates in place.
-/
public def gemmtrLoop (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (off ld sz : Nat) (hld : n ≤ ld) (hsz : n = 0 ∨ n = 0 ∨ off + ld * (n - 1) + n ≤ sz)
    (j : Nat) (c : Float32Array) (hc : c.size = sz) : Float32Array :=
  if hj : j < n then
    gemmtrLoop uplo α A B β off ld sz hld hsz (j + 1)
      (gemmtrColData uplo α A B β ⟨c, off, ld, hld, by rw [hc]; exact hsz⟩ j hj)
      (by rw [gemmtrColData_eq, size_modifyAt]; exact hc)
  else c
termination_by n - j

private theorem gemmtrLoop_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) (j : Nat) (hj : j ≤ n) (c : Float32Array) (hc : c.size = C.data.size)
    (hinv : c = mapMat C.data C.off C.ld n 0 j (gemmtrAt uplo α A B β)) :
    gemmtrLoop uplo α A B β C.off C.ld C.data.size C.le_ld C.bound j c hc =
      mapMat C.data C.off C.ld n 0 n (gemmtrAt uplo α A B β) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j c with
  | ind e ih =>
    rw [gemmtrLoop]
    split
    · rename_i hjn
      refine ih (n - (j + 1)) (by lia) (j + 1) hjn _ _ ?_ rfl
      rw [gemmtrColData_eq]
      dsimp only
      rw [hinv]
      exact modifyAt_col_mapMat _ _ _ C.le_ld j _
    · rename_i hjn
      obtain rfl : j = n := by lia
      exact hinv

/-- The value of `gemmtr` at `(i, j)`, with the special case `α = 0` of the reference BLAS. -/
@[expose] public def gemmtrEntryAt (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n)
    (β : Float32) (i j : Nat) (v : Float32) : Float32 :=
  if α == 0 then scalTriAt uplo β i j v else gemmtrAt uplo α A B β i j v

/-- The array of `gemmtr`. -/
public def gemmtrData (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) : Float32Array :=
  if α == 0 then scalTriData uplo β C
  else gemmtrLoop uplo α A B β C.off C.ld C.data.size C.le_ld C.bound 0 C.data rfl

public theorem gemmtrData_eq (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) :
    gemmtrData uplo α A B β C = mapMat C.data C.off C.ld n 0 n (gemmtrEntryAt uplo α A B β) := by
  unfold gemmtrData gemmtrEntryAt
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact gemmtrLoop_eq uplo α A B β C 0 (Nat.zero_le _) _ rfl
      (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm
  · simp only [↓reduceIte, scalTriData_eq]

/--
`gemmtr uplo α A B β C` is `α * A * B + β * C` on the triangle `uplo` of `C`, by the loops of the
reference BLAS: for each column `j`, it scales the triangle's part of the column by `β`, or sets it
to `0` without reading it when `β = 0`, then adds column `l` of `A` times `α * B[l, j]` to it, for
`l = 0, …, k - 1`. As in the reference BLAS, it only scales the triangle when `α = 0`. It updates
`C` in place when its array is not shared, and leaves the elements of the array outside the
triangle unchanged.
-/
@[expose] public def gemmtr (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) : Mat n n where
  data := gemmtrData uplo α A B β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [gemmtrData_eq, size_mapMat]; exact C.bound

public theorem data_gemmtr (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) :
    (gemmtr uplo α A B β C).data = mapMat C.data C.off C.ld n 0 n (gemmtrEntryAt uplo α A B β) :=
  gemmtrData_eq uplo α A B β C

@[simp] public theorem off_gemmtr (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n)
    (β : Float32) (C : Mat n n) : (gemmtr uplo α A B β C).off = C.off := rfl

@[simp] public theorem ld_gemmtr (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n)
    (β : Float32) (C : Mat n n) : (gemmtr uplo α A B β C).ld = C.ld := rfl

/--
Element `(i, j)` of `gemmtr uplo α A B β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, and otherwise `betaMul β C[i, j]`, plus the terms `α * B[l, j] * A[i, l]` for
`l = 0, …, k - 1`, added from the left. The other elements are those of `C`.
-/
public theorem getElem_gemmtr (uplo : Uplo) (α : Float32) (A : Mat n k) (B : Mat k n) (β : Float32)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (gemmtr uplo α A B β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else Nat.fold k (fun l hl s => s + α * B[(l, j)]'⟨hl, h.2⟩ * A[(i, l)]'⟨h.1, hl⟩)
          (betaMul β C[(i, j)])
      else C[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_gemmtr uplo α A B β C) rfl rfl i j h, gemmtrEntryAt]
  cases hc : uplo.contains i j
  · cases α == 0 <;> simp [scalTriAt, gemmtrAt, hc]
  · cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte, gemmtrAt, hc]
      congr 1
      funext l hl s
      rw [getElem!_pos B.data _ (B.index_lt hl h.2), getElem!_pos A.data _ (A.index_lt h.1 hl)]
      rfl
    · simp [scalTriAt, hc]

/-! ## `gemmtrTN` -/

/-- The value of the loops of `gemmtrTN` in the triangle `uplo`, and the old value elsewhere. -/
@[expose] public def gemmtrTNAt (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  if uplo.contains i j then syrkTVal α β (syr2kTSum A B i j) v else v

/-- The array of `gemmtrTN`, for `α ≠ 0`. -/
public def gemmtrTNCols (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (C : Mat n n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ C.data.size < USize.size ∧
      n < USize.size ∧ k < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let c := C.data
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    (inplace c do
      for j in 0...nu do
        let cj := co + cl * j
        let lo := uplo.loU j
        let s := syr2kTSums uplo A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.2 hs.2.2.2.1 j.toNat (by lia)
        for i in lo...uplo.hiU nu j do
          have hi : i.toNat < n := lt_of_hiU (u := uplo) (j := j) hnu (by lia) (by lia)
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.2.1 hi (by lia)
          c[cj + 1 * i] := syrkTVal α β s[(i - lo).toNat]! c[cj + 1 * i]).2
  else mapMat C.data C.off C.ld n 0 n (gemmtrTNAt uplo α A B β)

public theorem gemmtrTNCols_eq (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) :
    gemmtrTNCols uplo α A B β C = mapMat C.data C.off C.ld n 0 n (gemmtrTNAt uplo α A B β) := by
  unfold gemmtrTNCols
  split
  · rename_i hs
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 n fun i v =>
        gemmtrTNAt uplo α A B β i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ C.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify
        (G := fun i v => syrkTVal α β (syr2kTSum A B i j.toNat) v)
        (idx := (Stride.mk (C.off + C.ld * j.toNat) 1).idx)
        (he := fun i _ hi => C.toNat_col_index hs.2.2.1 (lt_of_hiU (u := uplo) hnu hj hi) hj)]
      · apply run_congr
        simp only [uplo.toNat_loU, uplo.toNat_hiU hnu hj]
        rw [modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
          (uplo.hi_le hj)]
        apply modifyAt_congr_fun
        intro i v _ hi
        simp only [gemmtrTNAt]
        by_cases hc : uplo.contains i j.toNat = true
        · rw [ite_eq_left ((uplo.contains_iff hi).1 hc), ite_eq_left hc]
        · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h')), ite_eq_right hc]
      · intro i hlo hhi v
        rw [getElem!_syr2kTSums uplo A B _ _ _ hj hnu hlo hhi]
  · rfl

/-- The value of `gemmtrTN` at `(i, j)`, with the special case `α = 0` of the reference BLAS. -/
@[expose] public def gemmtrTNEntryAt (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (i j : Nat) (v : Float32) : Float32 :=
  if α == 0 then scalTriAt uplo β i j v else gemmtrTNAt uplo α A B β i j v

/-- The array of `gemmtrTN`. -/
public def gemmtrTNData (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32) (C : Mat n n) :
    Float32Array :=
  if α == 0 then scalTriData uplo β C else gemmtrTNCols uplo α A B β C

public theorem gemmtrTNData_eq (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) :
    gemmtrTNData uplo α A B β C =
      mapMat C.data C.off C.ld n 0 n (gemmtrTNEntryAt uplo α A B β) := by
  unfold gemmtrTNData gemmtrTNEntryAt
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, gemmtrTNCols_eq]
  · simp only [↓reduceIte, scalTriData_eq]

/--
`gemmtrTN uplo α A B β C` is `α * Aᵀ * B + β * C` on the triangle `uplo` of `C`, by the loops of
the reference BLAS: for each element `(i, j)` of the triangle, it sums the products
`A[l, i] * B[l, j]` for `l = 0, …, k - 1` from the left, into `t`, then writes
`α * t + β * C[i, j]`, or `α * t` without reading `C[i, j]` when `β = 0`. It computes the sums of
four elements of a column at a time, by the loops of `gemvT`, which gives the same sums. As in the
reference BLAS, it only scales the triangle when `α = 0`. It updates `C` in place when its array
is not shared, and leaves the elements of the array outside the triangle unchanged.
-/
@[expose] public def gemmtrTN (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) : Mat n n where
  data := gemmtrTNData uplo α A B β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [gemmtrTNData_eq, size_mapMat]; exact C.bound

public theorem data_gemmtrTN (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) :
    (gemmtrTN uplo α A B β C).data =
      mapMat C.data C.off C.ld n 0 n (gemmtrTNEntryAt uplo α A B β) :=
  gemmtrTNData_eq uplo α A B β C

@[simp] public theorem off_gemmtrTN (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) : (gemmtrTN uplo α A B β C).off = C.off := rfl

@[simp] public theorem ld_gemmtrTN (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) : (gemmtrTN uplo α A B β C).ld = C.ld := rfl

/--
Element `(i, j)` of `gemmtrTN uplo α A B β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, and otherwise `α * t`, when `β = 0`, or `α * t + β * C[i, j]`, where `t` is the sum of
the products `A[l, i] * B[l, j]` for `l = 0, …, k - 1`, from the left. The other elements are
those of `C`.
-/
public theorem getElem_gemmtrTN (uplo : Uplo) (α : Float32) (A B : Mat k n) (β : Float32)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (gemmtrTN uplo α A B β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else
          let t := Nat.fold k (fun l hl s => s + A[(l, i)]'⟨hl, h.1⟩ * B[(l, j)]'⟨hl, h.2⟩) 0
          if β == 0 then α * t else α * t + β * C[(i, j)]
      else C[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_gemmtrTN uplo α A B β C) rfl rfl i j h, gemmtrTNEntryAt]
  have e : syr2kTSum A B i j =
      Nat.fold k (fun l hl s => s + A[(l, i)]'⟨hl, h.1⟩ * B[(l, j)]'⟨hl, h.2⟩) 0 := by
    unfold syr2kTSum
    congr
    funext l hl s
    rw [getElem!_pos A.data _ (A.index_lt hl h.1), getElem!_pos B.data _ (B.index_lt hl h.2)]
    rfl
  cases hα : α == 0 <;> cases hc : uplo.contains i j <;>
    simp [scalTriAt, gemmtrTNAt, syrkTVal, hc, e]

/-! ## `gemmtrNT` and `gemmtrTT` -/

/--
`gemmtrNT uplo α A B β C` is `α * A * Bᵀ + β * C` on the triangle `uplo` of `C`, by the loops of
the reference BLAS, which are those of `gemmtr` on `Bᵀ`: it computes `gemmtr` on a packed copy of
the transpose of `B`.
-/
@[expose] public def gemmtrNT (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) : Mat n n :=
  gemmtr uplo α A B.transpose β C

/--
`gemmtrTT uplo α A B β C` is `α * Aᵀ * Bᵀ + β * C` on the triangle `uplo` of `C`, by the loops of
the reference BLAS, which are those of `gemmtrTN` on `Bᵀ`: it computes `gemmtrTN` on a packed copy
of the transpose of `B`.
-/
@[expose] public def gemmtrTT (uplo : Uplo) (α : Float32) (A : Mat k n) (B : Mat n k) (β : Float32)
    (C : Mat n n) : Mat n n :=
  gemmtrTN uplo α A B.transpose β C

/--
Element `(i, j)` of `gemmtrNT uplo α A B β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, and otherwise `betaMul β C[i, j]`, plus the terms `α * B[j, l] * A[i, l]` for
`l = 0, …, k - 1`, added from the left. The other elements are those of `C`.
-/
public theorem getElem_gemmtrNT (uplo : Uplo) (α : Float32) (A B : Mat n k) (β : Float32)
    (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (gemmtrNT uplo α A B β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else Nat.fold k (fun l hl s => s + α * B[(j, l)]'⟨h.2, hl⟩ * A[(i, l)]'⟨h.1, hl⟩)
          (betaMul β C[(i, j)])
      else C[(i, j)] := by
  rw [gemmtrNT, getElem_gemmtr _ _ _ _ _ _ _ _ h]
  simp only [getElem_transpose]

/--
Element `(i, j)` of `gemmtrTT uplo α A B β C` in the triangle `uplo` is `betaMul β C[i, j]` when
`α = 0`, and otherwise `α * t`, when `β = 0`, or `α * t + β * C[i, j]`, where `t` is the sum of
the products `A[l, i] * B[j, l]` for `l = 0, …, k - 1`, from the left. The other elements are
those of `C`.
-/
public theorem getElem_gemmtrTT (uplo : Uplo) (α : Float32) (A : Mat k n) (B : Mat n k)
    (β : Float32) (C : Mat n n) (i j : Nat) (h : i < n ∧ j < n) :
    (gemmtrTT uplo α A B β C)[(i, j)] =
      if uplo.contains i j then
        if α == 0 then betaMul β C[(i, j)]
        else
          let t := Nat.fold k (fun l hl s => s + A[(l, i)]'⟨hl, h.1⟩ * B[(j, l)]'⟨h.2, hl⟩) 0
          if β == 0 then α * t else α * t + β * C[(i, j)]
      else C[(i, j)] := by
  rw [gemmtrTT, getElem_gemmtrTN _ _ _ _ _ _ _ _ h]
  simp only [getElem_transpose]

end Mat

end BLAS.Float32
