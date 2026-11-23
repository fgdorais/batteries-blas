/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Trmm
import all BLAS.Internal

/-!
# Triangular product with several rows, on the right

`Mat.trmmRight uplo d α A B` computes `α * B * A` and `Mat.trmmRightT uplo d α A B` computes
`α * B * Aᵀ`, for a triangular matrix `A`, over `B`, by the loops of the reference BLAS for
`SIDE = 'R'`. As in the reference BLAS, both set `B` to `0` without reading `A` or `B` when
`α = 0`.

The reference loops update each column `j` of `B` from columns of `B` that they haven't overwritten
yet: they scale column `j` by `α * A[j, j]` (or `α` for a unit diagonal), and add `α * A[k, j]`
times column `k` (`α * A[j, k]` for `trmmRightT`) for the other columns `k` of the triangle, in
their order. `trmmRightT` reaches some columns in a different order of `j`, but each element gets
the same operations in the same order, so these kernels compute one column at a time, in an order
of `j` where the columns they read are still those of `B`. As in the reference loops, `trmmRightT`
skips the scaling of a column when its factor is `1`. Each specification is a fold over `B`
itself.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {m n : Nat}

/-! ## The column steps -/

/-- Scale `v` by `t`, unless `t = 1`, as the reference `trmm` does for `TRANSA = 'T'`. -/
@[expose] public def scaleUnlessOne (t v : Float32) : Float32 := if t == 1 then v else t * v

/--
The step of the right products for column `j`, on the array `c`: scale each element by `sc`, then
add `w t` times the element of column `k t` in the same row, for `t = 0, …, L - 1`.
-/
@[expose] public def rightCol (B : Mat m n) (j L : Nat) (k : Nat → Nat) (w : Nat → Float32)
    (sc : Float32 → Float32) (c : Float32Array) : Float32Array :=
  c.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m fun i v =>
    Nat.fold L (fun t _ s => s + w t * c[B.off + B.ld * k t + i]!) (sc v)

/--
Adding `w k` times column `ok k` of `c` to column `j`, for `k` from `lo` to `lo + K - 1`, when
those columns are not column `j`, adds the terms in that order to each element.
-/
private theorem iterRange_addCols (c : Float32Array) (oj : Nat) (ok : Nat → Nat)
    (w : Nat → Float32) (lo K : Nat)
    (hd : ∀ k, lo ≤ k → k < lo + K → ∀ i, i < m → ∀ i', i' < m → oj + i ≠ ok k + i') :
    iterRange (fun k c => c.modifyAt (Stride.mk oj 1).idx 0 m fun i v => v + w k * c[ok k + i]!)
        lo (lo + K) c =
      c.modifyAt (Stride.mk oj 1).idx 0 m fun i v =>
        Nat.fold K (fun t _ s => s + w (lo + t) * c[ok (lo + t) + i]!) v := by
  induction K with
  | zero =>
    rw [Nat.add_zero, iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _; rw [Nat.fold_zero]
  | succ K ih =>
    rw [← Nat.add_assoc, iterRange_succ _ (Nat.le_add_right _ _),
      ih (fun k h₁ h₂ => hd k h₁ (by lia)), modifyAt_modifyAt _ _ (col_injOn _ _ _)]
    apply modifyAt_congr_fun
    intro i v _ hi
    rw [Nat.fold_succ, getElem!_modifyAt_of_ne _ _ _ (fun i' _ hi' e => by
      simp only [Stride.idx, Nat.one_mul] at e
      exact hd (lo + K) (Nat.le_add_right _ _) (by lia) i' hi' i hi e)]

/--
The scaling of column `j`, then the additions of the columns `k t ≠ j`, is `rightCol`: the columns
it reads are not changed by the scaling.
-/
private theorem addCols_scale (B : Mat m n) (a : Float32Array) (j L : Nat) (k : Nat → Nat)
    (w : Nat → Float32) (sc : Float32 → Float32) (hk : ∀ t, t < L → k t ≠ j ∧ k t < n) :
    iterRange (fun t c => c.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m fun i v =>
        v + w t * c[B.off + B.ld * k t + i]!) 0 L
      (a.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m fun _ v => sc v) =
      rightCol B j L k w sc a := by
  have hd : ∀ t, 0 ≤ t → t < 0 + L → ∀ i, i < m → ∀ i', i' < m →
      B.off + B.ld * j + i ≠ B.off + B.ld * k t + i' :=
    fun t _ ht i hi i' hi' => col_index_ne hi hi' B.le_ld (Ne.symm (hk t (by lia)).1)
  have h := iterRange_addCols (m := m)
    (a.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m fun _ v => sc v)
    (B.off + B.ld * j) (fun t => B.off + B.ld * k t) w 0 L hd
  simp only [Nat.zero_add] at h
  rw [h, modifyAt_modifyAt _ _ (col_injOn _ _ _), rightCol]
  apply modifyAt_congr_fun
  intro i v _ _
  congr 1
  funext t ht s
  rw [getElem!_modifyAt_of_ne _ _ _ (fun i' _ hi' e => by
    simp only [Stride.idx, Nat.one_mul] at e
    exact hd t (Nat.zero_le _) (by lia) i' hi' _ (by assumption) e)]

/-- An element of a column `j` outside the columns of a `mapMat` is unchanged. -/
private theorem getElem!_mapMat_col_of_not (a : Float32Array) (off ld lo hi : Nat)
    (g : Nat → Nat → Float32 → Float32) (hml : m ≤ ld) {j : Nat} (hj : ¬(lo ≤ j ∧ j < hi))
    {l : Nat}
    (hl : l < m) : (mapMat a off ld m lo hi g)[off + ld * j + l]! = a[off + ld * j + l]! := by
  by_cases hq : off + ld * j + l < a.size
  · rw [getElem!_pos _ _ (by rw [size_mapMat]; exact hq), getElem!_pos a _ hq,
      getElem_mapMat_of_ne _ _ _ _ _ _ _ (fun i' j' hi' h₁ h₂ e' => by
        by_cases hjj : j = j'
        · subst hjj; exact hj ⟨h₁, h₂⟩
        · exact col_index_ne hl hi' hml hjj e') hq]
  · rw [getElem!_neg _ _ (by rw [size_mapMat]; exact hq), getElem!_neg a _ hq]

/-- The value of an element of a right product, from its old value `v`. -/
@[expose] public def rightVal (B : Mat m n) (L : Nat → Nat) (k : Nat → Nat → Nat)
    (w : Nat → Nat → Float32) (sc : Nat → Float32 → Float32) (i j : Nat) (v : Float32) : Float32 :=
  Nat.fold (L j) (fun t _ s => s + w j t * B.data[B.off + B.ld * k j t + i]!) (sc j v)

/--
The steps for the columns `j < J`, in increasing order, when each column reads only columns after
it, map those columns by `rightVal`.
-/
private theorem iterRange_rightCol_asc (B : Mat m n) (L : Nat → Nat) (k : Nat → Nat → Nat)
    (w : Nat → Nat → Float32) (sc : Nat → Float32 → Float32)
    (hk : ∀ j t, j < n → t < L j → j < k j t ∧ k j t < n) {J : Nat} (hJ : J ≤ n) :
    iterRange (fun j c => rightCol B j (L j) (k j) (w j) (sc j) c) 0 J B.data =
      mapMat B.data B.off B.ld m 0 J (rightVal B L k w sc) := by
  induction J with
  | zero => rw [iterRange_self, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ J ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), rightCol,
      ← modifyAt_col_mapMat _ _ _ B.le_ld J]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [rightVal]
    congr 1
    funext t ht s
    have := hk J t (by lia) ht
    rw [getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hi]

/--
The steps for the columns `j ≥ n - T`, in decreasing order, when each column reads only columns
before it, map those columns by `rightVal`.
-/
private theorem iterRange_rightCol_desc (B : Mat m n) (L : Nat → Nat) (k : Nat → Nat → Nat)
    (w : Nat → Nat → Float32) (sc : Nat → Float32 → Float32)
    (hk : ∀ j t, j < n → t < L j → k j t < j) {T : Nat} (hT : T ≤ n) :
    iterRange (fun p c => rightCol B (n - 1 - p) (L (n - 1 - p)) (k (n - 1 - p)) (w (n - 1 - p))
        (sc (n - 1 - p)) c) 0 T B.data =
      mapMat B.data B.off B.ld m (n - T) n (rightVal B L k w sc) := by
  induction T with
  | zero => rw [iterRange_self, Nat.sub_zero, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ T ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), rightCol,
      show n - T = n - 1 - T + 1 by lia, show n - (T + 1) = n - 1 - T by lia,
      ← modifyAt_col_mapMat_lo _ _ _ B.le_ld (show n - 1 - T < n by lia)]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [rightVal]
    congr 1
    funext t ht s
    have := hk (n - 1 - T) t (by lia) ht
    rw [getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hi]

/-! ## `trmmRight` for the lower triangle -/

/-- The parameters of `rightVal` for `trmmRight .lower`: the columns `k = j + 1, …, n - 1`. -/
@[expose] public def trmmRightLowerW (α : Float32) (A : Mat n n) (j t : Nat) : Float32 :=
  α * A.data[A.off + A.ld * j + (j + 1 + t)]!

/-- The array of `trmmRight .lower` for `α ≠ 0`. -/
public def trmmRightLowerData (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    inplace b do
      for j in 0...nu do
        let cj := bo + bl * j
        let tj := d.mul α (A.uget ao al rfl rfl hs.1 j j (by lia) (by lia))
        for i in 0...mu do
          have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          b[cj + 1 * i] := tj * b[cj + 1 * i]
        for t in 0...(nu - 1 - j) do
          have hk : (j + 1 + t).toNat < n := by grind
          let w := α * A.uget ao al rfl rfl hs.1 (j + 1 + t) j hk (by lia)
          let ck := bo + bl * (j + 1 + t)
          for i in 0...mu do
            have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            have hq' : (ck + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hk
            b[cj + 1 * i] := b[cj + 1 * i] + w * b[ck + 1 * i]
  else mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => n - 1 - j) (fun j t => j + 1 + t)
    (trmmRightLowerW α A) (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v))

public theorem trmmRightLowerData_eq (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    trmmRightLowerData d α A B =
      mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => n - 1 - j) (fun j t => j + 1 + t)
        (trmmRightLowerW α A) (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v)) := by
  unfold trmmRightLowerData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c => rightCol B j (n - 1 - j) (fun t => j + 1 + t)
        (trmmRightLowerW α A j) (fun v => d.mul α A.data[A.off + A.ld * j + j]! * v) c)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      exact iterRange_rightCol_asc B _ _ _ _ (fun j t hj ht => ⟨by lia, by lia⟩) (Nat.le_refl _)
    · intro j _ hj next a h
      rw [hnu] at hj
      have hr : (n.toUSize - 1 - j).toNat = n - 1 - j.toNat := by grind
      rw [Tail.run_forInFrom_modify
          (G := fun _ v => d.mul α A.data[A.off + A.ld * j.toNat + j.toNat]! * v)
          (idx := (Stride.mk (B.off + B.ld * j.toNat) 1).idx)
          (e := fun i => B.off.toUSize + B.ld.toUSize * j + 1 * i)
          (he := fun i _ hi => B.toNat_col_index hs.2.1 (by lia) hj)]
      · rw [Tail.run_forInFrom_unit (F := fun t c =>
            c.modifyAt (Stride.mk (B.off + B.ld * j.toNat) 1).idx 0 m fun i v =>
              v + trmmRightLowerW α A j.toNat t * c[B.off + B.ld * (j.toNat + 1 + t) + i]!)
            (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
        · apply run_congr
          rw [hr, hmu, USize.toNat_zero, addCols_scale B a j.toNat _ (fun t => j.toNat + 1 + t)
            (trmmRightLowerW α A j.toNat) _ (fun t ht => ⟨by lia, by lia⟩)]
        · intro t _ ht next' a' h'
          rw [hr] at ht
          have hk : (j + 1 + t).toNat = j.toNat + 1 + t.toNat := by grind
          have hkn : j.toNat + 1 + t.toNat < n := by lia
          rw [Tail.run_forInFrom_unit (F := fun i c =>
              c.set! ((Stride.mk (B.off + B.ld * j.toNat) 1).idx i)
                (c[(Stride.mk (B.off + B.ld * j.toNat) 1).idx i]! +
                  trmmRightLowerW α A j.toNat t.toNat *
                  c[(Stride.mk (B.off + B.ld * (j.toNat + 1 + t.toNat)) 1).idx i]!))
              (hF := by simp)]
          · apply run_congr
            rw [USize.toNat_zero, hmu,
              iterRange_set!_read _ _ _
                (fun i v w => v + trmmRightLowerW α A j.toNat t.toNat * w)
                (fun i _ hi i' _ hi' e => by
                  simp only [Stride.idx, Nat.one_mul] at e
                  exact col_index_ne hi hi' B.le_ld (show j.toNat ≠ j.toNat + 1 + t.toNat by lia)
                    e)]
            apply modifyAt_congr_fun
            intro i v _ _
            simp only [Stride.idx, Nat.one_mul]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · exact B.toNat_col_index hs.2.1 hi hj
            · have h1 := B.toNat_col_index hs.2.1 hi hj
              have h2 := B.toNat_col_index hs.2.1 hi (j := j + 1 + t) (by rw [hk]; exact hkn)
              simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, hk, Stride.idx, Nat.one_mul,
                trmmRightLowerW]
              rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hj),
                getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hkn),
                getElem!_pos A.data _ (A.index_lt hkn hj)]
      · intro _ _ _ _
        rw [Mat.uget_eq_getElem, getElem_def, getElem!_pos A.data _ (A.index_lt hj hj)]
  · rfl

/-! ## `trmmRight` for the upper triangle -/

/-- The parameters of `rightVal` for `trmmRight .upper`: the columns `k = 0, …, j - 1`. -/
@[expose] public def trmmRightUpperW (α : Float32) (A : Mat n n) (j t : Nat) : Float32 :=
  α * A.data[A.off + A.ld * j + t]!

/-- The array of `trmmRight .upper` for `α ≠ 0`. -/
public def trmmRightUpperData (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    inplace b do
      for p in 0...nu do
        have hj : (nu - 1 - p).toNat = n - 1 - p.toNat := by grind
        have hjn : (nu - 1 - p).toNat < n := by lia
        let cj := bo + bl * (nu - 1 - p)
        let tj := d.mul α (A.uget ao al rfl rfl hs.1 (nu - 1 - p) (nu - 1 - p) hjn hjn)
        for i in 0...mu do
          have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
          b[cj + 1 * i] := tj * b[cj + 1 * i]
        for t in 0...(nu - 1 - p) do
          have hk : t.toNat < n := by grind
          let w := α * A.uget ao al rfl rfl hs.1 t (nu - 1 - p) hk hjn
          let ck := bo + bl * t
          for i in 0...mu do
            have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
            have hq' : (ck + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hk
            b[cj + 1 * i] := b[cj + 1 * i] + w * b[ck + 1 * i]
  else mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => j) (fun _ t => t)
    (trmmRightUpperW α A) (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v))

public theorem trmmRightUpperData_eq (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    trmmRightUpperData d α A B =
      mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => j) (fun _ t => t)
        (trmmRightUpperW α A) (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v)) := by
  unfold trmmRightUpperData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun p c => rightCol B (n - 1 - p) (n - 1 - p) (fun t => t)
        (trmmRightUpperW α A (n - 1 - p))
        (fun v => d.mul α A.data[A.off + A.ld * (n - 1 - p) + (n - 1 - p)]! * v) c)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_rightCol_desc B (fun j => j) _ _
        (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v) (fun j t hj ht => ht)
        (Nat.le_refl _), Nat.sub_self]
    · intro p _ hp next a h
      rw [hnu] at hp
      have hj : (n.toUSize - 1 - p).toNat = n - 1 - p.toNat := by grind
      have hjn : n - 1 - p.toNat < n := by lia
      rw [Tail.run_forInFrom_modify
          (G := fun _ v =>
            d.mul α A.data[A.off + A.ld * (n - 1 - p.toNat) + (n - 1 - p.toNat)]! * v)
          (idx := (Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx)
          (e := fun i => B.off.toUSize + B.ld.toUSize * (n.toUSize - 1 - p) + 1 * i)
          (he := fun i _ hi => by
            rw [B.toNat_col_index hs.2.1 (by lia) (by rw [hj]; exact hjn), hj]; rfl)]
      · rw [Tail.run_forInFrom_unit (F := fun t c =>
            c.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx 0 m fun i v =>
              v + trmmRightUpperW α A (n - 1 - p.toNat) t * c[B.off + B.ld * t + i]!)
            (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
        · apply run_congr
          rw [hj, hmu, USize.toNat_zero, addCols_scale B a (n - 1 - p.toNat) _ (fun t => t)
            (trmmRightUpperW α A (n - 1 - p.toNat)) _ (fun t ht => ⟨by lia, by lia⟩)]
        · intro t _ ht next' a' h'
          rw [hj] at ht
          have hkn : t.toNat < n := by lia
          rw [Tail.run_forInFrom_unit (F := fun i c =>
              c.set! ((Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx i)
                (c[(Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx i]! +
                  trmmRightUpperW α A (n - 1 - p.toNat) t.toNat *
                  c[(Stride.mk (B.off + B.ld * t.toNat) 1).idx i]!))
              (hF := by simp)]
          · apply run_congr
            rw [USize.toNat_zero, hmu,
              iterRange_set!_read _ _ _
                (fun i v w => v + trmmRightUpperW α A (n - 1 - p.toNat) t.toNat * w)
                (fun i _ hi i' _ hi' e => by
                  simp only [Stride.idx, Nat.one_mul] at e
                  exact col_index_ne hi hi' B.le_ld (show n - 1 - p.toNat ≠ t.toNat by lia) e)]
            apply modifyAt_congr_fun
            intro i v _ _
            simp only [Stride.idx, Nat.one_mul]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · rw [B.toNat_col_index hs.2.1 hi (by rw [hj]; exact hjn), hj]
              rfl
            · have h1 := B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - p)
                (by rw [hj]; exact hjn)
              have h2 := B.toNat_col_index hs.2.1 hi (j := t) hkn
              simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, hj, Stride.idx, Nat.one_mul,
                trmmRightUpperW]
              rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hjn),
                getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hkn),
                getElem!_pos A.data _ (A.index_lt hkn hjn)]
      · intro _ _ _ _
        rw [Mat.uget_eq_getElem, getElem_def]
        simp only [hj]
        rw [getElem!_pos A.data _ (A.index_lt hjn hjn)]
  · rfl

/-! ## `trmmRightT` for the upper triangle -/

/-- The parameters of `rightVal` for `trmmRightT .upper`: the columns `k = j + 1, …, n - 1`. -/
@[expose] public def trmmRightTUpperW (α : Float32) (A : Mat n n) (j t : Nat) : Float32 :=
  α * A.data[A.off + A.ld * (j + 1 + t) + j]!

/-- The array of `trmmRightT .upper` for `α ≠ 0`. -/
public def trmmRightTUpperData (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    inplace b do
      for j in 0...nu do
        let cj := bo + bl * j
        let tj := d.mul α (A.uget ao al rfl rfl hs.1 j j (by lia) (by lia))
        for i in 0...mu do
          have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
          b[cj + 1 * i] := scaleUnlessOne tj b[cj + 1 * i]
        for t in 0...(nu - 1 - j) do
          have hk : (j + 1 + t).toNat < n := by grind
          let w := α * A.uget ao al rfl rfl hs.1 j (j + 1 + t) (by lia) hk
          let ck := bo + bl * (j + 1 + t)
          for i in 0...mu do
            have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            have hq' : (ck + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hk
            b[cj + 1 * i] := b[cj + 1 * i] + w * b[ck + 1 * i]
  else mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => n - 1 - j) (fun j t => j + 1 + t)
    (trmmRightTUpperW α A) (fun j v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v))

public theorem trmmRightTUpperData_eq (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    trmmRightTUpperData d α A B =
      mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => n - 1 - j) (fun j t => j + 1 + t)
        (trmmRightTUpperW α A) (fun j v =>
          scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v)) := by
  unfold trmmRightTUpperData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c => rightCol B j (n - 1 - j) (fun t => j + 1 + t)
        (trmmRightTUpperW α A j)
        (fun v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v) c)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      exact iterRange_rightCol_asc B _ _ _ _ (fun j t hj ht => ⟨by lia, by lia⟩) (Nat.le_refl _)
    · intro j _ hj next a h
      rw [hnu] at hj
      have hr : (n.toUSize - 1 - j).toNat = n - 1 - j.toNat := by grind
      rw [Tail.run_forInFrom_modify
          (G := fun _ v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j.toNat + j.toNat]!) v)
          (idx := (Stride.mk (B.off + B.ld * j.toNat) 1).idx)
          (e := fun i => B.off.toUSize + B.ld.toUSize * j + 1 * i)
          (he := fun i _ hi => B.toNat_col_index hs.2.1 (by lia) hj)]
      · rw [Tail.run_forInFrom_unit (F := fun t c =>
            c.modifyAt (Stride.mk (B.off + B.ld * j.toNat) 1).idx 0 m fun i v =>
              v + trmmRightTUpperW α A j.toNat t * c[B.off + B.ld * (j.toNat + 1 + t) + i]!)
            (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
        · apply run_congr
          rw [hr, hmu, USize.toNat_zero, addCols_scale B a j.toNat _ (fun t => j.toNat + 1 + t)
            (trmmRightTUpperW α A j.toNat) _ (fun t ht => ⟨by lia, by lia⟩)]
        · intro t _ ht next' a' h'
          rw [hr] at ht
          have hk : (j + 1 + t).toNat = j.toNat + 1 + t.toNat := by grind
          have hkn : j.toNat + 1 + t.toNat < n := by lia
          rw [Tail.run_forInFrom_unit (F := fun i c =>
              c.set! ((Stride.mk (B.off + B.ld * j.toNat) 1).idx i)
                (c[(Stride.mk (B.off + B.ld * j.toNat) 1).idx i]! +
                  trmmRightTUpperW α A j.toNat t.toNat *
                  c[(Stride.mk (B.off + B.ld * (j.toNat + 1 + t.toNat)) 1).idx i]!))
              (hF := by simp)]
          · apply run_congr
            rw [USize.toNat_zero, hmu,
              iterRange_set!_read _ _ _
                (fun i v w => v + trmmRightTUpperW α A j.toNat t.toNat * w)
                (fun i _ hi i' _ hi' e => by
                  simp only [Stride.idx, Nat.one_mul] at e
                  exact col_index_ne hi hi' B.le_ld (show j.toNat ≠ j.toNat + 1 + t.toNat by lia)
                    e)]
            apply modifyAt_congr_fun
            intro i v _ _
            simp only [Stride.idx, Nat.one_mul]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · exact B.toNat_col_index hs.2.1 hi hj
            · have h1 := B.toNat_col_index hs.2.1 hi hj
              have h2 := B.toNat_col_index hs.2.1 hi (j := j + 1 + t) (by rw [hk]; exact hkn)
              simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, hk, Stride.idx, Nat.one_mul,
                trmmRightTUpperW]
              rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hj),
                getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hkn),
                getElem!_pos A.data _ (A.index_lt hj hkn)]
      · intro _ _ _ _
        rw [Mat.uget_eq_getElem, getElem_def, getElem!_pos A.data _ (A.index_lt hj hj)]
  · rfl

/-! ## `trmmRightT` for the lower triangle -/

/-- The parameters of `rightVal` for `trmmRightT .lower`: the columns `k = j - 1, …, 0`. -/
@[expose] public def trmmRightTLowerW (α : Float32) (A : Mat n n) (j t : Nat) : Float32 :=
  α * A.data[A.off + A.ld * (j - 1 - t) + j]!

/-- The array of `trmmRightT .lower` for `α ≠ 0`. -/
public def trmmRightTLowerData (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    inplace b do
      for p in 0...nu do
        have hj : (nu - 1 - p).toNat = n - 1 - p.toNat := by grind
        have hjn : (nu - 1 - p).toNat < n := by lia
        let cj := bo + bl * (nu - 1 - p)
        let tj := d.mul α (A.uget ao al rfl rfl hs.1 (nu - 1 - p) (nu - 1 - p) hjn hjn)
        for i in 0...mu do
          have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
          b[cj + 1 * i] := scaleUnlessOne tj b[cj + 1 * i]
        for t in 0...(nu - 1 - p) do
          have hk : (nu - 1 - p - 1 - t).toNat < n := by grind
          let w := α * A.uget ao al rfl rfl hs.1 (nu - 1 - p) (nu - 1 - p - 1 - t) hjn hk
          let ck := bo + bl * (nu - 1 - p - 1 - t)
          for i in 0...mu do
            have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
            have hq' : (ck + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hk
            b[cj + 1 * i] := b[cj + 1 * i] + w * b[ck + 1 * i]
  else mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => j) (fun j t => j - 1 - t)
    (trmmRightTLowerW α A) (fun j v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v))

public theorem trmmRightTLowerData_eq (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    trmmRightTLowerData d α A B =
      mapMat B.data B.off B.ld m 0 n (rightVal B (fun j => j) (fun j t => j - 1 - t)
        (trmmRightTLowerW α A) (fun j v =>
          scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v)) := by
  unfold trmmRightTLowerData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun p c =>
        rightCol B (n - 1 - p) (n - 1 - p) (fun t => n - 1 - p - 1 - t)
        (trmmRightTLowerW α A (n - 1 - p))
        (fun v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * (n - 1 - p) + (n - 1 - p)]!) v) c)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_rightCol_desc B (fun j => j) (fun j t => j - 1 - t) (trmmRightTLowerW α A)
        (fun j v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v)
        (fun j t hj ht => by lia)
        (Nat.le_refl _), Nat.sub_self]
    · intro p _ hp next a h
      rw [hnu] at hp
      have hj : (n.toUSize - 1 - p).toNat = n - 1 - p.toNat := by grind
      have hjn : n - 1 - p.toNat < n := by lia
      rw [Tail.run_forInFrom_modify
          (G := fun _ v =>
            scaleUnlessOne
              (d.mul α A.data[A.off + A.ld * (n - 1 - p.toNat) + (n - 1 - p.toNat)]!) v)
          (idx := (Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx)
          (e := fun i => B.off.toUSize + B.ld.toUSize * (n.toUSize - 1 - p) + 1 * i)
          (he := fun i _ hi => by
            rw [B.toNat_col_index hs.2.1 (by lia) (by rw [hj]; exact hjn), hj]; rfl)]
      · rw [Tail.run_forInFrom_unit (F := fun t c =>
            c.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx 0 m fun i v =>
              v + trmmRightTLowerW α A (n - 1 - p.toNat) t *
                c[B.off + B.ld * (n - 1 - p.toNat - 1 - t) + i]!)
            (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
        · apply run_congr
          rw [hj, hmu, USize.toNat_zero,
            addCols_scale B a (n - 1 - p.toNat) _ (fun t => n - 1 - p.toNat - 1 - t)
            (trmmRightTLowerW α A (n - 1 - p.toNat)) _ (fun t ht => ⟨by lia, by lia⟩)]
        · intro t _ ht next' a' h'
          rw [hj] at ht
          have hkn : n - 1 - p.toNat - 1 - t.toNat < n := by lia
          have hk2 : (n.toUSize - 1 - p - 1 - t).toNat = n - 1 - p.toNat - 1 - t.toNat := by grind
          rw [Tail.run_forInFrom_unit (F := fun i c =>
              c.set! ((Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx i)
                (c[(Stride.mk (B.off + B.ld * (n - 1 - p.toNat)) 1).idx i]! +
                  trmmRightTLowerW α A (n - 1 - p.toNat) t.toNat *
                  c[(Stride.mk (B.off + B.ld * (n - 1 - p.toNat - 1 - t.toNat)) 1).idx i]!))
              (hF := by simp)]
          · apply run_congr
            rw [USize.toNat_zero, hmu,
              iterRange_set!_read _ _ _
                (fun i v w => v + trmmRightTLowerW α A (n - 1 - p.toNat) t.toNat * w)
                (fun i _ hi i' _ hi' e => by
                  simp only [Stride.idx, Nat.one_mul] at e
                  exact col_index_ne hi hi' B.le_ld
                    (show n - 1 - p.toNat ≠ n - 1 - p.toNat - 1 - t.toNat by lia) e)]
            apply modifyAt_congr_fun
            intro i v _ _
            simp only [Stride.idx, Nat.one_mul]
          · intro i _ hi next'' a'' h''
            rw [hmu] at hi
            simp only [Tail.run_readThen, Tail.run_writeThen]
            apply run_set_eq_set!
            · rw [B.toNat_col_index hs.2.1 hi (by rw [hj]; exact hjn), hj]
              rfl
            · have h1 := B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - p)
                (by rw [hj]; exact hjn)
              have h2 := B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - p - 1 - t)
                (by rw [hk2]; exact hkn)
              simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, hj, hk2, Stride.idx, Nat.one_mul,
                trmmRightTLowerW]
              rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hjn),
                getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hkn),
                getElem!_pos A.data _ (A.index_lt hjn hkn)]
      · intro _ _ _ _
        rw [Mat.uget_eq_getElem, getElem_def]
        simp only [hj]
        rw [getElem!_pos A.data _ (A.index_lt hjn hjn)]
  · rfl


/-! ## The public products -/

/--
The value of element `(i, j)` of `trmmRight uplo d α A B` for `α ≠ 0`, from its old value.
-/
@[expose] public def trmmRightVal (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : Nat → Nat → Float32 → Float32 :=
  match uplo with
  | .upper => rightVal B (fun j => j) (fun _ t => t) (trmmRightUpperW α A)
      (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v)
  | .lower => rightVal B (fun j => n - 1 - j) (fun j t => j + 1 + t) (trmmRightLowerW α A)
      (fun j v => d.mul α A.data[A.off + A.ld * j + j]! * v)

/--
The value of element `(i, j)` of `trmmRightT uplo d α A B` for `α ≠ 0`, from its old value.
-/
@[expose] public def trmmRightTVal (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : Nat → Nat → Float32 → Float32 :=
  match uplo with
  | .upper => rightVal B (fun j => n - 1 - j) (fun j t => j + 1 + t) (trmmRightTUpperW α A)
      (fun j v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v)
  | .lower => rightVal B (fun j => j) (fun j t => j - 1 - t) (trmmRightTLowerW α A)
      (fun j v => scaleUnlessOne (d.mul α A.data[A.off + A.ld * j + j]!) v)

/-- The array of `trmmRight`. -/
public def trmmRightData (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if α == 0 then B.scalBetaData 0
  else match uplo with
    | .upper => trmmRightUpperData d α A B
    | .lower => trmmRightLowerData d α A B

/-- The array of `trmmRightT`. -/
public def trmmRightTData (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if α == 0 then B.scalBetaData 0
  else match uplo with
    | .upper => trmmRightTUpperData d α A B
    | .lower => trmmRightTLowerData d α A B

private theorem scalBetaData_zero_eq (B : Mat m n) :
    B.scalBetaData 0 = mapMat B.data B.off B.ld m 0 n fun _ _ _ => 0 := by
  rw [scalBetaData_eq]
  apply mapMat_congr
  intro i j v _ _ _
  simp [betaMul, show ((0 : Float32) == 0) = true from rfl]

public theorem trmmRightData_eq (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) :
    trmmRightData uplo d α A B = mapMat B.data B.off B.ld m 0 n fun i j v =>
      if α == 0 then 0 else trmmRightVal uplo d α A B i j v := by
  unfold trmmRightData
  cases hα : α == 0
  · cases uplo
    · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightUpperData_eq, trmmRightVal]
    · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightLowerData_eq, trmmRightVal]
  · simp only [↓reduceIte, scalBetaData_zero_eq]

public theorem trmmRightTData_eq (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) :
    trmmRightTData uplo d α A B = mapMat B.data B.off B.ld m 0 n fun i j v =>
      if α == 0 then 0 else trmmRightTVal uplo d α A B i j v := by
  unfold trmmRightTData
  cases hα : α == 0
  · cases uplo
    · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightTUpperData_eq, trmmRightTVal]
    · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightTLowerData_eq, trmmRightTVal]
  · simp only [↓reduceIte, scalBetaData_zero_eq]

/--
`trmmRight uplo d α A B` is `α * B * A` for the triangle `uplo` of `A`, with a unit diagonal if
`d` is `.unit`, over `B`, by the loops of the reference BLAS for `SIDE = 'R'` and `TRANSA = 'N'`.
It updates `B` in place when its array is not shared, and leaves the elements of the array outside
`B` unchanged. As in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when
`α = 0`, and reads only the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`.
-/
@[expose] public def trmmRight (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Mat m n where
  data := trmmRightData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trmmRightData_eq, size_mapMat]; exact B.bound

/--
`trmmRightT uplo d α A B` is `α * B * Aᵀ` for the triangle `uplo` of `A`, with a unit diagonal
if `d` is `.unit`, over `B`, by the loops of the reference BLAS for `SIDE = 'R'` and `TRANSA = 'T'`.
It updates `B` in place when its array is not shared, and leaves the elements of the array outside
`B` unchanged. As in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when
`α = 0`, reads only the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`, and
skips the scaling of a column when its factor is `1`.
-/
@[expose] public def trmmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : Mat m n where
  data := trmmRightTData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trmmRightTData_eq, size_mapMat]; exact B.bound

public theorem data_trmmRight (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    (trmmRight uplo d α A B).data = mapMat B.data B.off B.ld m 0 n fun i j v =>
      if α == 0 then 0 else trmmRightVal uplo d α A B i j v :=
  trmmRightData_eq uplo d α A B

@[simp] public theorem off_trmmRight (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : (trmmRight uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trmmRight (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : (trmmRight uplo d α A B).ld = B.ld := rfl

public theorem data_trmmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) :
    (trmmRightT uplo d α A B).data = mapMat B.data B.off B.ld m 0 n fun i j v =>
      if α == 0 then 0 else trmmRightTVal uplo d α A B i j v :=
  trmmRightTData_eq uplo d α A B

@[simp] public theorem off_trmmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : (trmmRightT uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trmmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : (trmmRightT uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trmmRight uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trmmRight (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRight uplo d α A B)[(i, j)] =
      if α == 0 then 0 else trmmRightVal uplo d α A B i j B[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_trmmRight uplo d α A B) rfl rfl i j h]

/-- Element `(i, j)` of `trmmRightT uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trmmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRightT uplo d α A B)[(i, j)] =
      if α == 0 then 0 else trmmRightTVal uplo d α A B i j B[(i, j)] := by
  rw [getElem_of_data_eq_mapMat _ (data_trmmRightT uplo d α A B) rfl rfl i j h]

/--
Element `(i, j)` of `trmmRight .upper d α A B` is `0` when `α = 0`, and otherwise
`α * A[j, j] * B[i, j]` (`α * B[i, j]` for a unit diagonal) plus the terms
`α * A[k, j] * B[i, k]` for `k = 0, …, j - 1`.
-/
public theorem getElem_trmmRight_upper (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRight .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else Nat.fold j (fun k _ s =>
          s + α * A[(k, j)]'⟨by lia, h.2⟩ * B[(i, k)]'⟨h.1, by lia⟩)
        (d.mul α A[(j, j)] * B[(i, j)]) := by
  rw [getElem_trmmRight _ _ _ _ _ _ _ h]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightVal, rightVal, trmmRightUpperW]
    rw [getElem!_pos A.data (A.off + A.ld * j + j) (A.index_lt h.2 h.2)]
    congr 1
    funext k hk s
    rw [getElem!_pos A.data (A.off + A.ld * j + k) (A.index_lt (by lia) h.2),
      getElem!_pos B.data (B.off + B.ld * k + i) (B.index_lt h.1 (by lia))]
    rfl
  · simp only [↓reduceIte]

/--
Element `(i, j)` of `trmmRight .lower d α A B` is `0` when `α = 0`, and otherwise
`α * A[j, j] * B[i, j]` (`α * B[i, j]` for a unit diagonal) plus the terms
`α * A[k, j] * B[i, k]` for `k = j + 1, …, n - 1`.
-/
public theorem getElem_trmmRight_lower (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRight .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else Nat.fold (n - 1 - j) (fun t _ s =>
          s + α * A[(j + 1 + t, j)]'⟨by lia, h.2⟩ * B[(i, j + 1 + t)]'⟨h.1, by lia⟩)
        (d.mul α A[(j, j)] * B[(i, j)]) := by
  rw [getElem_trmmRight _ _ _ _ _ _ _ h]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightVal, rightVal, trmmRightLowerW]
    rw [getElem!_pos A.data (A.off + A.ld * j + j) (A.index_lt h.2 h.2)]
    congr 1
    funext t ht s
    rw [getElem!_pos A.data (A.off + A.ld * j + (j + 1 + t)) (A.index_lt (by lia) h.2),
      getElem!_pos B.data (B.off + B.ld * (j + 1 + t) + i) (B.index_lt h.1 (by lia))]
    rfl
  · simp only [↓reduceIte]

/--
Element `(i, j)` of `trmmRightT .upper d α A B` is `0` when `α = 0`, and otherwise
`α * A[j, j] * B[i, j]` (`B[i, j]` when that factor is `1`, and `α * B[i, j]` for a unit
diagonal) plus the terms `α * A[j, k] * B[i, k]` for `k = j + 1, …, n - 1`.
-/
public theorem getElem_trmmRightT_upper (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRightT .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else Nat.fold (n - 1 - j) (fun t _ s =>
          s + α * A[(j, j + 1 + t)]'⟨h.2, by lia⟩ * B[(i, j + 1 + t)]'⟨h.1, by lia⟩)
        (scaleUnlessOne (d.mul α A[(j, j)]) B[(i, j)]) := by
  rw [getElem_trmmRightT _ _ _ _ _ _ _ h]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightTVal, rightVal, trmmRightTUpperW]
    rw [getElem!_pos A.data (A.off + A.ld * j + j) (A.index_lt h.2 h.2)]
    congr 1
    funext t ht s
    rw [getElem!_pos A.data (A.off + A.ld * (j + 1 + t) + j) (A.index_lt h.2 (by lia)),
      getElem!_pos B.data (B.off + B.ld * (j + 1 + t) + i) (B.index_lt h.1 (by lia))]
    rfl
  · simp only [↓reduceIte]

/--
Element `(i, j)` of `trmmRightT .lower d α A B` is `0` when `α = 0`, and otherwise
`α * A[j, j] * B[i, j]` (`B[i, j]` when that factor is `1`, and `α * B[i, j]` for a unit
diagonal) plus the terms `α * A[j, k] * B[i, k]` for `k = j - 1, …, 0`.
-/
public theorem getElem_trmmRightT_lower (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRightT .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else Nat.fold j (fun t _ s =>
          s + α * A[(j, j - 1 - t)]'⟨h.2, by lia⟩ * B[(i, j - 1 - t)]'⟨h.1, by lia⟩)
        (scaleUnlessOne (d.mul α A[(j, j)]) B[(i, j)]) := by
  rw [getElem_trmmRightT _ _ _ _ _ _ _ h]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmmRightTVal, rightVal, trmmRightTLowerW]
    rw [getElem!_pos A.data (A.off + A.ld * j + j) (A.index_lt h.2 h.2)]
    congr 1
    funext t ht s
    rw [getElem!_pos A.data (A.off + A.ld * (j - 1 - t) + j) (A.index_lt h.2 (by lia)),
      getElem!_pos B.data (B.off + B.ld * (j - 1 - t) + i) (B.index_lt h.1 (by lia))]
    rfl
  · simp only [↓reduceIte]

end Mat

end BLAS.Float32
