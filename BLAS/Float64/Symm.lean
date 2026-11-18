/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Symv
public import BLAS.Float64.Gemm
import all BLAS.Internal

/-!
# Symmetric matrix-matrix product

`Mat.symm uplo α A B β C` computes `α * A * B + β * C` and `Mat.symmRight uplo α A B β C`
computes `α * B * A + β * C`, for a symmetric matrix `A` stored in its triangle `uplo`, over `C`,
by the loops of the reference BLAS. As there, they only scale `C` by `β` when `α = 0` (setting it
to `0` when `β = 0`), and otherwise scale each element of `C` by `β` when they first reach it,
without reading it when `β = 0`.

`symm` computes each column of `C` from the same column of `B`, by loops like those of `symv`: for
each row `p` of the triangle, it adds `α * B[p, j]` times column `p` of `A` to the elements of the
column that the loops have reached, and sets element `p` from `β * C[p, j]`, the diagonal term,
and `α` times the dot product of column `p` of `A` with the elements of `B[:, j]` that it adds to.
`symmRight` adds the columns of `B` to each column of `C`, scaled by `α` times the elements of `A`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {m n : Nat}

/-! ## The loops -/

/-- A loop whose step `i` adds `g i` to its variable and maps its array by `F i`. -/
private theorem iterRange_pair (g : Nat → Float) (F : Nat → Float64Array → Float64Array)
    (k : Nat) (s : Float) (a : Float64Array) :
    iterRange (fun i p => (p.1 + g i, F i p.2)) 0 k (s, a) =
      (Nat.fold k (fun i _ s => s + g i) s, iterRange F 0 k a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, iterRange_succ _ (Nat.zero_le _),
      Nat.fold_succ]

/-- Steps that each write `G i c[idx i]!` at `idx i` are a `modifyAt`. -/
private theorem iterRange_set!_self (a : Float64Array) (idx : Nat → Nat)
    (G : Nat → Float → Float) {lo hi : Nat} :
    iterRange (fun i c => c.set! (idx i) (G i c[idx i]!)) lo hi a = a.modifyAt idx lo hi G := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), modifyAt_of_lt _ _ (by lia), ih _ (by lia)]

private theorem toNat_add_of_lt {cb k : USize} {m size : Nat} (hk : k.toNat < m)
    (hcb : cb.toNat + m ≤ size) (hcs : size < USize.size) :
    (cb + k).toNat = cb.toNat + k.toNat := by
  grind

/-- The value that the reference `dsymm` gives an element `v` of `C` with the term `u`. -/
@[expose] public def symmDiag (β v u : Float) : Float := if β == 0 then u else β * v + u

/-! ## The upper triangle, on the left -/

/-- The dot product of column `p` of the upper triangle, above the diagonal, with `B[:, j]`. -/
@[expose] public def symmUpperDot (A : Mat m m) (B : Mat m n) (j p : Nat) : Float :=
  Nat.fold p (fun k _ s => s + B.data[B.off + B.ld * j + k]! * A.data[A.off + A.ld * p + k]!) 0

/--
The step `p` of column `j` of `symm .upper`, on the array `c` with column `j` of `C` at `cb`: add
`α * B[p, j]` times column `p` of `A` to the elements above `p`, and set element `p`.
-/
@[expose] public def symmUpperStep (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (cb j p : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt (fun i => cb + i) 0 (p + 1) fun k v =>
    if k = p then
      symmDiag β v (α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + p]!) +
        α * symmUpperDot A B j p
    else v + α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + k]!

/-- The loops of column `j` of `symm .upper`, on the array `c` with column `j` of `C` at `cb`. -/
public def symmUpperCol (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) : {c' : Float64Array // c'.size = c.size} :=
  have hmu : m.toUSize.toNat = m := by grind
  let bo := B.off.toUSize
  let bl := B.ld.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  inplace c do
    for p in 0...m.toUSize do
      have hpm : p.toNat < m := by lia
      let t := α * B.uget bo bl rfl rfl hs.2 p j hpm hj
      for k in 0...p with (s := 0) do
        have hk : k.toNat < m := Nat.lt_trans (by assumption) hpm
        have hq : (cb + k).toNat < c.size := by rw [toNat_add_of_lt hk hcb hcs]; lia
        let akp := A.uget ao al rfl rfl hs.1 k p hk hpm
        c[cb + k] := c[cb + k] + t * akp
        s := s + B.uget bo bl rfl rfl hs.2 k j hk hj * akp
      have hq : (cb + p).toNat < c.size := by rw [toNat_add_of_lt hpm hcb hcs]; lia
      c[cb + p] := symmDiag β c[cb + p] (t * A.uget ao al rfl rfl hs.1 p p hpm hpm) + α * s
  then fun _ c' h => ⟨c', h⟩


/-- The step `p` of `symm .upper` updates the elements above `p`, and then element `p`. -/
private theorem symmUpperStep_eq (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (cb j p : Nat) (c : Float64Array) :
    symmUpperStep α A B β cb j p c =
      (c.modifyAt (fun i => cb + i) 0 p fun k v =>
        v + α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + k]!).set!
        (cb + p) (symmDiag β c[cb + p]!
          (α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + p]!) +
          α * symmUpperDot A B j p) := by
  rw [symmUpperStep, modifyAt_succ _ _ (Nat.zero_le _)]
  simp only [↓reduceIte]
  rw [modifyAt_congr_fun _ _ (g' := fun k v =>
      v + α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + k]!)
    (fun i v _ hi => ite_eq_right (by lia))]
  rw [getElem!_modifyAt_of_ne _ _ (p := cb + p) _ (fun i _ hi => by lia)]

public theorem symmUpperCol_eq (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) :
    (symmUpperCol α A B β hs cb j hj c hcb hcs).1 =
      iterRange (symmUpperStep α A B β cb.toNat j.toNat) 0 m c := by
  have hmu : m.toUSize.toNat = m := by grind
  unfold symmUpperCol
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := symmUpperStep α A B β cb.toNat j.toNat)
    (hF := fun _ _ => by unfold symmUpperStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
  · intro p _ hp next a h
    rw [hmu] at hp
    have hq : (cb + p).toNat = cb.toNat + p.toNat := toNat_add_of_lt hp hcb hcs
    rw [Tail.run_forInFrom (f := fun k q =>
        (q.1 + B.data[B.off + B.ld * j.toNat + k]! * A.data[A.off + A.ld * p.toNat + k]!,
          q.2.set! (cb.toNat + k) (q.2[cb.toNat + k]! +
            α * B.data[B.off + B.ld * j.toNat + p.toNat]! * A.data[A.off + A.ld * p.toNat + k]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun k => B.data[B.off + B.ld * j.toNat + k]! * A.data[A.off + A.ld * p.toNat + k]!)
        (fun k c => c.set! (cb.toNat + k) (c[cb.toNat + k]! +
          α * B.data[B.off + B.ld * j.toNat + p.toNat]! * A.data[A.off + A.ld * p.toNat + k]!))
        p.toNat 0 a
      rw [iterRange_set!_self a (fun k => cb.toNat + k) (fun k v =>
        v + α * B.data[B.off + B.ld * j.toNat + p.toNat]! *
          A.data[A.off + A.ld * p.toNat + k]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_readThen, Tail.run_writeThen]
      apply run_congr
      simp only [hpair, uget_eq_getElem, getElem_def, hq]
      rw [set_eq_set!, symmUpperStep_eq]
      congr 1
      simp only [getElem_eq_getElem!]
      rw [getElem!_modifyAt_of_ne _ _ (p := cb.toNat + p.toNat) _ (fun i _ hi => by lia)]
      rfl
    · intro k _ hk next' s a' h'
      have hkm : k.toNat < m := by lia
      have hq' : (cb + k).toNat = cb.toNat + k.toNat := toNat_add_of_lt hkm hcb hcs
      simp only [Tail.run_readThen, Tail.run_writeThen, uget_eq_getElem, getElem_def, hq']
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/-- The value of element `i` of column `j` of `symm .upper`, from its old value `v`. -/
@[expose] public def symmUpperAt (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (j i : Nat) (v : Float) : Float :=
  Nat.fold (m - 1 - i) (fun t _ s =>
      s + α * B.data[B.off + B.ld * j + (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
    (symmDiag β v (α * B.data[B.off + B.ld * j + i]! * A.data[A.off + A.ld * i + i]!) +
      α * symmUpperDot A B j i)

/--
After the steps `p < q`, the elements `i < q` have their diagonal term, their dot product and the
terms `p < q`, and the others are unchanged.
-/
private theorem iterRange_symmUpperStep (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (cb j : Nat) (c : Float64Array) {q : Nat} (hq : q ≤ m) :
    iterRange (symmUpperStep α A B β cb j) 0 q c = c.modifyAt (fun i => cb + i) 0 m fun i v =>
      if i < q then Nat.fold (q - 1 - i) (fun t _ s =>
          s + α * B.data[B.off + B.ld * j + (i + 1 + t)]! *
            A.data[A.off + A.ld * (i + 1 + t) + i]!)
        (symmDiag β v (α * B.data[B.off + B.ld * j + i]! * A.data[A.off + A.ld * i + i]!) +
          α * symmUpperDot A B j i)
      else v := by
  have hinj : ∀ i, 0 ≤ i → i < m → ∀ j, 0 ≤ j → j < m → cb + i = cb + j → i = j :=
    fun _ _ _ _ _ _ e => by lia
  induction q with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ q ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), symmUpperStep,
      modifyAt_widen (lo := 0) (hi := q + 1) (lo' := 0) (hi' := m) _ _ _ (Nat.le_refl _)
        (Nat.zero_le _) (by lia), modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < q
    · simp only [h₁, show i < q + 1 by lia, show i ≠ q by lia, and_self, ite_true, ite_false,
        Nat.zero_le]
      rw [Nat.fold_congr (show q + 1 - 1 - i = (q - 1 - i) + 1 by lia), Nat.fold_succ,
        show i + 1 + (q - 1 - i) = q by lia]
    · by_cases h₂ : i = q
      · subst h₂
        simp only [Nat.lt_irrefl, Nat.lt_succ_self, ite_true, ite_false, Nat.zero_le, and_self]
        rw [show i + 1 - 1 - i = 0 by lia, Nat.fold_zero]
      · simp [h₁, show ¬i < q + 1 by lia]

/-- The loops of column `j` of `symm .upper` map the column by `symmUpperAt`. -/
public theorem symmUpperCol_eq_modifyAt (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) :
    (symmUpperCol α A B β hs cb j hj c hcb hcs).1 =
      c.modifyAt (fun i => cb.toNat + i) 0 m (symmUpperAt α A B β j.toNat) := by
  rw [symmUpperCol_eq, iterRange_symmUpperStep _ _ _ _ _ _ _ (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [hi, ite_true, symmUpperAt]


/-! ## The lower triangle, on the left -/

private theorem set!_comm' (a : Float64Array) {p q : Nat} (v w : Float) (h : p ≠ q) :
    (a.set! p v).set! q w = (a.set! q w).set! p v := by
  apply ext_getElem?; intro r
  simp only [getElem?_set!, size_set!]
  by_cases hp : p = r <;> by_cases hq : q = r
  · exact absurd (hp.trans hq.symm) h
  all_goals simp [hp, hq]

private theorem getElem!_set!_of_ne' (a : Float64Array) {p q : Nat} (v : Float) (h : p ≠ q) :
    (a.set! p v)[q]! = a[q]! := by
  by_cases hq : q < a.size
  · rw [getElem!_set!_of_lt _ _ _ hq, ite_eq_right h]
  · rw [getElem!_neg _ q (by simpa using hq), getElem!_neg a q hq]

/-- A write at an index of no step commutes with `modifyAt`. -/
private theorem modifyAt_set!' (a : Float64Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float → Float) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) (v : Float) :
    (a.set! p v).modifyAt idx lo hi g = (a.modifyAt idx lo hi g).set! p v := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [modifyAt_of_le _ _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    have hne := hp lo (Nat.le_refl _) (by lia)
    rw [modifyAt_of_lt (a.set! p v) idx (lo := lo) (hi := hi) (by lia) g,
      modifyAt_of_lt a idx (lo := lo) (hi := hi) (by lia) g, getElem!_set!_of_ne' _ _ hne.symm,
      set!_comm' _ _ _ hne.symm, ih _ (fun i h₁ h₂ => hp i (by lia) h₂) (by lia)]

/-- `modifyAt` on the elements from `k` of a column is `modifyAt` on the column from `k`. -/
private theorem modifyAt_col_shift (a : Float64Array) (cb k h : Nat) (g : Nat → Float → Float) :
    a.modifyAt (fun l => cb + (k + l)) 0 h g =
      a.modifyAt (fun i => cb + i) k (k + h) fun i v => g (i - k) v := by
  have e₁ : a.modifyAt (fun l => cb + (k + l)) 0 h g =
      a.modifyAt ((Stride.mk cb 1).shift k).idx 0 h g :=
    modifyAt_congr _ (fun l _ _ => by simp [Stride.idx, Nat.add_assoc]) (fun _ _ _ => rfl)
  have e₂ : a.modifyAt (Stride.mk cb 1).idx k (k + h) (fun i v => g (i - k) v) =
      a.modifyAt (fun i => cb + i) k (k + h) fun i v => g (i - k) v :=
    modifyAt_congr _ (fun l _ _ => by simp [Stride.idx]) (fun _ _ _ => rfl)
  rw [e₁, modifyAt_shift, e₂]

/-- The dot product of column `p` of the lower triangle, below the diagonal, with `B[:, j]`. -/
@[expose] public def symmLowerDot (A : Mat m m) (B : Mat m n) (j p : Nat) : Float :=
  Nat.fold (m - 1 - p) (fun t _ s =>
    s + B.data[B.off + B.ld * j + (p + 1 + t)]! * A.data[A.off + A.ld * p + (p + 1 + t)]!) 0

/--
The step `p` of column `j` of `symm .lower`, on the array `c` with column `j` of `C` at `cb`: add
`α * B[p, j]` times column `p` of `A` to the elements below `p`, and set element `p`.
-/
@[expose] public def symmLowerStep (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (cb j p : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt (fun i => cb + i) p m fun k v =>
    if k = p then
      symmDiag β v (α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + p]!) +
        α * symmLowerDot A B j p
    else v + α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + k]!

/-- The step `p` of `symm .lower` updates the elements below `p`, and then element `p`. -/
private theorem symmLowerStep_eq (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (cb j : Nat) {p : Nat} (hp : p < m) (c : Float64Array) :
    symmLowerStep α A B β cb j p c =
      (c.modifyAt (fun l => cb + (p + 1 + l)) 0 (m - 1 - p) fun l v =>
        v + α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + (p + 1 + l)]!).set!
        (cb + p) (symmDiag β c[cb + p]!
          (α * B.data[B.off + B.ld * j + p]! * A.data[A.off + A.ld * p + p]!) +
          α * symmLowerDot A B j p) := by
  rw [symmLowerStep, modifyAt_of_lt _ _ hp]
  simp only [↓reduceIte]
  rw [modifyAt_set!' _ _ _ (fun i h₁ _ => by lia), modifyAt_col_shift,
    show p + 1 + (m - 1 - p) = m by lia]
  congr 1
  apply modifyAt_congr_fun
  intro i v h₁ _
  rw [ite_eq_right (by lia), show p + 1 + (i - (p + 1)) = i by lia]

/-- The loops of column `j` of `symm .lower`, on the array `c` with column `j` of `C` at `cb`. -/
public def symmLowerCol (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) : {c' : Float64Array // c'.size = c.size} :=
  have hmu : m.toUSize.toNat = m := by grind
  let mu := m.toUSize
  let bo := B.off.toUSize
  let bl := B.ld.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  inplace c do
    for q in 0...mu do
      have hpm : (mu - 1 - q).toNat < m := by grind
      let t := α * B.uget bo bl rfl rfl hs.2 (mu - 1 - q) j hpm hj
      have hq : (cb + (mu - 1 - q)).toNat < c.size := by rw [toNat_add_of_lt hpm hcb hcs]; lia
      let v := c[cb + (mu - 1 - q)]
      for l in 0...q with (s := 0) do
        have hk : (mu - 1 - q + 1 + l).toNat < m := by grind
        have hq' : (cb + (mu - 1 - q + 1 + l)).toNat < c.size := by
          rw [toNat_add_of_lt hk hcb hcs]; lia
        let akp := A.uget ao al rfl rfl hs.1 (mu - 1 - q + 1 + l) (mu - 1 - q) hk hpm
        c[cb + (mu - 1 - q + 1 + l)] := c[cb + (mu - 1 - q + 1 + l)] + t * akp
        s := s + B.uget bo bl rfl rfl hs.2 (mu - 1 - q + 1 + l) j hk hj * akp
      c[cb + (mu - 1 - q)] :=
        symmDiag β v (t * A.uget ao al rfl rfl hs.1 (mu - 1 - q) (mu - 1 - q) hpm hpm) + α * s
  then fun _ c' h => ⟨c', h⟩

public theorem symmLowerCol_eq (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) :
    (symmLowerCol α A B β hs cb j hj c hcb hcs).1 =
      iterRange (fun q => symmLowerStep α A B β cb.toNat j.toNat (m - 1 - q)) 0 m c := by
  have hmu : m.toUSize.toNat = m := by grind
  unfold symmLowerCol
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun q => symmLowerStep α A B β cb.toNat j.toNat (m - 1 - q))
    (hF := fun _ _ => by unfold symmLowerStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
  · intro q _ hq0 next a h
    rw [hmu] at hq0
    have hp : (m.toUSize - 1 - q).toNat = m - 1 - q.toNat := by grind
    have hpm : m - 1 - q.toNat < m := by lia
    have hq : (cb + (m.toUSize - 1 - q)).toNat = cb.toNat + (m - 1 - q.toNat) := by
      rw [toNat_add_of_lt (by rw [hp]; exact hpm) hcb hcs, hp]
    simp only [Tail.run_readThen]
    rw [Tail.run_forInFrom (f := fun l r =>
        (r.1 + B.data[B.off + B.ld * j.toNat + (m - 1 - q.toNat + 1 + l)]! *
            A.data[A.off + A.ld * (m - 1 - q.toNat) + (m - 1 - q.toNat + 1 + l)]!,
          r.2.set! (cb.toNat + (m - 1 - q.toNat + 1 + l))
            (r.2[cb.toNat + (m - 1 - q.toNat + 1 + l)]! +
              α * B.data[B.off + B.ld * j.toNat + (m - 1 - q.toNat)]! *
                A.data[A.off + A.ld * (m - 1 - q.toNat) + (m - 1 - q.toNat + 1 + l)]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun l => B.data[B.off + B.ld * j.toNat + (m - 1 - q.toNat + 1 + l)]! *
          A.data[A.off + A.ld * (m - 1 - q.toNat) + (m - 1 - q.toNat + 1 + l)]!)
        (fun l c => c.set! (cb.toNat + (m - 1 - q.toNat + 1 + l))
          (c[cb.toNat + (m - 1 - q.toNat + 1 + l)]! +
            α * B.data[B.off + B.ld * j.toNat + (m - 1 - q.toNat)]! *
              A.data[A.off + A.ld * (m - 1 - q.toNat) + (m - 1 - q.toNat + 1 + l)]!))
        q.toNat 0 a
      rw [iterRange_set!_self a (fun l => cb.toNat + (m - 1 - q.toNat + 1 + l)) (fun l v =>
        v + α * B.data[B.off + B.ld * j.toNat + (m - 1 - q.toNat)]! *
          A.data[A.off + A.ld * (m - 1 - q.toNat) + (m - 1 - q.toNat + 1 + l)]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_writeThen]
      apply run_congr
      simp only [hpair, uget_eq_getElem, getElem_def, hq, hp]
      rw [set_eq_set!, symmLowerStep_eq _ _ _ _ _ _ hpm,
        show m - 1 - (m - 1 - q.toNat) = q.toNat by lia]
      congr 1
      simp only [getElem_eq_getElem!, symmLowerDot]
      rw [show m - 1 - (m - 1 - q.toNat) = q.toNat by lia]
    · intro l _ hl next' s a' h'
      have hkm : m - 1 - q.toNat + 1 + l.toNat < m := by lia
      have hk' : (m.toUSize - 1 - q + 1 + l).toNat = m - 1 - q.toNat + 1 + l.toNat := by grind
      have hq' : (cb + (m.toUSize - 1 - q + 1 + l)).toNat =
          cb.toNat + (m - 1 - q.toNat + 1 + l.toNat) := by
        rw [toNat_add_of_lt (by rw [hk']; exact hkm) hcb hcs, hk']
      simp only [Tail.run_readThen, Tail.run_writeThen, uget_eq_getElem, getElem_def, hq', hk', hp]
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _


/-- The value of element `i` of column `j` of `symm .lower`, from its old value `v`. -/
@[expose] public def symmLowerAt (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (j i : Nat) (v : Float) : Float :=
  Nat.fold i (fun t _ s =>
      s + α * B.data[B.off + B.ld * j + (i - 1 - t)]! * A.data[A.off + A.ld * (i - 1 - t) + i]!)
    (symmDiag β v (α * B.data[B.off + B.ld * j + i]! * A.data[A.off + A.ld * i + i]!) +
      α * symmLowerDot A B j i)

/--
After the steps for the rows `p ≥ m - q`, from the last, these rows have their diagonal term, their
dot product and the terms of the rows from `m - q` that are above them, and the others are
unchanged.
-/
private theorem iterRange_symmLowerStep (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (cb j : Nat) (c : Float64Array) {q : Nat} (hq : q ≤ m) :
    iterRange (fun q => symmLowerStep α A B β cb j (m - 1 - q)) 0 q c =
      c.modifyAt (fun i => cb + i) 0 m fun i v =>
        if m - q ≤ i then Nat.fold (i - (m - q)) (fun t _ s =>
            s + α * B.data[B.off + B.ld * j + (i - 1 - t)]! *
              A.data[A.off + A.ld * (i - 1 - t) + i]!)
          (symmDiag β v (α * B.data[B.off + B.ld * j + i]! * A.data[A.off + A.ld * i + i]!) +
            α * symmLowerDot A B j i)
        else v := by
  have hinj : ∀ i, 0 ≤ i → i < m → ∀ j, 0 ≤ j → j < m → cb + i = cb + j → i = j :=
    fun _ _ _ _ _ _ e => by lia
  induction q with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬m ≤ i by lia]
  | succ q ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), symmLowerStep,
      modifyAt_widen (lo := m - 1 - q) (hi := m) (lo' := 0) (hi' := m) _ _ _ (Nat.zero_le _)
        (by lia) (Nat.le_refl _), modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : m - q ≤ i
    · simp only [h₁, show m - (q + 1) ≤ i by lia, show m - 1 - q ≤ i by lia, hi, and_self,
        show i ≠ m - 1 - q by lia, ite_true, ite_false]
      rw [Nat.fold_congr (show i - (m - (q + 1)) = (i - (m - q)) + 1 by lia), Nat.fold_succ,
        show i - 1 - (i - (m - q)) = m - 1 - q by lia]
    · by_cases h₂ : i = m - 1 - q
      · subst h₂
        simp only [h₁, show m - (q + 1) ≤ m - 1 - q by lia, Nat.le_refl, hi, and_self, ite_true,
          ite_false]
        rw [show m - 1 - q - (m - (q + 1)) = 0 by lia, Nat.fold_zero]
      · simp [h₁, show ¬m - (q + 1) ≤ i by lia, show ¬m - 1 - q ≤ i by lia]

/-- The loops of column `j` of `symm .lower` map the column by `symmLowerAt`. -/
public theorem symmLowerCol_eq_modifyAt (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) :
    (symmLowerCol α A B β hs cb j hj c hcb hcs).1 =
      c.modifyAt (fun i => cb.toNat + i) 0 m (symmLowerAt α A B β j.toNat) := by
  rw [symmLowerCol_eq, iterRange_symmLowerStep _ _ _ _ _ _ _ (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [Nat.sub_self, Nat.zero_le, ite_true, symmLowerAt]
  rw [Nat.sub_self, Nat.sub_zero]


/-! ## `symm` -/

/-- The value of element `i` of column `j` of the product on the left, from its old value. -/
@[expose] public def symmAt (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float) :
    Nat → Nat → Float → Float :=
  match uplo with
  | .upper => symmUpperAt α A B β
  | .lower => symmLowerAt α A B β

/-- The offset of column `j` of `C` as a `USize`, in an array of `USize` size. -/
private theorem toNat_col_base (C : Mat m n) (hs : C.data.size < USize.size) (hm : 0 < m)
    {j : Nat} (hj : j < n) (hju : j < USize.size) :
    (C.off.toUSize + C.ld.toUSize * j.toUSize).toNat = C.off + C.ld * j := by
  have := C.col_le hm hj
  have hj' : j.toUSize.toNat = j := by grind
  have := C.toNat_index hs (i := 0) (j := j.toUSize) hm (by rw [hj']; exact hj)
  grind

/-- The loops of `symm uplo` over the columns from `j` of the array `c` of `C`. -/
public def symmCols (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) (hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧
      C.data.size < USize.size ∧ n < USize.size ∧ 0 < m)
    (co cl : USize) (hco : C.off.toUSize = co) (hcl : C.ld.toUSize = cl) (j : Nat)
    (c : Float64Array) (hc : c.size = C.data.size) : Float64Array :=
  if hj : j < n then
    have hju : j.toUSize.toNat = j := by grind
    have hcb : (co + cl * j.toUSize).toNat + m ≤ c.size := by
      rw [← hco, ← hcl, toNat_col_base C hs.2.2.1 hs.2.2.2.2 hj (by lia), hc]
      exact C.col_le hs.2.2.2.2 hj
    have hcs : c.size < USize.size := hc ▸ hs.2.2.1
    let c' := match uplo with
      | .upper => symmUpperCol α A B β ⟨hs.1, hs.2.1⟩ (co + cl * j.toUSize) j.toUSize
          (by rw [hju]; exact hj) c hcb hcs
      | .lower => symmLowerCol α A B β ⟨hs.1, hs.2.1⟩ (co + cl * j.toUSize) j.toUSize
          (by rw [hju]; exact hj) c hcb hcs
    symmCols uplo α A B β C hs co cl hco hcl (j + 1) c'.1 (c'.2.trans hc)
  else c
termination_by n - j

/-- Steps that each map column `j` by `H j` map the columns by `mapMat`. -/
private theorem iterRange_col_mapMat (a : Float64Array) (off ld : Nat) (hml : m ≤ ld)
    (H : Nat → Nat → Float → Float) (J : Nat) :
    iterRange (fun j c => c.modifyAt (fun i => off + ld * j + i) 0 m (H j)) 0 J a =
      mapMat a off ld m 0 J fun i j v => H j i v := by
  induction J with
  | zero => rw [iterRange_self, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ J ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, ← modifyAt_col_mapMat _ _ _ hml J]
    exact modifyAt_congr _ (fun i _ _ => by simp [Stride.idx]) (fun _ _ _ => rfl)

private theorem symmCols_eq (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) (hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧
      C.data.size < USize.size ∧ n < USize.size ∧ 0 < m)
    (co cl : USize) (hco : C.off.toUSize = co) (hcl : C.ld.toUSize = cl) (j : Nat)
    (c : Float64Array) (hc : c.size = C.data.size) :
    symmCols uplo α A B β C hs co cl hco hcl j c hc =
      iterRange (fun j c => c.modifyAt (fun i => C.off + C.ld * j + i) 0 m
        (symmAt uplo α A B β j)) j n c := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing j c with
  | ind d ih =>
    rw [symmCols]
    split
    · rename_i hj
      have hju : j.toUSize.toNat = j := by grind
      have hcb : (co + cl * j.toUSize).toNat = C.off + C.ld * j := by
        rw [← hco, ← hcl, toNat_col_base C hs.2.2.1 hs.2.2.2.2 hj (by lia)]
      rw [ih (n - (j + 1)) (by lia) (j + 1) _ _ rfl, iterRange_of_lt _ hj]
      congr 1
      cases uplo
      · simp only [symmUpperCol_eq_modifyAt, hcb, hju, symmAt]
      · simp only [symmLowerCol_eq_modifyAt, hcb, hju, symmAt]
    · rename_i hj
      rw [iterRange_of_le _ (by lia)]

/-- The value of `symm` at the row `i` and the column `j`, from the old value `v`. -/
@[expose] public def symmVal (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (i j : Nat) (v : Float) : Float :=
  if α == 0 then betaMul β v else symmAt uplo α A B β j i v

/-- The array of `symm`. -/
public def symmData (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ C.data.size < USize.size ∧
      n < USize.size ∧ 0 < m then
    if α == 0 then C.scalBetaData β
    else symmCols uplo α A B β C hs C.off.toUSize C.ld.toUSize rfl rfl 0 C.data rfl
  else mapMat C.data C.off C.ld m 0 n (symmVal uplo α A B β)

public theorem symmData_eq (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) :
    symmData uplo α A B β C = mapMat C.data C.off C.ld m 0 n (symmVal uplo α A B β) := by
  unfold symmData
  split
  · cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [symmCols_eq, iterRange_col_mapMat _ _ _ C.le_ld]
      apply mapMat_congr
      intro i j v _ _ _
      simp [symmVal, hα]
    · simp only [↓reduceIte]
      rw [scalBetaData_eq]
      apply mapMat_congr
      intro i j v _ _ _
      simp [symmVal, hα]
  · rfl

/--
`symm uplo α A B β C` is `α * A * B + β * C` for the symmetric matrix `A` stored in its triangle
`uplo`, over `C`, by the loops of the reference BLAS for `SIDE = 'L'`. It updates `C` in place when
its array is not shared, leaves the elements of the array outside `C` unchanged, and reads only
the triangle `uplo` of `A`. As in the reference BLAS, it only scales `C` when `α = 0`, and doesn't
read `C` when `β = 0`.
-/
@[expose] public def symm (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) : Mat m n where
  data := symmData uplo α A B β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [symmData_eq, size_mapMat]; exact C.bound

public theorem data_symm (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) :
    (symm uplo α A B β C).data = mapMat C.data C.off C.ld m 0 n (symmVal uplo α A B β) :=
  symmData_eq uplo α A B β C

@[simp] public theorem off_symm (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n)
    (β : Float) (C : Mat m n) : (symm uplo α A B β C).off = C.off := rfl

@[simp] public theorem ld_symm (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n)
    (β : Float) (C : Mat m n) : (symm uplo α A B β C).ld = C.ld := rfl

/-- Element `(i, j)` of `symm uplo α A B β C` is `symmVal` of `C[i, j]`. -/
public theorem getElem_symm (uplo : Uplo) (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symm uplo α A B β C)[(i, j)] = symmVal uplo α A B β i j C[(i, j)] :=
  getElem_of_data_eq_mapMat _ (data_symm uplo α A B β C) rfl rfl i j h


/--
Element `(i, j)` of `symm .upper α A B β C` is `betaMul β C[i, j]` when `α = 0`, and otherwise
`β * C[i, j] + α * B[i, j] * A[i, i] + α * t` (without the first term when `β = 0`), with `t` the
sum of the terms `B[k, j] * A[k, i]` for `k = 0, …, i - 1`, plus the terms
`α * B[k, j] * A[i, k]` for `k = i + 1, …, m - 1`.
-/
public theorem getElem_symm_upper (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symm .upper α A B β C)[(i, j)] =
      if α == 0 then betaMul β C[(i, j)]
      else Nat.fold (m - 1 - i) (fun t _ s =>
          s + α * B[(i + 1 + t, j)]'⟨by lia, h.2⟩ * A[(i, i + 1 + t)]'⟨h.1, by lia⟩)
        (symmDiag β C[(i, j)] (α * B[(i, j)] * A[(i, i)]'⟨h.1, h.1⟩) +
          α * Nat.fold i (fun k _ s =>
            s + B[(k, j)]'⟨by lia, h.2⟩ * A[(k, i)]'⟨by lia, h.1⟩) 0) := by
  rw [getElem_symm _ _ _ _ _ _ _ _ h, symmVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, symmAt, symmUpperAt, symmUpperDot]
    rw [getElem!_pos B.data _ (B.index_lt h.1 h.2), getElem!_pos A.data _ (A.index_lt h.1 h.1)]
    congr 1
    · funext t ht s
      rw [getElem!_pos B.data _ (B.index_lt (by lia) h.2),
        getElem!_pos A.data _ (A.index_lt h.1 (by lia))]
      rfl
    · congr 3
      funext k hk s
      rw [getElem!_pos B.data _ (B.index_lt (by lia) h.2),
        getElem!_pos A.data _ (A.index_lt (by lia) h.1)]
      rfl
  · simp only [↓reduceIte]

/--
Element `(i, j)` of `symm .lower α A B β C` is `betaMul β C[i, j]` when `α = 0`, and otherwise
`β * C[i, j] + α * B[i, j] * A[i, i] + α * t` (without the first term when `β = 0`), with `t` the
sum of the terms `B[k, j] * A[k, i]` for `k = i + 1, …, m - 1`, plus the terms
`α * B[k, j] * A[i, k]` for `k = i - 1, …, 0`.
-/
public theorem getElem_symm_lower (α : Float) (A : Mat m m) (B : Mat m n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symm .lower α A B β C)[(i, j)] =
      if α == 0 then betaMul β C[(i, j)]
      else Nat.fold i (fun t _ s =>
          s + α * B[(i - 1 - t, j)]'⟨by lia, h.2⟩ * A[(i, i - 1 - t)]'⟨h.1, by lia⟩)
        (symmDiag β C[(i, j)] (α * B[(i, j)] * A[(i, i)]'⟨h.1, h.1⟩) +
          α * Nat.fold (m - 1 - i) (fun t _ s =>
            s + B[(i + 1 + t, j)]'⟨by lia, h.2⟩ * A[(i + 1 + t, i)]'⟨by lia, h.1⟩) 0) := by
  rw [getElem_symm _ _ _ _ _ _ _ _ h, symmVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, symmAt, symmLowerAt, symmLowerDot]
    rw [getElem!_pos B.data _ (B.index_lt h.1 h.2), getElem!_pos A.data _ (A.index_lt h.1 h.1)]
    congr 1
    · funext t ht s
      rw [getElem!_pos B.data _ (B.index_lt (by lia) h.2),
        getElem!_pos A.data _ (A.index_lt h.1 (by lia))]
      rfl
    · congr 3
      funext k hk s
      rw [getElem!_pos B.data _ (B.index_lt (by lia) h.2),
        getElem!_pos A.data _ (A.index_lt (by lia) h.1)]
      rfl
  · simp only [↓reduceIte]


/-! ## `symmRight` -/

/-- The element of `A` that `symmRight uplo` reads for the columns `j` and `k ≠ j` of `C`. -/
@[expose] public def symmRightA (uplo : Uplo) (A : Mat n n) (j k : Nat) : Float :=
  match uplo with
  | .upper => if k < j then A.data[A.off + A.ld * j + k]! else A.data[A.off + A.ld * k + j]!
  | .lower => if k < j then A.data[A.off + A.ld * k + j]! else A.data[A.off + A.ld * j + k]!

/-- The column of `B` of the step `t` of column `j` of `symmRight`: the columns `k ≠ j`. -/
@[expose] public def symmRightK (j t : Nat) : Nat := if t < j then t else t + 1

/-- The value of element `i` of column `j` of `symmRight`, from its old value `v`. -/
@[expose] public def symmRightAt (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (j i : Nat) (v : Float) : Float :=
  Nat.fold (n - 1 - j) (fun t _ s =>
      s + α * symmRightA uplo A j (j + 1 + t) * B.data[B.off + B.ld * (j + 1 + t) + i]!)
    (Nat.fold j (fun k _ s => s + α * symmRightA uplo A j k * B.data[B.off + B.ld * k + i]!)
      (symmDiag β v (α * A.data[A.off + A.ld * j + j]! * B.data[B.off + B.ld * j + i]!)))

/-- The steps over the columns `k ≠ j` are the columns `k < j`, then the columns `k > j`. -/
private theorem fold_symmRightK (G : Nat → Float → Float) (j d : Nat) (s : Float) :
    Nat.fold (j + d) (fun t _ s => G (symmRightK j t) s) s =
      Nat.fold d (fun t _ s => G (j + 1 + t) s) (Nat.fold j (fun k _ s => G k s) s) := by
  induction d with
  | zero =>
    have : ∀ N, N ≤ j → Nat.fold N (fun t _ s => G (symmRightK j t) s) s =
        Nat.fold N (fun k _ s => G k s) s := by
      intro N hN
      induction N with
      | zero => rw [Nat.fold_zero, Nat.fold_zero]
      | succ N ih =>
        rw [Nat.fold_succ, Nat.fold_succ, ih (by lia), symmRightK, ite_eq_left (by lia)]
    rw [Nat.add_zero, Nat.fold_zero]
    exact this j (Nat.le_refl _)
  | succ d ih =>
    rw [← Nat.add_assoc, Nat.fold_succ, ih, Nat.fold_succ, symmRightK, ite_eq_right (by lia),
      show j + d + 1 = j + 1 + d by lia]

/-- Steps that each map the same elements, without reading the array, compose into a fold. -/
private theorem iterRange_modifyAt_fold (a : Float64Array) (idx : Nat → Nat)
    (hinj : ∀ i, 0 ≤ i → i < m → ∀ i', 0 ≤ i' → i' < m → idx i = idx i' → i = i')
    (g : Nat → Nat → Float → Float) (T : Nat) :
    iterRange (fun t c => c.modifyAt idx 0 m (g t)) 0 T a =
      a.modifyAt idx 0 m fun i v => Nat.fold T (fun t _ s => g t i s) v := by
  induction T with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _; rw [Nat.fold_zero]
  | succ T ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ _
    rw [Nat.fold_succ]

/-- The column of `B` of the step `t` of column `j` of `symmRight`: `j`, then the others. -/
@[expose] public def symmRightCol (j t : Nat) : Nat := if t = 0 then j else symmRightK j (t - 1)

/-- The factor of the column of `B` of the step `t` of column `j` of `symmRight`. -/
@[expose] public def symmRightW (uplo : Uplo) (α : Float) (A : Mat n n) (j t : Nat) : Float :=
  if t = 0 then α * A.data[A.off + A.ld * j + j]!
  else α * symmRightA uplo A j (symmRightK j (t - 1))

/-- A step of `symmRight` on an element `v` of `C`, with the factor `w` and the element `b` of `B`:
the first one scales `v` by `β`. -/
@[expose] public def symmRightStep (β w b v : Float) (first : Bool) : Float :=
  if first then symmDiag β v (w * b) else v + w * b

/-- The loops of column `j` of `symmRight`, on the array `c` with column `j` of `C` at `cb`. -/
public def symmRightColLoop (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (hs : B.data.size < USize.size ∧ n < USize.size) (cb j : USize) (hj : j.toNat < n)
    (c : Float64Array) (hcb : cb.toNat + m ≤ c.size) (hcs : c.size < USize.size) :
    {c' : Float64Array // c'.size = c.size} :=
  have hmu : m.toUSize.toNat = m := by grind
  have hnu : n.toUSize.toNat = n := by grind
  let bo := B.off.toUSize
  let bl := B.ld.toUSize
  inplace c do
    for t in 0...n.toUSize do
      let k := if t = 0 then j else if t - 1 < j then t - 1 else t
      have hk : k.toNat < n := by grind
      let w := symmRightW uplo α A j.toNat t.toNat
      let first := t == 0
      for i in 0...m.toUSize do
        have hi : i.toNat < m := by lia
        have hq : (cb + i).toNat < c.size := by rw [toNat_add_of_lt hi hcb hcs]; lia
        c[cb + i] := symmRightStep β w (B.uget bo bl rfl rfl hs.1 i k hi hk) c[cb + i] first
  then fun _ c' h => ⟨c', h⟩

/-- A fold over `N + 1` steps is the step `0`, then a fold over the others. -/
private theorem fold_succ_shift (g : Nat → Float → Float) (N : Nat) (s : Float) :
    Nat.fold (N + 1) (fun t _ s => g t s) s = Nat.fold N (fun t _ s => g (t + 1) s) (g 0 s) := by
  induction N with
  | zero => rw [Nat.fold_succ, Nat.fold_zero, Nat.fold_zero]
  | succ N ih => rw [Nat.fold_succ, ih, Nat.fold_succ]

/-- The loops of column `j` of `symmRight` map the column by `symmRightAt`. -/
public theorem symmRightColLoop_eq (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (hs : B.data.size < USize.size ∧ n < USize.size) (cb j : USize)
    (hj : j.toNat < n) (c : Float64Array) (hcb : cb.toNat + m ≤ c.size)
    (hcs : c.size < USize.size) :
    (symmRightColLoop uplo α A B β hs cb j hj c hcb hcs).1 =
      c.modifyAt (fun i => cb.toNat + i) 0 m (symmRightAt uplo α A B β j.toNat) := by
  have hmu : m.toUSize.toNat = m := by grind
  have hnu : n.toUSize.toNat = n := by grind
  have hinj : ∀ i, 0 ≤ i → i < m → ∀ i', 0 ≤ i' → i' < m → cb.toNat + i = cb.toNat + i' →
      i = i' := fun _ _ _ _ _ _ e => by lia
  unfold symmRightColLoop
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun t c => c.modifyAt (fun i => cb.toNat + i) 0 m fun i v =>
      symmRightStep β (symmRightW uplo α A j.toNat t)
        B.data[B.off + B.ld * symmRightCol j.toNat t + i]! v (t == 0))
    (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
    rw [iterRange_modifyAt_fold _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ _
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by lia⟩
    rw [fold_succ_shift]
    simp only [symmRightStep, symmRightW, symmRightCol, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel, beq_iff_eq, BEq.rfl]
    have hfold := fold_symmRightK (fun k s => s + α * symmRightA uplo A j.toNat k *
      B.data[B.off + B.ld * k + i]!) j.toNat (N - j.toNat)
      (symmDiag β v (α * A.data[A.off + A.ld * j.toNat + j.toNat]! *
        B.data[B.off + B.ld * j.toNat + i]!))
    rw [show j.toNat + (N - j.toNat) = N by lia] at hfold
    rw [hfold, symmRightAt, show N + 1 - 1 - j.toNat = N - j.toNat by lia]
  · intro t _ ht next a h
    rw [hnu] at ht
    have hk : (if t = 0 then j else if t - 1 < j then t - 1 else t).toNat =
        symmRightCol j.toNat t.toNat := by
      by_cases h0 : t = 0
      · subst h0; simp [symmRightCol]
      · have h1 : (t - 1).toNat = t.toNat - 1 := by grind
        have h2 : t.toNat ≠ 0 := by grind
        have hlt : (t - 1 < j) = (t.toNat - 1 < j.toNat) := by rw [USize.lt_iff_toNat_lt, h1]
        simp only [h0, h2, ↓reduceIte, symmRightCol, symmRightK, hlt]
        split
        · exact h1
        · lia
    have hkn : symmRightCol j.toNat t.toNat < n := by
      unfold symmRightCol symmRightK; split <;> (try split) <;> lia
    have hf : (t == 0) = (t.toNat == 0) := by grind
    rw [Tail.run_forInFrom_modify
        (G := fun i v => symmRightStep β (symmRightW uplo α A j.toNat t.toNat)
          B.data[B.off + B.ld * symmRightCol j.toNat t.toNat + i]! v (t.toNat == 0))
        (idx := fun i => cb.toNat + i) (e := fun i => cb + i)
        (he := fun i _ hi => toNat_add_of_lt (by lia) hcb hcs)]
    · simp only [USize.toNat_zero, hmu]
    · intro i _ hi v
      rw [hmu] at hi
      simp only [Mat.uget_eq_getElem, getElem_def, hk, hf]
      rw [getElem!_pos B.data _ (B.index_lt hi hkn)]

/-- The loops of `symmRight` over the columns from `j` of the array `c` of `C`. -/
public def symmRightCols (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (C : Mat m n) (hs : B.data.size < USize.size ∧ C.data.size < USize.size ∧
      n < USize.size ∧ 0 < m)
    (co cl : USize) (hco : C.off.toUSize = co) (hcl : C.ld.toUSize = cl) (j : Nat)
    (c : Float64Array) (hc : c.size = C.data.size) : Float64Array :=
  if hj : j < n then
    have hju : j.toUSize.toNat = j := by grind
    have hcb : (co + cl * j.toUSize).toNat + m ≤ c.size := by
      rw [← hco, ← hcl, toNat_col_base C hs.2.1 hs.2.2.2 hj (by lia), hc]
      exact C.col_le hs.2.2.2 hj
    have hcs : c.size < USize.size := hc ▸ hs.2.1
    let c' := symmRightColLoop uplo α A B β ⟨hs.1, hs.2.2.1⟩ (co + cl * j.toUSize) j.toUSize
      (by rw [hju]; exact hj) c hcb hcs
    symmRightCols uplo α A B β C hs co cl hco hcl (j + 1) c'.1 (c'.2.trans hc)
  else c
termination_by n - j

private theorem symmRightCols_eq (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (C : Mat m n) (hs : B.data.size < USize.size ∧ C.data.size < USize.size ∧
      n < USize.size ∧ 0 < m)
    (co cl : USize) (hco : C.off.toUSize = co) (hcl : C.ld.toUSize = cl) (j : Nat)
    (c : Float64Array) (hc : c.size = C.data.size) :
    symmRightCols uplo α A B β C hs co cl hco hcl j c hc =
      iterRange (fun j c => c.modifyAt (fun i => C.off + C.ld * j + i) 0 m
        (symmRightAt uplo α A B β j)) j n c := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing j c with
  | ind d ih =>
    rw [symmRightCols]
    split
    · rename_i hj
      have hju : j.toUSize.toNat = j := by grind
      have hcb : (co + cl * j.toUSize).toNat = C.off + C.ld * j := by
        rw [← hco, ← hcl, toNat_col_base C hs.2.1 hs.2.2.2 hj (by lia)]
      rw [ih (n - (j + 1)) (by lia) (j + 1) _ _ rfl, iterRange_of_lt _ hj]
      congr 1
      simp only [symmRightColLoop_eq, hcb, hju]
    · rename_i hj
      rw [iterRange_of_le _ (by lia)]

/-- The value of `symmRight` at the row `i` and the column `j`, from the old value `v`. -/
@[expose] public def symmRightVal (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (i j : Nat) (v : Float) : Float :=
  if α == 0 then betaMul β v else symmRightAt uplo α A B β j i v

/-- The array of `symmRight`. -/
public def symmRightData (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (C : Mat m n) : Float64Array :=
  if α == 0 then C.scalBetaData β
  else if hs : B.data.size < USize.size ∧ C.data.size < USize.size ∧ n < USize.size ∧ 0 < m then
    symmRightCols uplo α A B β C hs C.off.toUSize C.ld.toUSize rfl rfl 0 C.data rfl
  else mapMat C.data C.off C.ld m 0 n (symmRightVal uplo α A B β)

public theorem symmRightData_eq (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (C : Mat m n) :
    symmRightData uplo α A B β C = mapMat C.data C.off C.ld m 0 n (symmRightVal uplo α A B β) := by
  unfold symmRightData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rw [symmRightCols_eq, iterRange_col_mapMat _ _ _ C.le_ld]
      apply mapMat_congr
      intro i j v _ _ _
      simp [symmRightVal, hα]
    · rfl
  · simp only [↓reduceIte]
    rw [scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [symmRightVal, hα]

/--
`symmRight uplo α A B β C` is `α * B * A + β * C` for the symmetric matrix `A` stored in its
triangle `uplo`, over `C`, by the loops of the reference BLAS for `SIDE = 'R'`. It updates `C` in
place when its array is not shared, leaves the elements of the array outside `C` unchanged, and
reads only the triangle `uplo` of `A`. As in the reference BLAS, it only scales `C` when `α = 0`,
and doesn't read `C` when `β = 0`.
-/
@[expose] public def symmRight (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (C : Mat m n) : Mat m n where
  data := symmRightData uplo α A B β C
  off := C.off
  ld := C.ld
  le_ld := C.le_ld
  bound := by rw [symmRightData_eq, size_mapMat]; exact C.bound

public theorem data_symmRight (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (C : Mat m n) :
    (symmRight uplo α A B β C).data =
      mapMat C.data C.off C.ld m 0 n (symmRightVal uplo α A B β) :=
  symmRightData_eq uplo α A B β C

@[simp] public theorem off_symmRight (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (C : Mat m n) : (symmRight uplo α A B β C).off = C.off := rfl

@[simp] public theorem ld_symmRight (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (C : Mat m n) : (symmRight uplo α A B β C).ld = C.ld := rfl

/-- Element `(i, j)` of `symmRight uplo α A B β C` is `symmRightVal` of `C[i, j]`. -/
public theorem getElem_symmRight (uplo : Uplo) (α : Float) (A : Mat n n) (B : Mat m n)
    (β : Float) (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symmRight uplo α A B β C)[(i, j)] = symmRightVal uplo α A B β i j C[(i, j)] :=
  getElem_of_data_eq_mapMat _ (data_symmRight uplo α A B β C) rfl rfl i j h

/--
Element `(i, j)` of `symmRight .upper α A B β C` is `betaMul β C[i, j]` when `α = 0`, and otherwise
`β * C[i, j] + α * A[j, j] * B[i, j]` (without the first term when `β = 0`), plus the terms
`α * A[k, j] * B[i, k]` for `k = 0, …, j - 1`, then the terms `α * A[j, k] * B[i, k]` for
`k = j + 1, …, n - 1`.
-/
public theorem getElem_symmRight_upper (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symmRight .upper α A B β C)[(i, j)] =
      if α == 0 then betaMul β C[(i, j)]
      else Nat.fold (n - 1 - j) (fun t _ s =>
          s + α * A[(j, j + 1 + t)]'⟨h.2, by lia⟩ * B[(i, j + 1 + t)]'⟨h.1, by lia⟩)
        (Nat.fold j (fun k _ s =>
            s + α * A[(k, j)]'⟨by lia, h.2⟩ * B[(i, k)]'⟨h.1, by lia⟩)
          (symmDiag β C[(i, j)] (α * A[(j, j)]'⟨h.2, h.2⟩ * B[(i, j)]))) := by
  rw [getElem_symmRight _ _ _ _ _ _ _ _ h, symmRightVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, symmRightAt, symmRightA]
    rw [getElem!_pos B.data _ (B.index_lt h.1 h.2), getElem!_pos A.data _ (A.index_lt h.2 h.2)]
    congr 1
    · funext t ht s
      rw [getElem!_pos B.data _ (B.index_lt h.1 (by lia))]
      simp only [show ¬j + 1 + t < j by lia, ↓reduceIte]
      rw [getElem!_pos A.data _ (A.index_lt h.2 (by lia))]
      rfl
    · congr 1
      funext k hk s
      rw [getElem!_pos B.data _ (B.index_lt h.1 (by lia))]
      simp only [hk, ↓reduceIte]
      rw [getElem!_pos A.data _ (A.index_lt (by lia) h.2)]
      rfl
  · simp only [↓reduceIte]

/--
Element `(i, j)` of `symmRight .lower α A B β C` is `betaMul β C[i, j]` when `α = 0`, and otherwise
`β * C[i, j] + α * A[j, j] * B[i, j]` (without the first term when `β = 0`), plus the terms
`α * A[j, k] * B[i, k]` for `k = 0, …, j - 1`, then the terms `α * A[k, j] * B[i, k]` for
`k = j + 1, …, n - 1`.
-/
public theorem getElem_symmRight_lower (α : Float) (A : Mat n n) (B : Mat m n) (β : Float)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (symmRight .lower α A B β C)[(i, j)] =
      if α == 0 then betaMul β C[(i, j)]
      else Nat.fold (n - 1 - j) (fun t _ s =>
          s + α * A[(j + 1 + t, j)]'⟨by lia, h.2⟩ * B[(i, j + 1 + t)]'⟨h.1, by lia⟩)
        (Nat.fold j (fun k _ s =>
            s + α * A[(j, k)]'⟨h.2, by lia⟩ * B[(i, k)]'⟨h.1, by lia⟩)
          (symmDiag β C[(i, j)] (α * A[(j, j)]'⟨h.2, h.2⟩ * B[(i, j)]))) := by
  rw [getElem_symmRight _ _ _ _ _ _ _ _ h, symmRightVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, symmRightAt, symmRightA]
    rw [getElem!_pos B.data _ (B.index_lt h.1 h.2), getElem!_pos A.data _ (A.index_lt h.2 h.2)]
    congr 1
    · funext t ht s
      rw [getElem!_pos B.data _ (B.index_lt h.1 (by lia))]
      simp only [show ¬j + 1 + t < j by lia, ↓reduceIte]
      rw [getElem!_pos A.data _ (A.index_lt (by lia) h.2)]
      rfl
    · congr 1
      funext k hk s
      rw [getElem!_pos B.data _ (B.index_lt h.1 (by lia))]
      simp only [hk, ↓reduceIte]
      rw [getElem!_pos A.data _ (A.index_lt h.2 (by lia))]
      rfl
  · simp only [↓reduceIte]

end Mat

end BLAS.Float64
