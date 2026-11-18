/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Trmv
public import BLAS.Float32.Level2
import all BLAS.Internal

/-!
# Symmetric matrix-vector product

`Mat.symv uplo α A x β y` computes `α * A * x + β * y` for a symmetric matrix `A`, stored in its
triangle `uplo`, over `y`, by the loops of the reference BLAS: it first scales `y` by `β` (setting
it to `0` when `β = 0`), and then, for each column `j` of the triangle, adds `α * x[j]` times the
column to the other elements of `y`, and to `y[j]` the diagonal term and `α` times the dot product
of the column with `x`. Each element of `y` gets these terms in the order of the loops.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n : Nat}

/-! ## The loops -/

/-- A loop whose step `i` adds `g i` to its variable and maps its array by `F i`. -/
private theorem iterRange_pair (g : Nat → Float32) (F : Nat → Float32Array → Float32Array)
    (k : Nat) (s : Float32) (a : Float32Array) :
    iterRange (fun i p => (p.1 + g i, F i p.2)) 0 k (s, a) =
      (Nat.fold k (fun i _ s => s + g i) s, iterRange F 0 k a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, iterRange_succ _ (Nat.zero_le _),
      Nat.fold_succ]

/-- Steps that each write `G i c[idx i]!` at `idx i` are a `modifyAt`. -/
private theorem iterRange_set!_self (a : Float32Array) (idx : Nat → Nat)
    (G : Nat → Float32 → Float32) {lo hi : Nat} :
    iterRange (fun i c => c.set! (idx i) (G i c[idx i]!)) lo hi a = a.modifyAt idx lo hi G := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), modifyAt_of_lt _ _ (by lia), ih _ (by lia)]

/-- Distinct steps `i < j < n` of a vector are at distinct indices. -/
private theorem idx_ne (y : Vec n) {i j : Nat} (hi : i < j) (hj : j < n) :
    y.off + y.inc * i ≠ y.off + y.inc * j := fun e => by
  have := y.fits.injOn (lo := 0) (Nat.le_refl _) i (Nat.zero_le _) (by lia) j (Nat.zero_le _) hj e
  lia

/-- `y.data` scaled by `β`, in place when it is not shared. -/
public def symvScale (β : Float32) (y : Vec n) (hs : y.data.size < USize.size) : Float32Array :=
  have hnu : n.toUSize.toNat = n := y.toNat_toUSize hs
  let a := y.data
  let o := y.off.toUSize
  let c := y.inc.toUSize
  (inplace a do
    for i in 0...n.toUSize do
      have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs (by lia)
      a[o + c * i] := betaMul β a[o + c * i]).2

public theorem symvScale_eq (β : Float32) (y : Vec n) (hs : y.data.size < USize.size) :
    symvScale β y hs = y.data.modifyAt y.stride.idx 0 n fun _ v => betaMul β v := by
  unfold symvScale
  have he := y.loop_idx hs
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v) (he := he)
    (hg := fun _ _ _ _ => rfl)]
  simp only [Tail.run_done, USize.toNat_zero, y.toNat_toUSize hs]

/-! ## The upper triangle -/

/-- The dot product of column `j` of the upper triangle, above the diagonal, with `x`. -/
@[expose] public def symvUpperDot (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  Nat.fold j (fun k _ s => s + A.data[A.off + A.ld * j + k]! * x.data[x.off + x.inc * k]!) 0

/--
The step `j` of the upper product: add `α * x[j]` times column `j` of `A` to the elements above
it, and the diagonal term and `α` times `symvUpperDot A x j` to element `j`.
-/
@[expose] public def symvUpperStep (α : Float32) (A : Mat n n) (x y : Vec n) (j : Nat)
    (c : Float32Array) : Float32Array :=
  c.modifyAt y.stride.idx 0 (j + 1) fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! +
        α * symvUpperDot A x j
    else v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The step `j` of the upper product updates the elements above `j`, and then element `j`. -/
private theorem symvUpperStep_eq (α : Float32) (A : Mat n n) (x y : Vec n) {j : Nat}
    (hj : j < n) (c : Float32Array) :
    symvUpperStep α A x y j c =
      (c.modifyAt (fun i => y.off + y.inc * i) 0 j fun i v =>
        v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!).set!
        (y.off + y.inc * j) (c[y.off + y.inc * j]! +
          α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! +
          α * symvUpperDot A x j) := by
  have e : y.stride.idx = fun i => y.off + y.inc * i := rfl
  rw [symvUpperStep, e, modifyAt_succ _ _ (Nat.zero_le _)]
  simp only [↓reduceIte]
  rw [modifyAt_congr_fun _ _ (g' := fun i v =>
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!)
    (fun i v _ hi => ite_eq_right (by lia))]
  rw [getElem!_modifyAt_of_ne _ _ (p := y.off + y.inc * j) _ (fun i _ hi => idx_ne y hi hj)]

/-- The loops of the upper product on the array `c` of `y`, already scaled by `β`. -/
public def symvUpperData (α : Float32) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) : Float32Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  (inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      for i in 0...j with (s := 0) do
        have hi : i.toNat < n := Nat.lt_trans (by assumption) hjn
        have hk : (o + cc * i).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := A.uget ao al rfl rfl hs.1 i j hi hjn
        c[o + cc * i] := c[o + cc * i] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 i hi
      have hk : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      c[o + cc * j] := c[o + cc * j] + t * A.uget ao al rfl rfl hs.1 j j hjn hjn + α * s).2

public theorem symvUpperData_eq_iterRange (α : Float32) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    symvUpperData α A x y hs o cc ho hcc c hc = iterRange (symvUpperStep α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  subst ho hcc
  unfold symvUpperData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := symvUpperStep α A x y)
    (hF := fun _ _ => by unfold symvUpperStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hp : (y.off.toUSize + y.inc.toUSize * j).toNat = y.off + y.inc * j.toNat :=
      y.toNat_index hs.2.2 hj
    rw [Tail.run_forInFrom (f := fun i p =>
        (p.1 + A.data[A.off + A.ld * j.toNat + i]! * x.data[x.off + x.inc * i]!,
          p.2.set! (y.off + y.inc * i) (p.2[y.off + y.inc * i]! +
            α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun i => A.data[A.off + A.ld * j.toNat + i]! * x.data[x.off + x.inc * i]!)
        (fun i c => c.set! (y.off + y.inc * i) (c[y.off + y.inc * i]! +
          α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]!)) j.toNat 0 a
      rw [iterRange_set!_self a (fun i => y.off + y.inc * i) (fun i v =>
        v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + i]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_readThen, Tail.run_writeThen]
      apply run_congr
      simp only [hpair, Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, hp]
      rw [set_eq_set!, symvUpperStep_eq α A x y hj]
      congr 1
      simp only [getElem_eq_getElem!]
      rw [getElem!_modifyAt_of_ne _ _ _ (fun i _ hi => idx_ne y hi hj)]
      rfl
    · intro i _ hi next' s a' h'
      have hin : i.toNat < n := by lia
      have hq : (y.off.toUSize + y.inc.toUSize * i).toNat = y.off + y.inc * i.toNat :=
        y.toNat_index hs.2.2 hin
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, hq]
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/-- The value of element `i` of the upper product, from its value `v` after the scaling. -/
@[expose] public def symvUpperAt (α : Float32) (A : Mat n n) (x : Vec n) (i : Nat) (v : Float32) :
    Float32 :=
  Nat.fold (n - 1 - i) (fun t _ s =>
      s + α * x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
    (v + α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i + i]! + α * symvUpperDot A x i)

/--
After the steps `l < j`, the elements `i < j` have their diagonal term, their dot product and the
terms `l < j`, and the others are unchanged.
-/
theorem iterRange_symvUpperStep (α : Float32) (A : Mat n n) (x y : Vec n) (c : Float32Array)
    (hc : c.size = y.data.size) {j : Nat} (hj : j ≤ n) :
    iterRange (symvUpperStep α A x y) 0 j c = c.modifyAt y.stride.idx 0 n fun i v =>
      if i < j then Nat.fold (j - 1 - i) (fun t _ s =>
          s + α * x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
        (v + α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i + i]! +
          α * symvUpperDot A x i)
      else v := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), symvUpperStep,
      modifyAt_widen (lo := 0) (hi := j + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.le_refl _)
        (Nat.zero_le _) (by lia), modifyAt_modifyAt _ _ hinj]
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

/-- The loops of the upper product map the array of the scaled `y` by `symvUpperAt`. -/
public theorem symvUpperData_eq (α : Float32) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    symvUpperData α A x y hs o cc ho hcc c hc = c.modifyAt y.stride.idx 0 n (symvUpperAt α A x) := by
  rw [symvUpperData_eq_iterRange, iterRange_symvUpperStep α A x y c hc (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [hi, ite_true, symvUpperAt]

/-! ## The lower triangle -/

private theorem set!_comm' (a : Float32Array) {p q : Nat} (v w : Float32) (h : p ≠ q) :
    (a.set! p v).set! q w = (a.set! q w).set! p v := by
  apply ext_getElem?; intro r
  simp only [getElem?_set!, size_set!]
  by_cases hp : p = r <;> by_cases hq : q = r
  · exact absurd (hp.trans hq.symm) h
  all_goals simp [hp, hq]

private theorem getElem!_set!_of_ne' (a : Float32Array) {p q : Nat} (v : Float32) (h : p ≠ q) :
    (a.set! p v)[q]! = a[q]! := by
  by_cases hq : q < a.size
  · rw [getElem!_set!_of_lt _ _ _ hq, ite_eq_right h]
  · rw [getElem!_neg _ q (by simpa using hq), getElem!_neg a q hq]

/-- A write at an index of no step commutes with `modifyAt`. -/
private theorem modifyAt_set!' (a : Float32Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float32 → Float32) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) (v : Float32) :
    (a.set! p v).modifyAt idx lo hi g = (a.modifyAt idx lo hi g).set! p v := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [modifyAt_of_le _ _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    have hne := hp lo (Nat.le_refl _) (by lia)
    rw [modifyAt_of_lt (a.set! p v) idx (lo := lo) (hi := hi) (by lia) g,
      modifyAt_of_lt a idx (lo := lo) (hi := hi) (by lia) g, getElem!_set!_of_ne' _ _ hne.symm,
      set!_comm' _ _ _ hne.symm, ih _ (fun i h₁ h₂ => hp i (by lia) h₂) (by lia)]

/-- The dot product of column `j` of the lower triangle, below the diagonal, with `x`. -/
@[expose] public def symvLowerDot (A : Mat n n) (x : Vec n) (j : Nat) : Float32 :=
  Nat.fold (n - 1 - j) (fun t _ s =>
    s + A.data[A.off + A.ld * j + (j + 1 + t)]! * x.data[x.off + x.inc * (j + 1 + t)]!) 0

/--
The step `j` of the lower product: add `α * x[j]` times column `j` of `A` to the elements below
it, and the diagonal term and `α` times `symvLowerDot A x j` to element `j`.
-/
@[expose] public def symvLowerStep (α : Float32) (A : Mat n n) (x y : Vec n) (j : Nat)
    (c : Float32Array) : Float32Array :=
  c.modifyAt y.stride.idx j n fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! +
        α * symvLowerDot A x j
    else v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The step `j` of the lower product updates the elements below `j`, and then element `j`. -/
private theorem symvLowerStep_eq (α : Float32) (A : Mat n n) (x y : Vec n) {j : Nat}
    (hj : j < n) (c : Float32Array) (hc : c.size = y.data.size) :
    symvLowerStep α A x y j c =
      (c.modifyAt (fun t => y.off + y.inc * (j + 1 + t)) 0 (n - 1 - j) fun t v =>
        v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (j + 1 + t)]!).set!
        (y.off + y.inc * j) (c[y.off + y.inc * j]! +
          α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! +
          α * symvLowerDot A x j) := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  rw [symvLowerStep, modifyAt_of_lt _ _ hj]
  simp only [↓reduceIte]
  rw [modifyAt_set!' _ _ _ (fun i h₁ h₂ e => by
    have := hinj i (Nat.zero_le _) h₂ j (Nat.zero_le _) hj e
    lia)]
  have e : (fun t => y.off + y.inc * (j + 1 + t)) = (y.stride.shift (j + 1)).idx := by
    funext t; rw [Stride.idx_shift]; rfl
  have hs := modifyAt_shift c y.stride (j + 1) (n - 1 - j) fun t v =>
    v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (j + 1 + t)]!
  rw [show j + 1 + (n - 1 - j) = n by lia] at hs
  rw [e, hs]
  congr 1
  apply modifyAt_congr_fun
  intro i v h₁ _
  rw [ite_eq_right (by lia), show j + 1 + (i - (j + 1)) = i by lia]

/-- The loops of the lower product on the array `c` of `y`, already scaled by `β`. -/
public def symvLowerData (α : Float32) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) : Float32Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  (inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      have hk : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      let d := c[o + cc * j] + t * A.uget ao al rfl rfl hs.1 j j hjn hjn
      for l in 0...(nu - 1 - j) with (s := 0) do
        have hi : (j + 1 + l).toNat < n := by grind
        have hk' : (o + cc * (j + 1 + l)).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := A.uget ao al rfl rfl hs.1 (j + 1 + l) j hi hjn
        c[o + cc * (j + 1 + l)] := c[o + cc * (j + 1 + l)] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 (j + 1 + l) hi
      c[o + cc * j] := d + α * s).2

public theorem symvLowerData_eq_iterRange (α : Float32) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    symvLowerData α A x y hs o cc ho hcc c hc = iterRange (symvLowerStep α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  subst ho hcc
  unfold symvLowerData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := symvLowerStep α A x y)
    (hF := fun _ _ => by unfold symvLowerStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hp : (y.off.toUSize + y.inc.toUSize * j).toNat = y.off + y.inc * j.toNat :=
      y.toNat_index hs.2.2 hj
    have hm : (n.toUSize - 1 - j).toNat = n - 1 - j.toNat := by grind
    simp only [Tail.run_readThen]
    rw [Tail.run_forInFrom (f := fun l p =>
        (p.1 + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + l)]! *
            x.data[x.off + x.inc * (j.toNat + 1 + l)]!,
          p.2.set! (y.off + y.inc * (j.toNat + 1 + l)) (p.2[y.off + y.inc * (j.toNat + 1 + l)]! +
            α * x.data[x.off + x.inc * j.toNat]! *
              A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + l)]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun l => A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + l)]! *
          x.data[x.off + x.inc * (j.toNat + 1 + l)]!)
        (fun l c => c.set! (y.off + y.inc * (j.toNat + 1 + l))
          (c[y.off + y.inc * (j.toNat + 1 + l)]! + α * x.data[x.off + x.inc * j.toNat]! *
            A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + l)]!)) (n - 1 - j.toNat) 0 a
      rw [iterRange_set!_self a (fun l => y.off + y.inc * (j.toNat + 1 + l)) (fun l v =>
        v + α * x.data[x.off + x.inc * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + l)]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_writeThen, hm]
      apply run_congr
      simp only [hpair, Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, hp]
      rw [set_eq_set!, symvLowerStep_eq α A x y hj a (h.trans hc)]
      congr 1
      simp only [getElem_eq_getElem!]
      rfl
    · intro l _ hl next' s a' h'
      rw [hm] at hl
      have hin : j.toNat + 1 + l.toNat < n := by lia
      have hl' : (j + 1 + l).toNat = j.toNat + 1 + l.toNat := by grind
      have hq : (y.off.toUSize + y.inc.toUSize * (j + 1 + l)).toNat =
          y.off + y.inc * (j.toNat + 1 + l.toNat) := by
        rw [y.toNat_index hs.2.2 (by rw [hl']; exact hin), hl']
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, hq, hl']
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/-- The value of element `i` of the lower product, from its value `v` after the scaling. -/
@[expose] public def symvLowerAt (α : Float32) (A : Mat n n) (x : Vec n) (i : Nat) (v : Float32) :
    Float32 :=
  Nat.fold i (fun j _ s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!) v +
    α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i + i]! + α * symvLowerDot A x i

/--
After the steps `l < j`, the elements `i < j` are final, and the others have the terms `l < j`.
-/
theorem iterRange_symvLowerStep (α : Float32) (A : Mat n n) (x y : Vec n) (c : Float32Array)
    (hc : c.size = y.data.size) {j : Nat} (hj : j ≤ n) :
    iterRange (symvLowerStep α A x y) 0 j c = c.modifyAt y.stride.idx 0 n fun i v =>
      if i < j then symvLowerAt α A x i v
      else Nat.fold j (fun l _ s =>
        s + α * x.data[x.off + x.inc * l]! * A.data[A.off + A.ld * l + i]!) v := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), symvLowerStep,
      modifyAt_widen (lo := j) (hi := n) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _)
        (by lia) (Nat.le_refl _), modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < j
    · simp [h₁, show i < j + 1 by lia, show ¬j ≤ i by lia]
    · by_cases h₂ : i = j
      · subst h₂
        simp [symvLowerAt, hi]
      · simp only [h₁, show ¬i < j + 1 by lia, show j ≤ i by lia, hi, h₂, and_self, ite_true,
          ite_false, Nat.fold_succ]

/-- The loops of the lower product map the array of the scaled `y` by `symvLowerAt`. -/
public theorem symvLowerData_eq (α : Float32) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float32Array) (hc : c.size = y.data.size) :
    symvLowerData α A x y hs o cc ho hcc c hc = c.modifyAt y.stride.idx 0 n (symvLowerAt α A x) := by
  rw [symvLowerData_eq_iterRange, iterRange_symvLowerStep α A x y c hc (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [hi, ite_true]

/-! ## `symv` -/

/-- The value of element `i` of the product on the triangle `uplo`, from its scaled value `v`. -/
@[expose] public def symvAt (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) : Nat → Float32 →
    Float32 :=
  match uplo with
  | .upper => symvUpperAt α A x
  | .lower => symvLowerAt α A x

/--
The value of `symv` at the index `i` of `y`, from its old value `v`: `betaMul β v` when `α = 0`,
and otherwise `symvAt` of it.
-/
@[expose] public def symvVal (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (i : Nat) (v : Float32) : Float32 :=
  if α == 0 then betaMul β v else symvAt uplo α A x i (betaMul β v)

/-- The array of `symv`. -/
public def symvData (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let o := y.off.toUSize
    let cc := y.inc.toUSize
    if α == 0 then symvScale β y hs.2.2
    else match uplo with
      | .upper => symvUpperData α A x y hs o cc rfl rfl (symvScale β y hs.2.2)
          (by rw [symvScale_eq, size_modifyAt])
      | .lower => symvLowerData α A x y hs o cc rfl rfl (symvScale β y hs.2.2)
          (by rw [symvScale_eq, size_modifyAt])
  else y.data.modifyAt y.stride.idx 0 n (symvVal uplo α A x β)

public theorem symvData_eq (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) :
    symvData uplo α A x β y = y.data.modifyAt y.stride.idx 0 n (symvVal uplo α A x β) := by
  have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
  unfold symvData
  split
  · rename_i hs
    cases hα : α == 0
    · cases uplo
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [symvUpperData_eq, symvScale_eq, modifyAt_modifyAt _ _ hinj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp [symvVal, symvAt, hα]
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [symvLowerData_eq, symvScale_eq, modifyAt_modifyAt _ _ hinj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp [symvVal, symvAt, hα]
    · simp only [↓reduceIte]
      rw [symvScale_eq]
      apply modifyAt_congr_fun
      intro i v _ _
      simp [symvVal, hα]
  · rfl

/--
`symv uplo α A x β y` is `α * A * x + β * y` for the symmetric matrix `A` stored in its triangle
`uplo`, over `y`, by the loops of the reference BLAS. It updates `y` in place when its array is not
shared, leaves the elements of the array outside `y` unchanged, and reads only the triangle `uplo`
of `A`. As in the reference BLAS, it sets `y` to `0` before adding the terms when `β = 0`, and only
scales `y` when `α = 0`.
-/
@[expose] public def symv (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) : Vec n where
  data := symvData uplo α A x β y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [symvData_eq, size_modifyAt]; exact y.bound

/-- The array of `symv uplo α A x β y` is the array of `y` with its elements updated. -/
public theorem data_symv (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) :
    (symv uplo α A x β y).data = y.data.modifyAt y.stride.idx 0 n (symvVal uplo α A x β) :=
  symvData_eq uplo α A x β y

@[simp] public theorem off_symv (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) : (symv uplo α A x β y).off = y.off := rfl

@[simp] public theorem inc_symv (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) : (symv uplo α A x β y).inc = y.inc := rfl

/-- Element `i` of `symv uplo α A x β y` is `symvVal` of `y[i]`. -/
public theorem getElem_symv (uplo : Uplo) (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32)
    (y : Vec n) (i : Nat) (h : i < n) :
    (symv uplo α A x β y)[i] = symvVal uplo α A x β i y[i] :=
  Vec.getElem_of_data_eq_modifyAt _ (data_symv uplo α A x β y) (off_symv uplo α A x β y)
    (inc_symv uplo α A x β y) i h

/--
Element `i` of `symv .upper α A x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i] + α * x[i] * A[i, i] + α * t`, with `t` the sum of the terms `A[k, i] * x[k]` for
`k = 0, …, i - 1`, plus the terms `α * x[j] * A[i, j]` for `j = i + 1, …, n - 1`.
-/
public theorem getElem_symv_upper (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32) (y : Vec n)
    (i : Nat) (h : i < n) :
    (symv .upper α A x β y)[i] =
      if α == 0 then betaMul β y[i]
      else Nat.fold (n - 1 - i) (fun t _ s =>
          s + α * x[i + 1 + t]'(by lia) * A[(i, i + 1 + t)]'⟨h, by lia⟩)
        (betaMul β y[i] + α * x[i] * A[(i, i)] +
          α * Nat.fold i (fun k _ s => s + A[(k, i)]'⟨by lia, h⟩ * x[k]'(by lia)) 0) := by
  rw [getElem_symv _ _ _ _ _ _ _ h, symvVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, symvAt, symvUpperAt, symvUpperDot]
    rw [getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
    congr 1
    · funext t ht s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt h (by lia))]
      rfl
    · congr 3
      funext k hk s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt (by lia) h)]
      rfl
  · simp only [↓reduceIte]

/--
Element `i` of `symv .lower α A x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i]` plus the terms `α * x[j] * A[i, j]` for `j = 0, …, i - 1`, plus
`α * x[i] * A[i, i] + α * t`, with `t` the sum of the terms `A[k, i] * x[k]` for
`k = i + 1, …, n - 1`.
-/
public theorem getElem_symv_lower (α : Float32) (A : Mat n n) (x : Vec n) (β : Float32) (y : Vec n)
    (i : Nat) (h : i < n) :
    (symv .lower α A x β y)[i] =
      if α == 0 then betaMul β y[i]
      else Nat.fold i (fun j _ s => s + α * x[j]'(by lia) * A[(i, j)]'⟨h, by lia⟩)
          (betaMul β y[i]) + α * x[i] * A[(i, i)] +
        α * Nat.fold (n - 1 - i) (fun t _ s =>
          s + A[(i + 1 + t, i)]'⟨by lia, h⟩ * x[i + 1 + t]'(by lia)) 0 := by
  rw [getElem_symv _ _ _ _ _ _ _ h, symvVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, symvAt, symvLowerAt, symvLowerDot]
    rw [getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
    congr 2
    · congr 1
      funext j hj s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt h (by lia))]
      rfl
    · congr 2
      funext t ht s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt (by lia) h)]
      rfl
  · simp only [↓reduceIte]

end Mat

end BLAS.Float32
