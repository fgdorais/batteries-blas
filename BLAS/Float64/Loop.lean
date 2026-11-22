/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# Specifications of loops

What the kernels need beyond scalar-arrays' models of loops: `foldUpTo`, a reduction over `USize`
indices, a few element lemmas, the elements of `iterRange` loops over contiguous
windows, which the `gemm` kernels use, and the algebra of `modifyAt` at the indices of a stride.

scalar-arrays gives the models of loops, `iterRange` and `Float64Array.modifyAt`, the
`InPlace.Tail` lemmas that run a loop to them, and `Stride`, with `Stride.Fits` for a stride whose
indices are distinct and in bounds.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

/-! ## Scaling by `β` -/

/--
`β * v`, or `0` when `β = 0`, without reading `v`: the reference BLAS scales `y` or `C` by `β` this
way in `gemv` and `gemm`, so that a `NaN` or an infinity in them doesn't survive `β = 0`.
-/
@[inline, expose] public def betaMul (β v : Float) : Float := if β == 0 then 0 else β * v

/-! ## Reductions -/

/--
`Nat.fold n f init`, as a loop over `USize` indices when `n < USize.size`, which holds for the size
of every array in memory, and as `Nat.fold` otherwise. It keeps a scalar `β` unboxed.

The loop runs `fu`, a version of `f` that takes the index as a `USize`, so that it can read arrays
with `uget`. A step that took a `Nat` index would convert it from `USize` and back at every element,
which costs about a third of a reduction's time. `foldUpTo_eq` needs `fu` to agree with `f`.
-/
@[specialize] public def foldUpTo {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (init : β) : β :=
  if hn : n < USize.size then loop n.toUSize (by grind) 0 init
  else Nat.fold n f init
where
  /-- The loop from the index `i`, up to the bound `m`, which is `n`. -/
  @[specialize] loop (m : USize) (hm : m.toNat = n) (i : USize) (b : β) : β :=
    if hi : i < m then loop m hm (i + 1) (fu i (hm ▸ hi) b) else b
  termination_by m.toNat - i.toNat
  decreasing_by
    grind

private theorem foldUpTo_loop_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (m : USize) (hm : m.toNat = n) (i : USize) (k : Nat) (hk : i.toNat = k) (hkn : k ≤ n)
    (init : β) :
    foldUpTo.loop n fu m hm i (Nat.fold k (fun j hj => f j (by lia)) init) =
      Nat.fold n f init := by
  obtain ⟨d, hd⟩ : ∃ d, n - k = d := ⟨_, rfl⟩
  induction d generalizing i k with
  | zero =>
    rw [foldUpTo.loop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : k = n := by lia
    rfl
  | succ d ih =>
    have hi : i.toNat < n := by lia
    have hsucc : (i + 1).toNat = k + 1 := by grind
    rw [foldUpTo.loop, dite_eq_left_of_eq_true (eq_true (by grind)),
      hf]
    have := ih (i + 1) (k + 1) hsucc (by lia) (by lia)
    rw [Nat.fold_succ] at this
    subst hk
    exact this

public theorem foldUpTo_eq {β : Type u} (n : Nat) (f : (i : Nat) → i < n → β → β)
    (fu : (i : USize) → i.toNat < n → β → β) (hf : ∀ i h b, fu i h b = f i.toNat h b)
    (init : β) : foldUpTo n f fu init = Nat.fold n f init := by
  unfold foldUpTo
  split
  · simpa using foldUpTo_loop_eq n f fu hf _ _ 0 0 (by simp) (by lia) init
  · rfl

/-! ## Elements -/

/-- A program that writes `v` at a `USize` index runs as one that writes it with `set!`. -/
public theorem run_set_eq_set! {N : Nat} {γ : Type} (t : InPlace.Tail N γ) (a : Float64Array)
    (i : USize) (p : Nat) (hp : i.toNat = p) (v v' : Float) (hv : v = v') (h₁ h₂ h₃) :
    t.run (a.set i.toNat v h₁) h₂ = t.run (a.set! p v') h₃ := by
  subst hp hv
  congr 1
  simp [Float64Array.set!, h₁]

/-- A program runs the same on equal arrays. -/
public theorem run_congr {N : Nat} {γ : Type} (t : InPlace.Tail N γ) {a a' : Float64Array}
    (e : a = a') (h : a.size = N) (h' : a'.size = N) : t.run a h = t.run a' h' := by
  subst e; rfl

/-- `set` is `set!` in bounds. -/
public theorem set_eq_set! (a : Float64Array) (i : Nat) (v : Float) (h : i < a.size) :
    a.set i v h = a.set! i v := by
  simp [Float64Array.set!, h]

/-- `getElem` is `getElem!` in bounds. -/
public theorem getElem_eq_getElem! (a : Float64Array) (i : Nat) (h : i < a.size) :
    a[i] = a[i]! := (getElem!_pos a i h).symm

/-! ## Loops of loops -/

/-- The steps of `iterRange` that keep the size of the array keep it. -/
public theorem size_iterRange (F : Nat → Float64Array → Float64Array)
    (hF : ∀ j a, (F j a).size = a.size) (lo hi : Nat) (a : Float64Array) :
    (iterRange F lo hi a).size = a.size :=
  iterRange_invariant (fun b : Float64Array => b.size = a.size)
    (fun j _ _ b hb => (hF j b).trans hb) rfl

/-- An element that no step changes is unchanged. -/
public theorem getElem!_iterRange_of_frame (F : Nat → Float64Array → Float64Array) (q : Nat)
    {lo hi : Nat} (hF : ∀ j, lo ≤ j → j < hi → ∀ a, (F j a)[q]! = a[q]!) (a : Float64Array) :
    (iterRange F lo hi a)[q]! = a[q]! := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le F (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt F (by lia), ih (fun j h₁ h₂ => hF j (by lia) h₂) _ (by lia),
      hF lo (Nat.le_refl _) (by lia)]

/--
An element that each step `F l` maps by `g l`, whatever the other elements of an array of size `N`,
ends up as the left fold of the `g l` over `l < hi`.
-/
public theorem getElem!_iterRange_of_pointwise (F : Nat → Float64Array → Float64Array) (q : Nat)
    (hi N : Nat) (g : (l : Nat) → l < hi → Float → Float) (hF : ∀ j a, (F j a).size = a.size)
    (hg : ∀ l (h : l < hi) a, a.size = N → (F l a)[q]! = g l h a[q]!) (a : Float64Array)
    (ha : a.size = N) :
    (iterRange F 0 hi a)[q]! = Nat.fold hi g a[q]! := by
  induction hi with
  | zero => rw [iterRange_of_le F (Nat.le_refl _), Nat.fold_zero]
  | succ hi ih =>
    rw [iterRange_succ F (Nat.zero_le _), hg hi (by lia) _ (by rw [size_iterRange F hF, ha]),
      Nat.fold_succ, ih (fun l h => g l (by lia)) (fun l h a => hg l (by lia) a)]

/--
A step `a.set! (off + i) (G i a[off + i]!)` for each `i` in `lo ≤ i < hi` maps the elements in
the window `off + lo ≤ p < off + hi` by `G (p - off)`, and leaves the others.
-/
public theorem getElem!_iterRange_set! (off : Nat) (G : Nat → Float → Float) (lo hi : Nat)
    (a : Float64Array) (p : Nat) (hp : p < a.size) :
    (iterRange (fun i a => a.set! (off + i) (G i a[off + i]!)) lo hi a)[p]! =
      if off + lo ≤ p ∧ p < off + hi then G (p - off) a[p]! else a[p]! := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    rw [iterRange_of_le _ (by lia)]
    split <;> first | rfl | lia
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), ih (lo + 1) _ (by simpa using hp) (by lia)]
    by_cases hp' : p = off + lo
    · subst hp'
      have : ¬lo + 1 ≤ lo := by lia
      simp [getElem!_pos, hp, this, show lo < hi by lia]
    · have : (a.set! (off + lo) (G lo a[off + lo]!))[p]! = a[p]! := by
        simp [getElem!_pos, hp, Ne.symm hp']
      rw [this]
      split <;> split <;> first | rfl | lia

/-- `getElem!` of `set!`, in bounds. -/
public theorem getElem!_set!_of_lt (a : Float64Array) (i : Nat) (v : Float) {q : Nat}
    (hq : q < a.size) : (a.set! i v)[q]! = if i = q then v else a[q]! := by
  rw [getElem!_pos (a.set! i v) q (by simpa using hq), getElem!_pos a q hq,
    Float64Array.getElem_set!]

/--
A step that writes `G i a[off + i]!` at `off + i` and `G' i a[off' + i]!` at `off' + i`, for each
`i` in `lo ≤ i < hi`, in two windows that don't overlap, maps the elements of each window by its
function, and leaves the others.
-/
public theorem getElem!_iterRange_set2! (off off' : Nat) (G G' : Nat → Float → Float)
    (lo hi : Nat) (hd : off + hi ≤ off') (a : Float64Array) (p : Nat) (hp : p < a.size) :
    (iterRange (fun i a => (a.set! (off + i) (G i a[off + i]!)).set! (off' + i)
        (G' i a[off' + i]!)) lo hi a)[p]! =
      if off + lo ≤ p ∧ p < off + hi then G (p - off) a[p]!
      else if off' + lo ≤ p ∧ p < off' + hi then G' (p - off') a[p]! else a[p]! := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero =>
    rw [iterRange_of_le _ (by lia)]
    split
    · lia
    · split
      · lia
      · rfl
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), ih (lo + 1) _ (by simpa using hp) (by lia)]
    have e : ∀ q, q < a.size →
        ((a.set! (off + lo) (G lo a[off + lo]!)).set! (off' + lo) (G' lo a[off' + lo]!))[q]! =
          if q = off' + lo then G' lo a[off' + lo]! else if q = off + lo then G lo a[off + lo]!
          else a[q]! := by
      intro q hq
      rw [getElem!_set!_of_lt _ _ _ (by simpa using hq), getElem!_set!_of_lt _ _ _ hq]
      have hne : off' ≠ off := by lia
      by_cases h1 : q = off' + lo
      · simp [h1]
      · by_cases h2 : q = off + lo
        · simp [h2, hne, hne.symm]
        · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    simp only [e p hp]
    by_cases h1 : p = off' + lo
    · subst h1
      simp only [show off' + lo - off' = lo by lia]
      (repeat' split) <;> first | rfl | lia
    · by_cases h2 : p = off + lo
      · subst h2
        simp only [show off + lo - off = lo by lia]
        (repeat' split) <;> first | rfl | lia
      · (repeat' split) <;> first | rfl | lia

/-! ## Updates at the indices of a stride -/

/-- `set!` of the element already there leaves the array unchanged. -/
public theorem set!_getElem!_self (a : Float64Array) (i : Nat) : a.set! i a[i]! = a := by
  apply ext_getElem (by simp)
  intro q _ _
  rw [getElem_set!]
  split
  · rename_i e; subst e; exact getElem!_pos a i (by simpa using ‹i < (a.set! i a[i]!).size›)
  · rfl

/-- `modifyAt` by the identity leaves the array unchanged. -/
public theorem modifyAt_id (a : Float64Array) (idx : Nat → Nat) (lo hi : Nat) :
    a.modifyAt idx lo hi (fun _ v => v) = a := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo with
  | zero => exact modifyAt_of_le _ _ (by lia) _
  | succ d ih => rw [modifyAt_of_lt _ _ (by lia), set!_getElem!_self, ih _ (by lia)]

/-- `modifyAt` depends only on the values of its update at the steps of its range. -/
public theorem modifyAt_congr_fun (a : Float64Array) (idx : Nat → Nat) {lo hi : Nat}
    {g g' : Nat → Float → Float} (h : ∀ i v, lo ≤ i → i < hi → g i v = g' i v) :
    a.modifyAt idx lo hi g = a.modifyAt idx lo hi g' :=
  modifyAt_congr a (fun _ _ _ => rfl) (fun i h₁ h₂ => funext fun v => h i v h₁ h₂)

/-- Writing at the index `idx j` is `modifyAt` over the single step `j`. -/
public theorem set_eq_modifyAt (a : Float64Array) (idx : Nat → Nat) (j : Nat) (v : Float)
    (h : idx j < a.size) : a.set (idx j) v h = a.modifyAt idx j (j + 1) fun _ _ => v := by
  rw [modifyAt_of_lt _ _ (Nat.lt_succ_self j), modifyAt_self, set_eq_set!]

/--
`modifyAt` over `lo ≤ i < hi` is `modifyAt` over a wider range, by the identity at the other
steps.
-/
public theorem modifyAt_widen (a : Float64Array) (idx : Nat → Nat) {lo hi lo' hi' : Nat}
    (g : Nat → Float → Float) (h₁ : lo' ≤ lo) (h₂ : lo ≤ hi) (h₃ : hi ≤ hi') :
    a.modifyAt idx lo hi g =
      a.modifyAt idx lo' hi' fun i v => if lo ≤ i ∧ i < hi then g i v else v := by
  rw [modifyAt_split _ _ h₁ (show lo ≤ hi' by lia), modifyAt_split _ _ h₂ h₃,
    modifyAt_congr _ (lo := lo') (hi := lo) (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun i _ h => by funext v; simp [show ¬lo ≤ i by lia]),
    modifyAt_congr _ (lo := hi) (hi := hi') (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun i h _ => by funext v; simp [show ¬i < hi by lia]),
    modifyAt_congr _ (lo := lo) (hi := hi) (g := fun i v => if lo ≤ i ∧ i < hi then g i v else v)
      (g' := g) (fun _ _ _ => rfl) (fun i h₁ h₂ => by funext v; simp [h₁, h₂]),
    modifyAt_id, modifyAt_id]

/-- `modifyAt` from the step `k` of a stride is `modifyAt` on the stride from that step. -/
public theorem modifyAt_shift (a : Float64Array) (s : Stride) (k h : Nat)
    (g : Nat → Float → Float) :
    a.modifyAt (s.shift k).idx 0 h g = a.modifyAt s.idx k (k + h) fun i v => g (i - k) v := by
  induction h with
  | zero => rw [modifyAt_self, Nat.add_zero, modifyAt_self]
  | succ h ih =>
    rw [modifyAt_succ _ _ (Nat.zero_le _), ← Nat.add_assoc, modifyAt_succ _ _ (by lia), ← ih,
      Stride.idx_shift, Nat.add_sub_cancel_left]

/-- The steps of a stride that fits are at distinct indices. -/
public theorem _root_.ScalarArray.Stride.Fits.injOn {s : Stride} {N size : Nat} (hs : s.Fits N size)
    {lo hi : Nat} (hn : hi ≤ N) :
    ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → s.idx i = s.idx j → i = j :=
  fun _ _ h₁ _ _ h₂ e => hs.idx_inj (by lia) (by lia) e

/--
Two `modifyAt` at the same indices, distinct and in bounds, compose: the element at the step `i`
is mapped by `g i` and then `g' i`.
-/
public theorem modifyAt_modifyAt (a : Float64Array) (idx : Nat → Nat) {lo hi : Nat}
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j)
    (g g' : Nat → Float → Float) :
    (a.modifyAt idx lo hi g).modifyAt idx lo hi g' =
      a.modifyAt idx lo hi fun i v => g' i (g i v) := by
  apply ext_getElem (by simp)
  intro p hp _
  by_cases hc : ∃ i, lo ≤ i ∧ i < hi ∧ idx i = p
  · obtain ⟨i, h₁, h₂, rfl⟩ := hc
    rw [getElem_modifyAt_idx _ _ _ hinj h₁ h₂ hp, getElem_modifyAt_idx _ _ _ hinj h₁ h₂,
      getElem_modifyAt_idx _ _ _ hinj h₁ h₂]
  · have hne : ∀ i, lo ≤ i → i < hi → idx i ≠ p := fun i h₁ h₂ e => hc ⟨i, h₁, h₂, e⟩
    rw [getElem_modifyAt_of_forall_ne _ _ _ hne hp, getElem_modifyAt_of_forall_ne _ _ _ hne,
      getElem_modifyAt_of_forall_ne _ _ _ hne]

/--
Steps that each `modifyAt` the same indices, distinct and in bounds, by `G j` at step `j`, map
them by the left fold of the `G j` over `j < n`.
-/
public theorem iterRange_modifyAt (a : Float64Array) (idx : Nat → Nat) {lo hi : Nat}
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j) (n : Nat)
    (G : Nat → Nat → Float → Float) :
    iterRange (fun j c => c.modifyAt idx lo hi (G j)) 0 n a =
      a.modifyAt idx lo hi fun i v => Nat.fold n (fun j _ v => G j i v) v := by
  induction n with
  | zero =>
    rw [iterRange_self, modifyAt_congr a (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext v; simp), modifyAt_id]
  | succ n ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, modifyAt_modifyAt _ _ hinj]
    simp only [Nat.fold_succ]

/--
Steps that each `modifyAt` the same indices, distinct and in bounds, by `G j t` at step `j`, where
`t` is the element at the step `r j`, which the earlier steps leave unchanged, map them by the left
fold of the `G j t` over `j < n`, with `t` the element before the loop.
-/
public theorem iterRange_modifyAt_read (a : Float64Array) (idx : Nat → Nat) {hi : Nat}
    (hinj : ∀ i, 0 ≤ i → i < hi → ∀ j, 0 ≤ j → j < hi → idx i = idx j → i = j)
    (hlt : ∀ i, i < hi → idx i < a.size) (r : Nat → Nat) (n : Nat) (hr : ∀ j, j < n → r j < hi)
    (G : Nat → Float → Nat → Float → Float)
    (hG : ∀ j' j, j' < j → j < n → ∀ t v, G j' t (r j) v = v) :
    iterRange (fun j c => c.modifyAt idx 0 hi (G j c[idx (r j)]!)) 0 n a =
      a.modifyAt idx 0 hi fun i v => Nat.fold n (fun j _ v => G j a[idx (r j)]! i v) v := by
  induction n with
  | zero =>
    rw [iterRange_self, modifyAt_congr a (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext v; simp), modifyAt_id]
  | succ n ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (fun j hj => hr j (by lia))
      (fun j' j h₁ h₂ => hG j' j h₁ (by lia)), modifyAt_modifyAt _ _ hinj]
    have hrn := hr n (by lia)
    have hfix : ∀ k, k ≤ n → ∀ w, Nat.fold k (fun j _ v => G j a[idx (r j)]! (r n) v) w = w := by
      intro k
      induction k with
      | zero => intro _ w; exact Nat.fold_zero _ _
      | succ k ihk => intro hk w; rw [Nat.fold_succ, ihk (by lia), hG k n (by lia) (by lia)]
    have hread : (a.modifyAt idx 0 hi fun i v =>
        Nat.fold n (fun j _ v => G j a[idx (r j)]! i v) v)[idx (r n)]! = a[idx (r n)]! := by
      rw [getElem!_pos _ _ (by rw [size_modifyAt]; exact hlt _ hrn),
        getElem_modifyAt_idx _ _ _ hinj (Nat.zero_le _) hrn, hfix n (Nat.le_refl _),
        getElem!_pos a _ (hlt _ hrn)]
    rw [hread]
    simp only [Nat.fold_succ]

/--
The values that the steps of `iterRange_modifyAt_self` read: the element at the step `r j` of `a`
after the steps before `j`, which map it by `G j' (selfRead a idx r G j') (r j)`.
-/
@[expose] public def selfRead (a : Float64Array) (idx r : Nat → Nat)
    (G : Nat → Float → Nat → Float → Float) (j : Nat) : Float :=
  Nat.fold j (fun j' _hj v => G j' (selfRead a idx r G j') (r j) v) a[idx (r j)]!
termination_by j
decreasing_by exact _hj

/--
Steps that each `modifyAt` the same indices, distinct and in bounds, by `G j t` at step `j`, where
`t` is the element at the step `r j` when step `j` starts, map them by the left fold of the
`G j (selfRead a idx r G j)` over `j < n`.
-/
public theorem iterRange_modifyAt_self (a : Float64Array) (idx : Nat → Nat) {hi : Nat}
    (hinj : ∀ i, 0 ≤ i → i < hi → ∀ j, 0 ≤ j → j < hi → idx i = idx j → i = j)
    (hlt : ∀ i, i < hi → idx i < a.size) (r : Nat → Nat) (n : Nat) (hr : ∀ j, j < n → r j < hi)
    (G : Nat → Float → Nat → Float → Float) :
    iterRange (fun j c => c.modifyAt idx 0 hi (G j c[idx (r j)]!)) 0 n a =
      a.modifyAt idx 0 hi fun i v =>
        Nat.fold n (fun j _ v => G j (selfRead a idx r G j) i v) v := by
  induction n with
  | zero =>
    rw [iterRange_self, modifyAt_congr a (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext v; simp), modifyAt_id]
  | succ n ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (fun j hj => hr j (by lia)),
      modifyAt_modifyAt _ _ hinj]
    have hrn := hr n (by lia)
    have hread : (a.modifyAt idx 0 hi fun i v =>
        Nat.fold n (fun j _ v => G j (selfRead a idx r G j) i v) v)[idx (r n)]! =
          selfRead a idx r G n := by
      rw [getElem!_pos _ _ (by rw [size_modifyAt]; exact hlt _ hrn),
        getElem_modifyAt_idx _ _ _ hinj (Nat.zero_le _) hrn, selfRead,
        getElem!_pos a _ (hlt _ hrn)]
    rw [hread]
    simp only [Nat.fold_succ]

/-- `selfRead` is the element of `a` at a step `r j` that no step before `j` changes. -/
public theorem selfRead_eq_of_fix (a : Float64Array) (idx r : Nat → Nat)
    (G : Nat → Float → Nat → Float → Float) {j : Nat}
    (h : ∀ j', j' < j → ∀ t v, G j' t (r j) v = v) : selfRead a idx r G j = a[idx (r j)]! := by
  rw [selfRead]
  have : ∀ m, m ≤ j → ∀ w,
      Nat.fold m (fun j' (_ : j' < m) v => G j' (selfRead a idx r G j') (r j) v) w = w := by
    intro m
    induction m with
    | zero => intro _ w; exact Nat.fold_zero _ _
    | succ m ih => intro hm w; rw [Nat.fold_succ, ih (by lia), h m (by lia)]
  exact this j (Nat.le_refl _) _

/--
`modifyAt` at distinct indices in bounds maps each element by its value in `a`, which no other step
changes.
-/
public theorem modifyAt_eq_read (a : Float64Array) (idx : Nat → Nat) {lo hi : Nat}
    (hinj : ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi → idx i = idx j → i = j)
    (hlt : ∀ i, lo ≤ i → i < hi → idx i < a.size) (g : Nat → Float → Float) :
    a.modifyAt idx lo hi g = a.modifyAt idx lo hi fun i _ => g i a[idx i]! := by
  apply ext_getElem (by simp)
  intro p hp _
  by_cases hc : ∃ i, lo ≤ i ∧ i < hi ∧ idx i = p
  · obtain ⟨i, h₁, h₂, rfl⟩ := hc
    rw [getElem_modifyAt_idx _ _ _ hinj h₁ h₂ hp, getElem_modifyAt_idx _ _ _ hinj h₁ h₂,
      getElem!_pos a _ (hlt i h₁ h₂)]
  · have hne : ∀ i, lo ≤ i → i < hi → idx i ≠ p := fun i h₁ h₂ e => hc ⟨i, h₁, h₂, e⟩
    rw [getElem_modifyAt_of_forall_ne _ _ _ hne hp, getElem_modifyAt_of_forall_ne _ _ _ hne]

/--
The values that the steps of `iterRange_write` write: step `k` writes `H k` of the elements when it
starts, which are `writeRead a idx s H (s q)` at the steps `q` written before, at the step `s q`,
and those of `a` at the others.
-/
@[expose] public def writeRead (a : Float64Array) (idx s : Nat → Nat)
    (H : Nat → (Nat → Float) → Float) (k : Nat) : Float :=
  H k fun q => if _h : s q < k then writeRead a idx s H (s q) else a[idx q]!
termination_by k
decreasing_by exact _h

/--
Steps `k < N` that each write `H k` of the elements at the step `p k` of distinct indices in
bounds, where `p` is a bijection of `[0, hi)` with inverse `s` and `H` reads only the steps below
`hi`, write `writeRead a idx s H k` at the step `p k`.
-/
public theorem iterRange_write (a : Float64Array) (idx : Nat → Nat) {hi : Nat}
    (hinj : ∀ i, 0 ≤ i → i < hi → ∀ j, 0 ≤ j → j < hi → idx i = idx j → i = j)
    (hlt : ∀ i, i < hi → idx i < a.size) (p s : Nat → Nat) (hsp : ∀ k, k < hi → s (p k) = k)
    (hps : ∀ q, q < hi → p (s q) = q) (H : Nat → (Nat → Float) → Float)
    (hH : ∀ k, k < hi → ∀ get get', (∀ q, q < hi → get q = get' q) → H k get = H k get')
    {N : Nat} (hN : N ≤ hi) :
    iterRange (fun k c => c.modifyAt idx 0 hi fun i v =>
        if i = p k then H k (fun q => c[idx q]!) else v) 0 N a =
      a.modifyAt idx 0 hi fun i v => if s i < N then writeRead a idx s H (s i) else v := by
  induction N with
  | zero =>
    rw [iterRange_self, modifyAt_congr a (g' := fun _ v => v) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext v; simp), modifyAt_id]
  | succ N ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), modifyAt_modifyAt _ _ hinj]
    have hval : H N (fun q => (a.modifyAt idx 0 hi fun i v =>
        if s i < N then writeRead a idx s H (s i) else v)[idx q]!) = writeRead a idx s H N := by
      rw [writeRead]
      apply hH N (by lia)
      intro q hq
      rw [getElem!_pos _ _ (by rw [size_modifyAt]; exact hlt _ hq),
        getElem_modifyAt_idx _ _ _ hinj (Nat.zero_le _) hq, getElem!_pos a _ (hlt _ hq)]
      split <;> (try split) <;> rfl
    rw [hval]
    apply modifyAt_congr_fun
    intro i v _ hi'
    by_cases h₁ : i = p N
    · subst h₁
      rw [hsp N (by lia)]
      simp
    · have : s i ≠ N := fun e => h₁ (by rw [← e, hps i hi'])
      simp only [h₁, ↓reduceIte]
      split <;> (try split) <;> first | rfl | (exfalso; lia)

/--
Writing `t` at the step `j` of a stride, then updating the steps from `j + 1` to `n - 1` by `G`,
as the steps of the stride from `j + 1`, is a `modifyAt` over the steps `j ≤ i < n`: the
triangular update.
-/
public theorem set_modifyAt_succ (a : Float64Array) (s : Stride) {j n : Nat} (t : Float)
    (G : Nat → Float → Float) (hj : j < n) (p : Nat) (hp : p = s.idx j) (h : p < a.size) :
    (a.set p t h).modifyAt (s.shift (j + 1)).idx 0 (n - j - 1) G =
      a.modifyAt s.idx j n fun i v => if i = j then t else G (i - (j + 1)) v := by
  subst hp
  rw [set_eq_modifyAt a s.idx j t, modifyAt_shift, show j + 1 + (n - j - 1) = n by lia,
    modifyAt_split a s.idx (Nat.le_succ j) (show j + 1 ≤ n by lia)]
  have e : a.modifyAt s.idx j (j + 1) (fun i v => if i = j then t else G (i - (j + 1)) v) =
      a.modifyAt s.idx j (j + 1) fun _ _ => t :=
    modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ h₂ => by funext v; simp [show i = j by lia])
  rw [e]
  exact modifyAt_congr _ (fun _ _ _ => rfl) (fun i h₁ _ => by
    funext v; simp [show i ≠ j by lia])

/--
Writing `t` at the step `j` of a stride that fits, then updating the steps before `j` by `G`, is a
`modifyAt` over the steps `i ≤ j`: the triangular update from the end.
-/
public theorem set_modifyAt_pred (a : Float64Array) {s : Stride} {N : Nat}
    (hs : s.Fits N a.size) {j : Nat} (hj : j < N) (t : Float) (G : Nat → Float → Float)
    (p : Nat) (hp : p = s.idx j) (h : p < a.size) :
    (a.set p t h).modifyAt s.idx 0 j G =
      a.modifyAt s.idx 0 (j + 1) fun i v => if i = j then t else G i v := by
  subst hp
  rw [modifyAt_succ_of_injOn _ _ (Nat.zero_le _) _ (hs.injOn hj), set_eq_set!]
  simp only [↓reduceIte]
  exact modifyAt_congr _ (fun _ _ _ => rfl) (fun i _ h₂ => by
    funext v; simp [show i ≠ j by lia])

/-- Element `l < m` of a column window `o + l`, after a `modifyAt` of the window by `g`. -/
public theorem getElem!_modifyAt_col (b : Float64Array) (o m : Nat) (g : Nat → Float → Float)
    {l : Nat} (hl : l < m) :
    (b.modifyAt (Stride.mk o 1).idx 0 m g)[o + l]! =
      if o + l < b.size then g l b[o + l]! else default := by
  have e : (Stride.mk o 1).idx l = o + l := by simp [Stride.idx]
  split
  · rename_i h
    have hinj : ∀ i, 0 ≤ i → i < m → ∀ j, 0 ≤ j → j < m →
        (Stride.mk o 1).idx i = (Stride.mk o 1).idx j → i = j :=
      fun _ _ _ _ _ _ e' => by simp only [Stride.idx] at e'; lia
    have := getElem_modifyAt_idx b (Stride.mk o 1).idx g hinj (Nat.zero_le l) hl
      (by rw [size_modifyAt, e]; exact h)
    simp only [e] at this
    rw [getElem!_pos _ _ (by rw [size_modifyAt]; exact h), getElem!_pos b _ h, this]
  · rename_i h
    rw [getElem!_neg _ _ (by rw [size_modifyAt]; exact h)]

/-- An element outside the indices of a `modifyAt` is unchanged. -/
public theorem getElem!_modifyAt_of_ne (b : Float64Array) (idx : Nat → Nat) {lo hi : Nat}
    (g : Nat → Float → Float) {p : Nat} (hp : ∀ i, lo ≤ i → i < hi → idx i ≠ p) :
    (b.modifyAt idx lo hi g)[p]! = b[p]! := by
  by_cases h : p < b.size
  · rw [getElem!_pos _ p (by rw [size_modifyAt]; exact h), getElem!_pos b p h,
      getElem_modifyAt_of_forall_ne _ _ _ hp]
  · rw [getElem!_neg _ p (by rw [size_modifyAt]; exact h), getElem!_neg b p h]

/--
Steps that each write `G i c[idx i]! c[idx' i]!` at `idx i`, where the indices `idx'` that they
read are never written, are a `modifyAt` that reads the elements at `idx'` in the array before the
loop.
-/
public theorem iterRange_set!_read (a : Float64Array) (idx idx' : Nat → Nat)
    (G : Nat → Float → Float → Float) {lo hi : Nat}
    (hd : ∀ i, lo ≤ i → i < hi → ∀ i', lo ≤ i' → i' < hi → idx i ≠ idx' i') :
    iterRange (fun i c => c.set! (idx i) (G i c[idx i]! c[idx' i]!)) lo hi a =
      a.modifyAt idx lo hi fun i v => G i v a[idx' i]! := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), modifyAt_of_lt _ _ (by lia),
      ih _ (fun i h₁ h₂ i' h₃ h₄ => hd i (by lia) h₂ i' (by lia) h₄) (by lia)]
    apply modifyAt_congr_fun
    intro i v h₁ h₂
    have hne : idx lo ≠ idx' i := hd lo (Nat.le_refl _) (by lia) i (by lia) h₂
    by_cases hq : idx' i < a.size
    · rw [getElem!_set!_of_lt _ _ _ hq, ite_eq_right hne]
    · rw [getElem!_neg _ _ (by simpa using hq), getElem!_neg a _ hq]

/-! ## Maps that change only a set of indices -/

/--
`F` is local to the indices `U`: it keeps the size of the array, leaves the elements outside `U`
unchanged, and its elements in `U` depend only on the elements of its argument in `U`. The kernels
that work on several columns at a time are local to each column, so that they commute.
-/
@[expose] public def Local (U : Nat → Prop) (F : Float64Array → Float64Array) : Prop :=
  (∀ b, (F b).size = b.size) ∧ (∀ b p, ¬U p → (F b)[p]! = b[p]!) ∧
    ∀ b b', b.size = b'.size → (∀ p, U p → b[p]! = b'[p]!) → ∀ p, U p → (F b)[p]! = (F b')[p]!

/-- Arrays of the same size are equal if their elements are, by `getElem!`. -/
public theorem ext_getElem! {a b : Float64Array} (h : a.size = b.size)
    (h' : ∀ p, p < a.size → a[p]! = b[p]!) : a = b := by
  apply ext_getElem h
  intro p h₁ h₂
  rw [← getElem!_pos a p h₁, ← getElem!_pos b p h₂]
  exact h' p h₁

/-- Maps local to disjoint sets of indices commute. -/
public theorem Local.comm {U V : Nat → Prop} {F G : Float64Array → Float64Array} (hF : Local U F)
    (hG : Local V G) (hUV : ∀ p, U p → ¬V p) (b : Float64Array) : F (G b) = G (F b) := by
  apply ext_getElem! (by rw [hF.1, hG.1, hG.1, hF.1])
  intro p _
  by_cases hU : U p
  · rw [hG.2.1 _ _ (hUV p hU)]
    exact hF.2.2 _ _ (hG.1 b) (fun q hq => hG.2.1 _ _ (hUV q hq)) p hU
  · by_cases hV : V p
    · rw [hF.2.1 _ _ hU]
      exact (hG.2.2 (F b) b (hF.1 b) (fun q hq => hF.2.1 _ _ (fun h => hUV q h hq)) p hV).symm
    · rw [hF.2.1 _ _ hU, hG.2.1 _ _ hV, hG.2.1 _ _ hV, hF.2.1 _ _ hU]

/-- A map local to `U` is local to a larger set. -/
public theorem Local.mono {U U' : Nat → Prop} {F : Float64Array → Float64Array} (hF : Local U F)
    (h : ∀ p, U p → U' p) : Local U' F := by
  refine ⟨hF.1, fun b p hp => hF.2.1 b p (fun h' => hp (h p h')), ?_⟩
  intro b b' hs hb p hp
  by_cases hU : U p
  · exact hF.2.2 b b' hs (fun q hq => hb q (h q hq)) p hU
  · rw [hF.2.1 _ _ hU, hF.2.1 _ _ hU]; exact hb p hp

/-- The composition of maps local to `U` and `V` is local to their union. -/
public theorem Local.comp {U V : Nat → Prop} {F G : Float64Array → Float64Array} (hF : Local U F)
    (hG : Local V G) : Local (fun p => U p ∨ V p) (fun b => F (G b)) := by
  refine ⟨fun b => by rw [hF.1, hG.1], fun b p hp => ?_, ?_⟩
  · rw [hF.2.1 _ _ (fun h => hp (Or.inl h)), hG.2.1 _ _ (fun h => hp (Or.inr h))]
  · intro b b' hs hb
    have hG' : ∀ p, U p ∨ V p → (G b)[p]! = (G b')[p]! := by
      intro p hp
      by_cases hV : V p
      · exact hG.2.2 b b' hs (fun q hq => hb q (Or.inr hq)) p hV
      · rw [hG.2.1 _ _ hV, hG.2.1 _ _ hV]; exact hb p hp
    intro p hp
    by_cases hU : U p
    · exact hF.2.2 _ _ (by rw [hG.1, hG.1, hs]) (fun q hq => hG' q (Or.inl hq)) p hU
    · rw [hF.2.1 _ _ hU, hF.2.1 _ _ hU]; exact hG' p hp

/-- The identity is local to any set. -/
public theorem local_id (U : Nat → Prop) : Local U fun b => b :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ hb p hp => hb p hp⟩

/-- A loop whose steps are local to `U` is local to `U`. -/
public theorem Local.iterRange {U : Nat → Prop} {F : Nat → Float64Array → Float64Array}
    {lo hi : Nat}
    (hF : ∀ j, lo ≤ j → j < hi → Local U (F j)) : Local U (iterRange F lo hi) := by
  obtain ⟨d, hd⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo with
  | zero =>
    have e : ScalarArray.iterRange F lo hi = fun b => b :=
      funext fun b => iterRange_of_le _ (by lia) b
    rw [e]; exact local_id U
  | succ d ih =>
    have e : ScalarArray.iterRange F lo hi =
        fun b => ScalarArray.iterRange F (lo + 1) hi (F lo b) :=
      funext fun b => iterRange_of_lt _ (by lia) b
    rw [e]
    have := (ih (lo := lo + 1) (fun j h₁ h₂ => hF j (by lia) h₂) (by lia)).comp
      (hF lo (Nat.le_refl _) (by lia))
    exact this.mono fun p h => h.elim id id

/--
A loop whose step `j` is `F j` after `G j`, for steps local to disjoint sets, is the loop of `G`
followed by the loop of `F`.
-/
public theorem iterRange_comp_of_local {U V : Nat → Prop}
    {F G : Nat → Float64Array → Float64Array} {k : Nat} (hF : ∀ j, j < k → Local U (F j))
    (hG : ∀ j, j < k → Local V (G j))
    (hUV : ∀ p, U p → ¬V p) (b : Float64Array) :
    ScalarArray.iterRange (fun j c => F j (G j c)) 0 k b =
      ScalarArray.iterRange F 0 k (ScalarArray.iterRange G 0 k b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), iterRange_succ _ (Nat.zero_le _),
      iterRange_succ _ (Nat.zero_le _), ih (fun j hj => hF j (by lia)) (fun j hj => hG j (by lia)),
      (Local.iterRange (fun j _ hj => hF j (by lia))).comm (hG k (by lia)) hUV]

/-- The indices `o + i` for `i < m` of a column. -/
@[expose] public def colIdx (o m : Nat) (p : Nat) : Prop := o ≤ p ∧ p < o + m

/--
A loop over four columns `o₀ < o₁ < o₂ < o₃` that don't overlap, whose step `j` runs the steps
`j` of the four columns in turn, each local to its column, is the four loops of the columns, one
after the other.
-/
public theorem iterRange_four_cols {m k o₀ o₁ o₂ o₃ : Nat}
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃)
    {F₀ F₁ F₂ F₃ : Nat → Float64Array → Float64Array}
    (l₀ : ∀ j, j < k → Local (colIdx o₀ m) (F₀ j)) (l₁ : ∀ j, j < k → Local (colIdx o₁ m) (F₁ j))
    (l₂ : ∀ j, j < k → Local (colIdx o₂ m) (F₂ j)) (l₃ : ∀ j, j < k → Local (colIdx o₃ m) (F₃ j))
    (b : Float64Array) :
    ScalarArray.iterRange (fun j c => F₃ j (F₂ j (F₁ j (F₀ j c)))) 0 k b =
      ScalarArray.iterRange F₃ 0 k (ScalarArray.iterRange F₂ 0 k
        (ScalarArray.iterRange F₁ 0 k (ScalarArray.iterRange F₀ 0 k b))) := by
  have l₂₃ := fun j hj => (l₃ j hj).comp (l₂ j hj)
  have l₁₂₃ := fun j hj => (l₂₃ j hj).comp (l₁ j hj)
  rw [iterRange_comp_of_local (F := fun j c => F₃ j (F₂ j (F₁ j c))) l₁₂₃ l₀
      (fun p h h' => by simp only [colIdx] at h h'; lia),
    iterRange_comp_of_local (F := fun j c => F₃ j (F₂ j c)) l₂₃ l₁
      (fun p h h' => by simp only [colIdx] at h h'; lia),
    iterRange_comp_of_local l₃ l₂ (fun p h h' => by simp only [colIdx] at h h'; lia)]

/--
Four maps `S q`, each local to column `q`, followed by four maps `I q`, each local to column `q`,
are the four pairs `I q` after `S q`, column by column, for columns that don't overlap.
-/
public theorem four_cols_reorder {m o₀ o₁ o₂ o₃ : Nat}
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃)
    {S₀ S₁ S₂ S₃ I₀ I₁ I₂ I₃ : Float64Array → Float64Array}
    (s₁ : Local (colIdx o₁ m) S₁) (s₂ : Local (colIdx o₂ m) S₂) (s₃ : Local (colIdx o₃ m) S₃)
    (i₀ : Local (colIdx o₀ m) I₀) (i₁ : Local (colIdx o₁ m) I₁) (i₂ : Local (colIdx o₂ m) I₂)
    (b : Float64Array) :
    I₃ (I₂ (I₁ (I₀ (S₃ (S₂ (S₁ (S₀ b))))))) = I₃ (S₃ (I₂ (S₂ (I₁ (S₁ (I₀ (S₀ b))))))) := by
  rw [i₀.comm s₃ (fun p h h' => by simp only [colIdx] at h h'; lia),
    i₀.comm s₂ (fun p h h' => by simp only [colIdx] at h h'; lia),
    i₀.comm s₁ (fun p h h' => by simp only [colIdx] at h h'; lia),
    i₁.comm s₃ (fun p h h' => by simp only [colIdx] at h h'; lia),
    i₁.comm s₂ (fun p h h' => by simp only [colIdx] at h h'; lia),
    i₂.comm s₃ (fun p h h' => by simp only [colIdx] at h h'; lia)]

/--
A map that writes `T b` at the index `o` in `U`, for a value `T b` that depends only on the
elements of `b` in `U`, is local to `U`.
-/
public theorem local_set! {U : Nat → Prop} (o : Nat) (ho : U o) (T : Float64Array → Float)
    (hT : ∀ b b', b.size = b'.size → (∀ p, U p → b[p]! = b'[p]!) → T b = T b') :
    Local U fun b => b.set! o (T b) := by
  refine ⟨fun b => by simp, fun b p hp => ?_, ?_⟩
  · by_cases hq : p < b.size
    · rw [getElem!_set!_of_lt _ _ _ hq, ite_eq_right (fun e => hp (by rw [← e]; exact ho))]
    · rw [getElem!_neg _ _ (by simpa using hq), getElem!_neg b _ hq]
  · intro b b' hs hb p hp
    by_cases hq : p < b.size
    · rw [getElem!_set!_of_lt _ _ _ hq, getElem!_set!_of_lt _ _ _ (hs ▸ hq), hT b b' hs hb, hb p hp]
    · rw [getElem!_neg _ _ (by simpa using hq), getElem!_neg _ _ (by simpa [← hs] using hq)]

/-- `modifyAt` on the indices `o + i` for `i < m`, with a function of each old element. -/
public theorem local_modifyAt_col (o m : Nat) (g : Nat → Float → Float) :
    Local (colIdx o m) fun b => b.modifyAt (Stride.mk o 1).idx 0 m g := by
  refine ⟨fun b => by simp, fun b p hp => ?_, ?_⟩
  · exact getElem!_modifyAt_of_ne _ _ _ fun i _ hi e =>
      hp (by simp [Stride.idx, colIdx] at e ⊢; lia)
  · intro b b' hs hb p hp
    simp only [colIdx] at hp
    obtain ⟨l, rfl⟩ : ∃ l, p = o + l := ⟨p - o, by lia⟩
    rw [getElem!_modifyAt_col _ _ _ _ (by lia), getElem!_modifyAt_col _ _ _ _ (by lia), hs,
      hb _ (by simp only [colIdx]; lia)]

/-- The column at `o`, with stride `1`, scaled by `α`. -/
@[expose] public def colScale (α : Float) (o m : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt (Stride.mk o 1).idx 0 m fun _ v => α * v

public theorem local_colScale (α : Float) (o m : Nat) : Local (colIdx o m) (colScale α o m) :=
  local_modifyAt_col o m _

@[simp] public theorem size_colScale (α : Float) (o m : Nat) (c : Float64Array) :
    (colScale α o m c).size = c.size :=
  (local_colScale α o m).1 c

/-- `iterRange` of a map of a variable is `Nat.fold`. -/
public theorem iterRange_eq_fold {β : Type u} (f : Nat → β → β) (k : Nat) (x : β) :
    ScalarArray.iterRange f 0 k x = Nat.fold k (fun i _ s => f i s) x := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/--
Runs a loop of the `inplace` notation with four `Float` variables whose steps only read the array:
step `j` maps the variables by `f₀ j` to `f₃ j`. The loop maps them by the `iterRange` of these
maps, then runs `k`.
-/
public theorem run_forIn4From_read {N : Nat} {γ : Type} (lo hi j₀ : USize)
    (hlo : lo.toNat ≤ j₀.toNat) (i₀ i₁ i₂ i₃ : Float)
    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →
      (Float → Float → Float → Float → InPlace.Tail N γ) →
        Float → Float → Float → Float → InPlace.Tail N γ)
    (k : Float → Float → Float → Float → InPlace.Tail N γ)
    (f₀ f₁ f₂ f₃ : Nat → Float → Float)
    (a : Float64Array) (h : a.size = N)
    (hbody : ∀ j hl hj next s₀ s₁ s₂ s₃, (body j hl hj next s₀ s₁ s₂ s₃).run a h =
      (next (f₀ j.toNat s₀) (f₁ j.toNat s₁) (f₂ j.toNat s₂) (f₃ j.toNat s₃)).run a h) :
    (InPlace.Tail.forIn4From lo hi j₀ hlo i₀ i₁ i₂ i₃ body k).run a h =
      (k (ScalarArray.iterRange f₀ j₀.toNat hi.toNat i₀)
        (ScalarArray.iterRange f₁ j₀.toNat hi.toNat i₁)
        (ScalarArray.iterRange f₂ j₀.toNat hi.toNat i₂)
        (ScalarArray.iterRange f₃ j₀.toNat hi.toNat i₃)).run a h := by
  obtain ⟨d, hd⟩ : ∃ d, hi.toNat - j₀.toNat = d := ⟨_, rfl⟩
  induction d generalizing j₀ i₀ i₁ i₂ i₃ with
  | zero =>
    rw [InPlace.Tail.forIn4From_eq, dite_eq_right (by rw [USize.lt_iff_toNat_lt]; lia),
      iterRange_of_le _ (by lia), iterRange_of_le _ (by lia), iterRange_of_le _ (by lia),
      iterRange_of_le _ (by lia)]
  | succ d ih =>
    have hj : j₀ < hi := by rw [USize.lt_iff_toNat_lt]; lia
    have e : (j₀ + 1).toNat = j₀.toNat + 1 := by grind
    rw [InPlace.Tail.forIn4From_eq, dite_eq_left hj, hbody j₀ hlo hj, ih _ _ _ _ _ _ (by lia),
      iterRange_of_lt _ (show j₀.toNat < hi.toNat by lia) i₀,
      iterRange_of_lt _ (show j₀.toNat < hi.toNat by lia) i₁,
      iterRange_of_lt _ (show j₀.toNat < hi.toNat by lia) i₂,
      iterRange_of_lt _ (show j₀.toNat < hi.toNat by lia) i₃, e]

end BLAS.Float64
