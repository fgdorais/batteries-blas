/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Trmv
public import BLAS.Float64.Level2
import all BLAS.Internal

/-!
# Symmetric matrix-vector product

`Mat.symv uplo α A x β y` computes `α * A * x + β * y` for a symmetric matrix `A`, stored in its
triangle `uplo`, over `y`, by the loops of the reference BLAS: it first scales `y` by `β` (setting
it to `0` when `β = 0`), and then, for each column `j` of the triangle, adds `α * x[j]` times the
column to the other elements of `y`, and to `y[j]` the diagonal term and `α` times the dot product
of the column with `x`. Each element of `y` gets these terms in the order of the loops.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {n : Nat}

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

/-- Distinct steps `i < j < n` of a vector are at distinct indices. -/
private theorem idx_ne (y : Vec n) {i j : Nat} (hi : i < j) (hj : j < n) :
    y.off + y.inc * i ≠ y.off + y.inc * j := fun e => by
  have := y.fits.injOn (lo := 0) (Nat.le_refl _) i (Nat.zero_le _) (by lia) j (Nat.zero_le _) hj e
  lia

/-- `y.data` scaled by `β`, in place when it is not shared. -/
public def symvScale (β : Float) (y : Vec n) (hs : y.data.size < USize.size) : Float64Array :=
  have hnu : n.toUSize.toNat = n := y.toNat_toUSize hs
  let a := y.data
  let o := y.off.toUSize
  let c := y.inc.toUSize
  inplace a do
    for i in 0...n.toUSize do
      have hk : (o + c * i).toNat < a.size := y.toNat_index_lt hs (by lia)
      a[o + c * i] := betaMul β a[o + c * i]

public theorem symvScale_eq (β : Float) (y : Vec n) (hs : y.data.size < USize.size) :
    symvScale β y hs = y.data.modifyAt y.stride.idx 0 n fun _ v => betaMul β v := by
  unfold symvScale
  have he := y.loop_idx hs
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_modify (G := fun _ v => betaMul β v) (he := he)
    (hg := fun _ _ _ _ => rfl)]
  simp only [Tail.run_done, USize.toNat_zero, y.toNat_toUSize hs]

/-! ## The upper triangle -/

/-- The dot product of column `j` of the upper triangle, above the diagonal, with `x`. -/
@[expose] public def symvUpperDot (A : Mat n n) (x : Vec n) (j : Nat) : Float :=
  Nat.fold j (fun k _ s => s + A.data[A.off + A.ld * j + k]! * x.data[x.off + x.inc * k]!) 0

/--
The step `j` of the upper product: add `α * x[j]` times column `j` of `A` to the elements above
it, and the diagonal term and `α` times `symvUpperDot A x j` to element `j`.
-/
@[expose] public def symvUpperStep (α : Float) (A : Mat n n) (x y : Vec n) (j : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt y.stride.idx 0 (j + 1) fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! +
        α * symvUpperDot A x j
    else v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The step `j` of the upper product updates the elements above `j`, and then element `j`. -/
private theorem symvUpperStep_eq (α : Float) (A : Mat n n) (x y : Vec n) {j : Nat}
    (hj : j < n) (c : Float64Array) :
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

/-- The update of element `i` by the step `j` of the upper product. -/
private def symvUpperFn (α : Float) (A : Mat n n) (x : Vec n) (j i : Nat) (v : Float) :
    Float :=
  if i = j then
    v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! + α * symvUpperDot A x j
  else v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The steps `J` to `J + k - 1` of the upper product update each element by those steps. -/
private theorem iterRange_symvUpperStep_from (α : Float) (A : Mat n n) (x y : Vec n)
    (c : Float64Array) (hc : c.size = y.data.size) {J : Nat} :
    ∀ k, J + k ≤ n → iterRange (symvUpperStep α A x y) J (J + k) c =
      c.modifyAt y.stride.idx 0 n fun i v =>
        Nat.fold k (fun r _ v => if i < J + r + 1 then symvUpperFn α A x (J + r) i v else v) v := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.add_zero, iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ k ih =>
    intro hk
    rw [← Nat.add_assoc, iterRange_succ _ (Nat.le_add_right _ _), ih (by lia),
      show symvUpperStep α A x y (J + k) = fun c =>
        c.modifyAt y.stride.idx 0 (J + k + 1) (symvUpperFn α A x (J + k)) from rfl]
    dsimp only
    rw [modifyAt_widen (lo := 0) (hi := J + k + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.le_refl _)
        (Nat.zero_le _) (by lia), modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ _
    simp only [Nat.fold_succ, Nat.zero_le, true_and]

/--
The steps `J` to `J + 3` of the upper product: the elements above `J` get the four column terms,
and the elements `J` to `J + 3` are finished in the order of the steps.
-/
private theorem iterRange_symvUpperStep_four (α : Float) (A : Mat n n) (x y : Vec n)
    (c : Float64Array) (hc : c.size = y.data.size) {J : Nat} (hJ : J + 3 < n) :
    let t := fun r => α * x.data[x.off + x.inc * (J + r)]!
    let a := fun i r => A.data[A.off + A.ld * (J + r) + i]!
    let v := fun r => c[y.off + y.inc * (J + r)]!
    iterRange (symvUpperStep α A x y) J (J + 4) c =
      ((((c.modifyAt (fun i => y.off + y.inc * i) 0 J fun i w =>
            (((w + t 0 * a i 0) + t 1 * a i 1) + t 2 * a i 2) + t 3 * a i 3).set!
          (y.off + y.inc * J) ((((v 0 + t 0 * a J 0 + α * symvUpperDot A x J) +
            t 1 * a J 1) + t 2 * a J 2) + t 3 * a J 3)).set!
          (y.off + y.inc * (J + 1)) (((v 1 + t 1 * a (J + 1) 1 + α * symvUpperDot A x (J + 1)) +
            t 2 * a (J + 1) 2) + t 3 * a (J + 1) 3)).set!
          (y.off + y.inc * (J + 2)) ((v 2 + t 2 * a (J + 2) 2 + α * symvUpperDot A x (J + 2)) +
            t 3 * a (J + 2) 3)).set!
        (y.off + y.inc * (J + 3)) (v 3 + t 3 * a (J + 3) 3 + α * symvUpperDot A x (J + 3)) := by
  intro t a v
  have e : y.stride.idx = fun i => y.off + y.inc * i := rfl
  rw [iterRange_symvUpperStep_from α A x y c hc 4 (by lia), e,
    modifyAt_split _ _ (Nat.zero_le (J + 4)) (by lia : J + 4 ≤ n),
    modifyAt_congr_fun _ _ (lo := J + 4) (g' := fun _ v => v) (fun i w h _ => by
      simp only [Nat.fold_succ, Nat.fold_zero, show ¬i < J + 0 + 1 by lia,
        show ¬i < J + 1 + 1 by lia, show ¬i < J + 2 + 1 by lia, show ¬i < J + 3 + 1 by lia,
        ite_false]), modifyAt_id,
    show J + 4 = J + 3 + 1 from rfl, modifyAt_succ _ _ (by lia),
    show J + 3 = J + 2 + 1 from rfl, modifyAt_succ _ _ (by lia),
    show J + 2 = J + 1 + 1 from rfl, modifyAt_succ _ _ (by lia), modifyAt_succ _ _ (by lia),
    show J + 1 + 1 + 1 = J + 3 from rfl, show J + 1 + 1 = J + 2 from rfl,
    modifyAt_congr_fun _ _ (lo := 0) (hi := J) (g' := fun i w =>
      (((w + t 0 * a i 0) + t 1 * a i 1) + t 2 * a i 2) + t 3 * a i 3) (fun i w _ hi => by
        simp (disch := lia) only [Nat.fold_succ, Nat.fold_zero, symvUpperFn, ite_eq_left,
          ite_eq_right, t, a, Nat.add_zero])]
  simp (disch := first
    | exact idx_ne y (by lia) (by lia)
    | exact (idx_ne y (by lia) (by lia)).symm
    | exact fun i _ hi => idx_ne y (by lia) (by lia))
    only [getElem!_set!_ne, getElem!_modifyAt_of_ne]
  simp (disch := lia) only [Nat.fold_succ, Nat.fold_zero, symvUpperFn, ite_eq_left,
    ite_eq_right, t, a, v, Nat.add_zero]

/--
The loops of the upper product on the array `c` of `y`, already scaled by `β`: four columns per
sweep, then the rest one at a time.
-/
public def symvUpperData (α : Float) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) : Float64Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  let q4 := nu / 4
  have hq4 : q4.toNat = n / 4 := by simp only [q4, nu, USize.toNat_div, hnu]; simp
  inplace c do
    for g in 0...q4 do
      have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
      have j₀ : (4 * g).toNat = 4 * g.toNat := by grind
      have j₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
      have j₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
      have j₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
      let A' := fun (i j : USize) (hi : i.toNat < n) (hj : j.toNat < n) =>
        A.uget ao al rfl rfl hs.1 i j hi hj
      let x' := fun (i : USize) (hi : i.toNat < n) => x.uget xo xc rfl rfl hs.2.1 i hi
      let t₀ := α * x' (4 * g) (by lia)
      let t₁ := α * x' (4 * g + 1) (by lia)
      let t₂ := α * x' (4 * g + 2) (by lia)
      let t₃ := α * x' (4 * g + 3) (by lia)
      for i in 0...(4 * g) with (s₀ := 0) (s₁ := 0) (s₂ := 0) (s₃ := 0) do
        have hi : i.toNat < n := by lia
        have hk : (o + cc * i).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let xi := x' i hi
        let p₀ := A' i (4 * g) hi (by lia)
        let p₁ := A' i (4 * g + 1) hi (by lia)
        let p₂ := A' i (4 * g + 2) hi (by lia)
        let p₃ := A' i (4 * g + 3) hi (by lia)
        c[o + cc * i] := (((c[o + cc * i] + t₀ * p₀) + t₁ * p₁) + t₂ * p₂) + t₃ * p₃
        s₀ := s₀ + p₀ * xi
        s₁ := s₁ + p₁ * xi
        s₂ := s₂ + p₂ * xi
        s₃ := s₃ + p₃ * xi
      have k₀ : (o + cc * (4 * g)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have k₁ : (o + cc * (4 * g + 1)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have k₂ : (o + cc * (4 * g + 2)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have k₃ : (o + cc * (4 * g + 3)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      let v₀ := c[o + cc * (4 * g)]
      let v₁ := c[o + cc * (4 * g + 1)]
      let v₂ := c[o + cc * (4 * g + 2)]
      let v₃ := c[o + cc * (4 * g + 3)]
      let a01 := A' (4 * g) (4 * g + 1) (by lia) (by lia)
      let a02 := A' (4 * g) (4 * g + 2) (by lia) (by lia)
      let a03 := A' (4 * g) (4 * g + 3) (by lia) (by lia)
      let a12 := A' (4 * g + 1) (4 * g + 2) (by lia) (by lia)
      let a13 := A' (4 * g + 1) (4 * g + 3) (by lia) (by lia)
      let a23 := A' (4 * g + 2) (4 * g + 3) (by lia) (by lia)
      let x₀ := x' (4 * g) (by lia)
      let x₁ := x' (4 * g + 1) (by lia)
      let x₂ := x' (4 * g + 2) (by lia)
      c[o + cc * (4 * g)] := ((((v₀ + t₀ * A' (4 * g) (4 * g) (by lia) (by lia)) + α * s₀) +
        t₁ * a01) + t₂ * a02) + t₃ * a03
      c[o + cc * (4 * g + 1)] := (((v₁ + t₁ * A' (4 * g + 1) (4 * g + 1) (by lia) (by lia)) +
        α * (s₁ + a01 * x₀)) + t₂ * a12) + t₃ * a13
      c[o + cc * (4 * g + 2)] := ((v₂ + t₂ * A' (4 * g + 2) (4 * g + 2) (by lia) (by lia)) +
        α * ((s₂ + a02 * x₀) + a12 * x₁)) + t₃ * a23
      c[o + cc * (4 * g + 3)] := (v₃ + t₃ * A' (4 * g + 3) (4 * g + 3) (by lia) (by lia)) +
        α * (((s₃ + a03 * x₀) + a13 * x₁) + a23 * x₂)
    for j in 4 * q4...nu do
      have hjn : j.toNat < n := by lia
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      for i in 0...j with (s := 0) do
        have hi : i.toNat < n := Nat.lt_trans (by assumption) hjn
        have hk : (o + cc * i).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := A.uget ao al rfl rfl hs.1 i j hi hjn
        c[o + cc * i] := c[o + cc * i] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 i hi
      have hk : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      c[o + cc * j] := c[o + cc * j] + t * A.uget ao al rfl rfl hs.1 j j hjn hjn + α * s

public theorem symvUpperData_eq_iterRange (α : Float) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    symvUpperData α A x y hs o cc ho hcc c hc = iterRange (symvUpperStep α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  have hq4 : (n.toUSize / 4).toNat = n / 4 := by simp only [USize.toNat_div, hnu]; simp
  have h4q : (4 * (n.toUSize / 4)).toNat = 4 * (n / 4) := by grind
  have hF : ∀ j (b : Float64Array), (symvUpperStep α A x y j b).size = b.size :=
    fun _ _ => by unfold symvUpperStep; exact size_modifyAt _ _ _ _ _
  subst ho hcc
  unfold symvUpperData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit
    (F := fun g b => iterRange (symvUpperStep α A x y) (4 * g) (4 * g + 4) b)
    (hF := fun _ _ => size_iterRange _ hF _ _ _)]
  · rw [Tail.run_forInFrom_unit (F := symvUpperStep α A x y) (hF := hF)]
    · simp only [Tail.run_done, hq4, h4q, hnu, USize.toNat_zero]
      rw [iterRange_four, ← iterRange_split _ (Nat.zero_le _) (by lia)]
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
  · intro g _ hg next a h
    rw [hq4] at hg
    have hg4 : 4 * g.toNat + 3 < n := by lia
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
    have j₀ : (4 * g).toNat = 4 * g.toNat := by grind
    have j₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
    have j₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
    have j₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
    have t₀ := y.toNat_index hs.2.2 (i := 4 * g) (by lia)
    have t₁ := y.toNat_index hs.2.2 (i := 4 * g + 1) (by lia)
    have t₂ := y.toNat_index hs.2.2 (i := 4 * g + 2) (by lia)
    have t₃ := y.toNat_index hs.2.2 (i := 4 * g + 3) (by lia)
    rw [j₀] at t₀
    rw [j₁] at t₁
    rw [j₂] at t₂
    rw [j₃] at t₃
    let J := 4 * g.toNat
    let H := fun i w =>
      (((w + α * x.data[x.off + x.inc * (J + 0)]! * A.data[A.off + A.ld * (J + 0) + i]!) +
        α * x.data[x.off + x.inc * (J + 1)]! * A.data[A.off + A.ld * (J + 1) + i]!) +
        α * x.data[x.off + x.inc * (J + 2)]! * A.data[A.off + A.ld * (J + 2) + i]!) +
        α * x.data[x.off + x.inc * (J + 3)]! * A.data[A.off + A.ld * (J + 3) + i]!
    simp only [Tail.forIn4_eq]
    rw [run_forIn4From_modify
      (f₀ := fun i s => s + A.data[A.off + A.ld * (J + 0) + i]! * x.data[x.off + x.inc * i]!)
      (f₁ := fun i s => s + A.data[A.off + A.ld * (J + 1) + i]! * x.data[x.off + x.inc * i]!)
      (f₂ := fun i s => s + A.data[A.off + A.ld * (J + 2) + i]! * x.data[x.off + x.inc * i]!)
      (f₃ := fun i s => s + A.data[A.off + A.ld * (J + 3) + i]! * x.data[x.off + x.inc * i]!)
      (F := fun i b => b.set! (y.off + y.inc * i) (H i b[y.off + y.inc * i]!))
      (hF := fun _ _ => by simp)]
    · simp only [Tail.run_readThen, Tail.run_writeThen, USize.toNat_zero, j₀]
      apply run_congr
      simp only [set_eq_set!, getElem_eq_getElem!, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, t₀, t₁, t₂, t₃, j₀, j₁, j₂, j₃]
      rw [iterRange_set!_self, iterRange_symvUpperStep_four α A x y a (h.trans hc) hg4]
      simp (disch := exact fun i _ hi => idx_ne y (by lia) (by lia)) only [iterRange_eq_fold,
        symvUpperDot, Nat.fold_succ, Nat.add_zero, H, J, getElem!_modifyAt_of_ne]
    · intro i _ hi next' s₀ s₁ s₂ s₃ b hb
      rw [j₀] at hi
      have hq := y.toNat_index hs.2.2 (i := i) (by lia)
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, hq, j₀, j₁, j₂, j₃, getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/-- The value of element `i` of the upper product, from its value `v` after the scaling. -/
@[expose] public def symvUpperAt (α : Float) (A : Mat n n) (x : Vec n) (i : Nat) (v : Float) :
    Float :=
  Nat.fold (n - 1 - i) (fun t _ s =>
      s + α * x.data[x.off + x.inc * (i + 1 + t)]! * A.data[A.off + A.ld * (i + 1 + t) + i]!)
    (v + α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i + i]! + α * symvUpperDot A x i)

/--
After the steps `l < j`, the elements `i < j` have their diagonal term, their dot product and the
terms `l < j`, and the others are unchanged.
-/
theorem iterRange_symvUpperStep (α : Float) (A : Mat n n) (x y : Vec n) (c : Float64Array)
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
public theorem symvUpperData_eq (α : Float) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    symvUpperData α A x y hs o cc ho hcc c hc = c.modifyAt y.stride.idx 0 n (symvUpperAt α A x) := by
  rw [symvUpperData_eq_iterRange, iterRange_symvUpperStep α A x y c hc (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [hi, ite_true, symvUpperAt]

/-! ## The lower triangle -/

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

/-- The dot product of column `j` of the lower triangle, below the diagonal, with `x`. -/
@[expose] public def symvLowerDot (A : Mat n n) (x : Vec n) (j : Nat) : Float :=
  Nat.fold (n - 1 - j) (fun t _ s =>
    s + A.data[A.off + A.ld * j + (j + 1 + t)]! * x.data[x.off + x.inc * (j + 1 + t)]!) 0

/--
The step `j` of the lower product: add `α * x[j]` times column `j` of `A` to the elements below
it, and the diagonal term and `α` times `symvLowerDot A x j` to element `j`.
-/
@[expose] public def symvLowerStep (α : Float) (A : Mat n n) (x y : Vec n) (j : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt y.stride.idx j n fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! +
        α * symvLowerDot A x j
    else v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The step `j` of the lower product updates the elements below `j`, and then element `j`. -/
private theorem symvLowerStep_eq (α : Float) (A : Mat n n) (x y : Vec n) {j : Nat}
    (hj : j < n) (c : Float64Array) (hc : c.size = y.data.size) :
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

/-- The update of element `i` by the step `j` of the lower product. -/
private def symvLowerFn (α : Float) (A : Mat n n) (x : Vec n) (j i : Nat) (v : Float) :
    Float :=
  if i = j then
    v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + j]! + α * symvLowerDot A x j
  else v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!

/-- The steps `J` to `J + k - 1` of the lower product update each element by those steps. -/
private theorem iterRange_symvLowerStep_from (α : Float) (A : Mat n n) (x y : Vec n)
    (c : Float64Array) (hc : c.size = y.data.size) {J : Nat} :
    ∀ k, J + k ≤ n → iterRange (symvLowerStep α A x y) J (J + k) c =
      c.modifyAt y.stride.idx 0 n fun i v =>
        Nat.fold k (fun r _ v => if J + r ≤ i then symvLowerFn α A x (J + r) i v else v) v := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.add_zero, iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ k ih =>
    intro hk
    rw [← Nat.add_assoc, iterRange_succ _ (Nat.le_add_right _ _), ih (by lia),
      show symvLowerStep α A x y (J + k) = fun c =>
        c.modifyAt y.stride.idx (J + k) n (symvLowerFn α A x (J + k)) from rfl]
    dsimp only
    rw [modifyAt_widen (lo := J + k) (hi := n) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _)
        (by lia) (Nat.le_refl _), modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [Nat.fold_succ, hi, and_true]

/--
The steps `J` to `J + 3` of the lower product: the elements `J` to `J + 3` are finished in the
order of the steps, and the elements below `J + 3` get the four column terms.
-/
private theorem iterRange_symvLowerStep_four (α : Float) (A : Mat n n) (x y : Vec n)
    (c : Float64Array) (hc : c.size = y.data.size) {J : Nat} (hJ : J + 3 < n) :
    let t := fun r => α * x.data[x.off + x.inc * (J + r)]!
    let a := fun i r => A.data[A.off + A.ld * (J + r) + i]!
    let v := fun r => c[y.off + y.inc * (J + r)]!
    iterRange (symvLowerStep α A x y) J (J + 4) c =
      ((((c.modifyAt (fun l => y.off + y.inc * (J + 4 + l)) 0 (n - 4 - J) fun l w =>
            (((w + t 0 * a (J + 4 + l) 0) + t 1 * a (J + 4 + l) 1) + t 2 * a (J + 4 + l) 2) +
              t 3 * a (J + 4 + l) 3).set!
          (y.off + y.inc * J) (v 0 + t 0 * a J 0 + α * symvLowerDot A x J)).set!
          (y.off + y.inc * (J + 1))
            ((v 1 + t 0 * a (J + 1) 0) + t 1 * a (J + 1) 1 + α * symvLowerDot A x (J + 1))).set!
          (y.off + y.inc * (J + 2)) (((v 2 + t 0 * a (J + 2) 0) + t 1 * a (J + 2) 1) +
            t 2 * a (J + 2) 2 + α * symvLowerDot A x (J + 2))).set!
        (y.off + y.inc * (J + 3)) ((((v 3 + t 0 * a (J + 3) 0) + t 1 * a (J + 3) 1) +
          t 2 * a (J + 3) 2) + t 3 * a (J + 3) 3 + α * symvLowerDot A x (J + 3)) := by
  intro t a v
  have e : y.stride.idx = fun i => y.off + y.inc * i := rfl
  have e' : (fun l => y.off + y.inc * (J + 4 + l)) = (y.stride.shift (J + 4)).idx := by
    funext l; rw [Stride.idx_shift]; rfl
  rw [e', modifyAt_shift, show J + 4 + (n - 4 - J) = n by lia,
    iterRange_symvLowerStep_from α A x y c hc 4 (by lia), e,
    modifyAt_split _ _ (Nat.zero_le J) (by lia : J ≤ n),
    modifyAt_congr_fun _ _ (lo := 0) (hi := J) (g' := fun _ v => v) (fun i w _ h => by
      simp only [Nat.fold_succ, Nat.fold_zero, show ¬J + 0 ≤ i by lia,
        show ¬J + 1 ≤ i by lia, show ¬J + 2 ≤ i by lia, show ¬J + 3 ≤ i by lia,
        ite_false]), modifyAt_id,
    modifyAt_split _ _ (show J ≤ J + 4 by lia) (by lia : J + 4 ≤ n),
    modifyAt_of_lt (lo := J) (hi := J + 4) _ _ (by lia),
    modifyAt_of_lt (lo := J + 1) (hi := J + 4) _ _ (by lia),
    modifyAt_of_lt (lo := J + 1 + 1) (hi := J + 4) _ _ (by lia),
    modifyAt_of_lt (lo := J + 1 + 1 + 1) (hi := J + 4) _ _ (by lia),
    modifyAt_of_le (lo := J + 1 + 1 + 1 + 1) (hi := J + 4) _ _ (by lia),
    show J + 1 + 1 + 1 = J + 3 from rfl, show J + 1 + 1 = J + 2 from rfl]
  simp (disch := first
    | exact idx_ne y (by lia) (by lia)
    | exact (idx_ne y (by lia) (by lia)).symm
    | exact fun i h₁ h₂ => (idx_ne y (by lia) h₂).symm) only [getElem!_set!_ne, modifyAt_set!']
  rw [modifyAt_congr_fun _ _ (lo := J + 4) (hi := n) (g' := fun i w =>
      (((w + t 0 * a (J + 4 + (i - (J + 4))) 0) + t 1 * a (J + 4 + (i - (J + 4))) 1) +
        t 2 * a (J + 4 + (i - (J + 4))) 2) + t 3 * a (J + 4 + (i - (J + 4))) 3) (fun i w h _ => by
      rw [show J + 4 + (i - (J + 4)) = i by lia]
      simp (disch := lia) only [Nat.fold_succ, Nat.fold_zero, symvLowerFn, ite_eq_left,
        ite_eq_right, t, a, Nat.add_zero])]
  simp (disch := lia) only [Nat.fold_succ, Nat.fold_zero, symvLowerFn, ite_eq_left,
    ite_eq_right, t, a, v, Nat.add_zero]

/--
The dot products of the columns `J` to `J + 3` of the lower triangle: the terms of the rows down
to `J + 3`, then the others.
-/
private theorem symvLowerDot_four (A : Mat n n) (x : Vec n) {J : Nat} (hJ : J + 3 < n) :
    let F := fun r l s => s + A.data[A.off + A.ld * (J + r) + (J + 4 + l)]! *
      x.data[x.off + x.inc * (J + 4 + l)]!
    let p := fun i r => A.data[A.off + A.ld * (J + r) + (J + i)]! * x.data[x.off + x.inc * (J + i)]!
    symvLowerDot A x J = Nat.fold (n - 4 - J) (fun l _ s => F 0 l s)
        (((0 + p 1 0) + p 2 0) + p 3 0) ∧
      symvLowerDot A x (J + 1) = Nat.fold (n - 4 - J) (fun l _ s => F 1 l s)
        ((0 + p 2 1) + p 3 1) ∧
      symvLowerDot A x (J + 2) = Nat.fold (n - 4 - J) (fun l _ s => F 2 l s) (0 + p 3 2) ∧
      symvLowerDot A x (J + 3) = Nat.fold (n - 4 - J) (fun l _ s => F 3 l s) 0 := by
  intro F p
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold symvLowerDot
    rw [fold_split 3 (n - 4 - J) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, F, p]
    congr 1
    funext l hl s; congr 4 <;> lia
  · unfold symvLowerDot
    rw [fold_split 2 (n - 4 - J) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, F, p]
    congr 1
    funext l hl s; congr 4 <;> lia
  · unfold symvLowerDot
    rw [fold_split 1 (n - 4 - J) _ _ (by lia)]
    simp only [Nat.fold_succ, Nat.fold_zero, F, p]
    congr 1
    funext l hl s; congr 4 <;> lia
  · unfold symvLowerDot
    rw [Nat.fold_congr (show n - 1 - (J + 3) = n - 4 - J by lia)]

/--
The loops of the lower product on the array `c` of `y`, already scaled by `β`: four columns per
sweep, then the rest one at a time.
-/
public def symvLowerData (α : Float) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) : Float64Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  let q4 := nu / 4
  have hq4 : q4.toNat = n / 4 := by simp only [q4, nu, USize.toNat_div, hnu]; simp
  inplace c do
    for g in 0...q4 do
      have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
      have j₀ : (4 * g).toNat = 4 * g.toNat := by grind
      have j₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
      have j₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
      have j₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
      let A' := fun (i j : USize) (hi : i.toNat < n) (hj : j.toNat < n) =>
        A.uget ao al rfl rfl hs.1 i j hi hj
      let x' := fun (i : USize) (hi : i.toNat < n) => x.uget xo xc rfl rfl hs.2.1 i hi
      let t₀ := α * x' (4 * g) (by lia)
      let t₁ := α * x' (4 * g + 1) (by lia)
      let t₂ := α * x' (4 * g + 2) (by lia)
      let t₃ := α * x' (4 * g + 3) (by lia)
      let a10 := A' (4 * g + 1) (4 * g) (by lia) (by lia)
      let a20 := A' (4 * g + 2) (4 * g) (by lia) (by lia)
      let a30 := A' (4 * g + 3) (4 * g) (by lia) (by lia)
      let a21 := A' (4 * g + 2) (4 * g + 1) (by lia) (by lia)
      let a31 := A' (4 * g + 3) (4 * g + 1) (by lia) (by lia)
      let a32 := A' (4 * g + 3) (4 * g + 2) (by lia) (by lia)
      let x₁ := x' (4 * g + 1) (by lia)
      let x₂ := x' (4 * g + 2) (by lia)
      let x₃ := x' (4 * g + 3) (by lia)
      for l in 0...(nu - 4 - 4 * g) with (s₀ := ((0 + a10 * x₁) + a20 * x₂) + a30 * x₃)
          (s₁ := (0 + a21 * x₂) + a31 * x₃) (s₂ := 0 + a32 * x₃) (s₃ := 0) do
        have hi : (4 * g + 4 + l).toNat < n := by grind
        have hk : (o + cc * (4 * g + 4 + l)).toNat < c.size :=
          hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let xi := x' (4 * g + 4 + l) hi
        let p₀ := A' (4 * g + 4 + l) (4 * g) hi (by lia)
        let p₁ := A' (4 * g + 4 + l) (4 * g + 1) hi (by lia)
        let p₂ := A' (4 * g + 4 + l) (4 * g + 2) hi (by lia)
        let p₃ := A' (4 * g + 4 + l) (4 * g + 3) hi (by lia)
        c[o + cc * (4 * g + 4 + l)] :=
          (((c[o + cc * (4 * g + 4 + l)] + t₀ * p₀) + t₁ * p₁) + t₂ * p₂) + t₃ * p₃
        s₀ := s₀ + p₀ * xi
        s₁ := s₁ + p₁ * xi
        s₂ := s₂ + p₂ * xi
        s₃ := s₃ + p₃ * xi
      have k₀ : (o + cc * (4 * g)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have k₁ : (o + cc * (4 * g + 1)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have k₂ : (o + cc * (4 * g + 2)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      have k₃ : (o + cc * (4 * g + 3)).toNat < c.size :=
        hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 (by lia)
      let v₀ := c[o + cc * (4 * g)]
      let v₁ := c[o + cc * (4 * g + 1)]
      let v₂ := c[o + cc * (4 * g + 2)]
      let v₃ := c[o + cc * (4 * g + 3)]
      c[o + cc * (4 * g)] := (v₀ + t₀ * A' (4 * g) (4 * g) (by lia) (by lia)) + α * s₀
      c[o + cc * (4 * g + 1)] :=
        ((v₁ + t₀ * a10) + t₁ * A' (4 * g + 1) (4 * g + 1) (by lia) (by lia)) + α * s₁
      c[o + cc * (4 * g + 2)] := (((v₂ + t₀ * a20) + t₁ * a21) +
        t₂ * A' (4 * g + 2) (4 * g + 2) (by lia) (by lia)) + α * s₂
      c[o + cc * (4 * g + 3)] := ((((v₃ + t₀ * a30) + t₁ * a31) + t₂ * a32) +
        t₃ * A' (4 * g + 3) (4 * g + 3) (by lia) (by lia)) + α * s₃
    for j in 4 * q4...nu do
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
      c[o + cc * j] := d + α * s

public theorem symvLowerData_eq_iterRange (α : Float) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    symvLowerData α A x y hs o cc ho hcc c hc = iterRange (symvLowerStep α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  have hq4 : (n.toUSize / 4).toNat = n / 4 := by simp only [USize.toNat_div, hnu]; simp
  have h4q : (4 * (n.toUSize / 4)).toNat = 4 * (n / 4) := by grind
  have hF : ∀ j (b : Float64Array), (symvLowerStep α A x y j b).size = b.size :=
    fun _ _ => by unfold symvLowerStep; exact size_modifyAt _ _ _ _ _
  subst ho hcc
  unfold symvLowerData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit
    (F := fun g b => iterRange (symvLowerStep α A x y) (4 * g) (4 * g + 4) b)
    (hF := fun _ _ => size_iterRange _ hF _ _ _)]
  rotate_left
  · intro g _ hg next a h
    rw [hq4] at hg
    have hg4 : 4 * g.toNat + 3 < n := by lia
    have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
    have j₀ : (4 * g).toNat = 4 * g.toNat := by grind
    have j₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
    have j₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
    have j₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
    have hm : (n.toUSize - 4 - 4 * g).toNat = n - 4 - 4 * g.toNat := by grind
    have t₀ := y.toNat_index hs.2.2 (i := 4 * g) (by lia)
    have t₁ := y.toNat_index hs.2.2 (i := 4 * g + 1) (by lia)
    have t₂ := y.toNat_index hs.2.2 (i := 4 * g + 2) (by lia)
    have t₃ := y.toNat_index hs.2.2 (i := 4 * g + 3) (by lia)
    rw [j₀] at t₀
    rw [j₁] at t₁
    rw [j₂] at t₂
    rw [j₃] at t₃
    let J := 4 * g.toNat
    let H := fun l w =>
      (((w + α * x.data[x.off + x.inc * (J + 0)]! * A.data[A.off + A.ld * (J + 0) + (J + 4 + l)]!) +
        α * x.data[x.off + x.inc * (J + 1)]! * A.data[A.off + A.ld * (J + 1) + (J + 4 + l)]!) +
        α * x.data[x.off + x.inc * (J + 2)]! * A.data[A.off + A.ld * (J + 2) + (J + 4 + l)]!) +
        α * x.data[x.off + x.inc * (J + 3)]! * A.data[A.off + A.ld * (J + 3) + (J + 4 + l)]!
    simp only [Tail.forIn4_eq]
    rw [run_forIn4From_modify
      (f₀ := fun l s => s + A.data[A.off + A.ld * (J + 0) + (J + 4 + l)]! *
        x.data[x.off + x.inc * (J + 4 + l)]!)
      (f₁ := fun l s => s + A.data[A.off + A.ld * (J + 1) + (J + 4 + l)]! *
        x.data[x.off + x.inc * (J + 4 + l)]!)
      (f₂ := fun l s => s + A.data[A.off + A.ld * (J + 2) + (J + 4 + l)]! *
        x.data[x.off + x.inc * (J + 4 + l)]!)
      (f₃ := fun l s => s + A.data[A.off + A.ld * (J + 3) + (J + 4 + l)]! *
        x.data[x.off + x.inc * (J + 4 + l)]!)
      (F := fun l b => b.set! (y.off + y.inc * (J + 4 + l)) (H l b[y.off + y.inc * (J + 4 + l)]!))
      (hF := fun _ _ => by simp)]
    · simp only [Tail.run_readThen, Tail.run_writeThen, USize.toNat_zero, hm]
      apply run_congr
      simp only [set_eq_set!, getElem_eq_getElem!, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, t₀, t₁, t₂, t₃, j₀, j₁, j₂, j₃]
      rw [iterRange_set!_self, iterRange_symvLowerStep_four α A x y a (h.trans hc) hg4]
      obtain ⟨d₀, d₁, d₂, d₃⟩ := symvLowerDot_four A x hg4
      rw [d₀, d₁, d₂, d₃]
      simp (disch := exact fun i _ hi => (idx_ne y (by lia) (by lia)).symm) only
        [iterRange_eq_fold, Nat.add_zero, H, J, getElem!_modifyAt_of_ne]
    · intro l _ hl next' s₀ s₁ s₂ s₃ b hb
      rw [hm] at hl
      have hl' : (4 * g + 4 + l).toNat = 4 * g.toNat + 4 + l.toNat := by grind
      have hq := y.toNat_index hs.2.2 (i := 4 * g + 4 + l) (by lia)
      rw [hl'] at hq
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, hq, hl', j₀, j₁, j₂, j₃, getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _
  rw [Tail.run_forInFrom_unit (F := symvLowerStep α A x y) (hF := hF)]
  · simp only [Tail.run_done, hq4, h4q, hnu, USize.toNat_zero]
    rw [iterRange_four, ← iterRange_split _ (Nat.zero_le _) (by lia)]
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
@[expose] public def symvLowerAt (α : Float) (A : Mat n n) (x : Vec n) (i : Nat) (v : Float) :
    Float :=
  Nat.fold i (fun j _ s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + i]!) v +
    α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i + i]! + α * symvLowerDot A x i

/--
After the steps `l < j`, the elements `i < j` are final, and the others have the terms `l < j`.
-/
theorem iterRange_symvLowerStep (α : Float) (A : Mat n n) (x y : Vec n) (c : Float64Array)
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
public theorem symvLowerData_eq (α : Float) (A : Mat n n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    symvLowerData α A x y hs o cc ho hcc c hc = c.modifyAt y.stride.idx 0 n (symvLowerAt α A x) := by
  rw [symvLowerData_eq_iterRange, iterRange_symvLowerStep α A x y c hc (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp only [hi, ite_true]

/-! ## `symv` -/

/-- The value of element `i` of the product on the triangle `uplo`, from its scaled value `v`. -/
@[expose] public def symvAt (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) : Nat → Float →
    Float :=
  match uplo with
  | .upper => symvUpperAt α A x
  | .lower => symvLowerAt α A x

/--
The value of `symv` at the index `i` of `y`, from its old value `v`: `betaMul β v` when `α = 0`,
and otherwise `symvAt` of it.
-/
@[expose] public def symvVal (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (i : Nat) (v : Float) : Float :=
  if α == 0 then betaMul β v else symvAt uplo α A x i (betaMul β v)

/-- The array of `symv`. -/
public def symvData (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (y : Vec n) : Float64Array :=
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

public theorem symvData_eq (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
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
@[expose] public def symv (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (y : Vec n) : Vec n where
  data := symvData uplo α A x β y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [symvData_eq, size_modifyAt]; exact y.bound

/-- The array of `symv uplo α A x β y` is the array of `y` with its elements updated. -/
public theorem data_symv (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (y : Vec n) :
    (symv uplo α A x β y).data = y.data.modifyAt y.stride.idx 0 n (symvVal uplo α A x β) :=
  symvData_eq uplo α A x β y

@[simp] public theorem off_symv (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (y : Vec n) : (symv uplo α A x β y).off = y.off := rfl

@[simp] public theorem inc_symv (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (y : Vec n) : (symv uplo α A x β y).inc = y.inc := rfl

/-- Element `i` of `symv uplo α A x β y` is `symvVal` of `y[i]`. -/
public theorem getElem_symv (uplo : Uplo) (α : Float) (A : Mat n n) (x : Vec n) (β : Float)
    (y : Vec n) (i : Nat) (h : i < n) :
    (symv uplo α A x β y)[i] = symvVal uplo α A x β i y[i] :=
  Vec.getElem_of_data_eq_modifyAt _ (data_symv uplo α A x β y) (off_symv uplo α A x β y)
    (inc_symv uplo α A x β y) i h

/--
Element `i` of `symv .upper α A x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i] + α * x[i] * A[i, i] + α * t`, with `t` the sum of the terms `A[k, i] * x[k]` for
`k = 0, …, i - 1`, plus the terms `α * x[j] * A[i, j]` for `j = i + 1, …, n - 1`.
-/
public theorem getElem_symv_upper (α : Float) (A : Mat n n) (x : Vec n) (β : Float) (y : Vec n)
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
public theorem getElem_symv_lower (α : Float) (A : Mat n n) (x : Vec n) (β : Float) (y : Vec n)
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

end BLAS.Float64
