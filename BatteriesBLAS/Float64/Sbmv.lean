/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float64.Gbmv
public import BatteriesBLAS.Float64.Trsv
import all BatteriesBLAS.Internal

/-!
# Symmetric band matrix-vector product

A symmetric band matrix with `k` sub- and superdiagonals is stored as in the reference BLAS, by one
of its triangles in a matrix `A : Mat (k + 1) n`: for the upper triangle, the element in row `i`
and column `j` of the band matrix, for `j - k ≤ i ≤ j`, is in row `k + i - j` of column `j` of `A`,
so that the diagonal is row `k`; for the lower triangle, the element for `j ≤ i ≤ j + k` is in row
`i - j`, so that the diagonal is row `0`. The other elements of `A` are not part of the matrix, and
the routines don't read them.

`Mat.sbmv uplo α A x β y` computes `α * A * x + β * y` by the loops of the reference BLAS (`dsbmv`):
it first scales `y` by `β` (setting it to `0` when `β = 0`), and then, for each column `j` of the
triangle, adds `α * x[j]` times the column to the other elements of `y` in the band, and to `y[j]`
the diagonal term and `α` times the dot product of the column with `x`. Each element of `y` gets
these terms in the order of the loops, as for `Mat.symv`.
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

/-! ## The upper triangle -/

/--
The dot product of column `j` of the upper band, above the diagonal, with `x`: the terms
`A[k + i - j, j] * x[i]` for `i = j - min j k, …, j - 1`, from `0`.
-/
@[expose] public def sbmvUpperDot (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat) : Float :=
  Nat.fold (min j k) (fun l _ s =>
    s + A.data[A.off + A.ld * j + (k - min j k + l)]! *
      x.data[x.off + x.inc * (j - min j k + l)]!) 0

/--
The step `j` of the upper product: add `α * x[j]` times column `j` of the band to the elements
above `j`, and the diagonal term and `α` times `sbmvUpperDot k A x j` to element `j`.
-/
@[expose] public def sbmvUpperStep (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt y.stride.idx 0 n fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + k]! +
        α * sbmvUpperDot k A x j
    else if j - min j k ≤ i ∧ i < j - min j k + min j k then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (k + i - j)]!
    else v

/-- The loops of the upper product on the array `c` of `y`, already scaled by `β`. -/
public def sbmvUpperData (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) : Float64Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  let ku := k.toUSize
  inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      have hku : ku.toNat = k := toNat_toUSize_of_lt (by
        have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      let lo := j - bandAbove k j
      let r0 := ku - bandAbove k j
      for l in 0...bandAbove k j with (s := 0) do
        have hl := toNat_sub_bandAbove_add (by assumption)
        have hr := toNat_sub_bandAbove_add' hku (by assumption)
        have hi : (lo + l).toNat < n := hl.1 ▸ Nat.lt_trans hl.2 hjn
        have hq : (o + cc * (lo + l)).toNat < c.size :=
          hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := A.uget ao al rfl rfl hs.1 (r0 + l) j (by rw [hr.1]; lia) hjn
        c[o + cc * (lo + l)] := c[o + cc * (lo + l)] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 (lo + l) hi
      have hq : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      c[o + cc * j] :=
        c[o + cc * j] + t * A.uget ao al rfl rfl hs.1 ku j (by lia) hjn + α * s

public theorem sbmvUpperData_eq_iterRange (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    sbmvUpperData k α A x y hs o cc ho hcc c hc = iterRange (sbmvUpperStep k α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  subst ho hcc
  unfold sbmvUpperData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := sbmvUpperStep k α A x y)
    (hF := fun _ _ => by unfold sbmvUpperStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hku : k.toUSize.toNat = k :=
      toNat_toUSize_of_lt (by have := A.rows_lt_size hs.1 (by lia) (by lia); lia)
    have hp : (y.off.toUSize + y.inc.toUSize * j).toNat = y.off + y.inc * j.toNat :=
      y.toNat_index hs.2.2 hj
    have hab := toNat_bandAbove k j
    rw [Tail.run_forInFrom (f := fun l p =>
        (p.1 + A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]! *
            x.data[x.off + x.inc * (j.toNat - min j.toNat k + l)]!,
          p.2.set! (y.off + y.inc * (j.toNat - min j.toNat k + l))
            (p.2[y.off + y.inc * (j.toNat - min j.toNat k + l)]! +
              α * x.data[x.off + x.inc * j.toNat]! *
                A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun l => A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]! *
          x.data[x.off + x.inc * (j.toNat - min j.toNat k + l)]!)
        (fun l c => c.set! (y.off + y.inc * (j.toNat - min j.toNat k + l))
          (c[y.off + y.inc * (j.toNat - min j.toNat k + l)]! +
            α * x.data[x.off + x.inc * j.toNat]! *
              A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]!)) (min j.toNat k) 0 a
      rw [iterRange_set!_self a (fun l => y.off + y.inc * (j.toNat - min j.toNat k + l))
        (fun l v => v + α * x.data[x.off + x.inc * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + l)]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_readThen, Tail.run_writeThen, hab]
      apply run_congr
      simp only [hpair, Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, hp,
        hku]
      rw [set_eq_set!]
      simp only [getElem_eq_getElem!]
      rw [set!_modifyAt_band y a (h.trans hc) (j.toNat - min j.toNat k) (min j.toNat k) j.toNat
        (by lia) hj (by lia) _ (fun v => v + α * x.data[x.off + x.inc * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + k]! +
          α * Nat.fold (min j.toNat k) (fun i _ s =>
            s + A.data[A.off + A.ld * j.toNat + (k - min j.toNat k + i)]! *
              x.data[x.off + x.inc * (j.toNat - min j.toNat k + i)]!) 0), sbmvUpperStep]
      apply modifyAt_congr_fun
      intro i v _ _
      by_cases h₁ : i = j.toNat
      · simp only [h₁, ↓reduceIte, sbmvUpperDot]
      · simp only [h₁, ↓reduceIte]
        split
        · rw [show k - min j.toNat k + (i - (j.toNat - min j.toNat k)) = k + i - j.toNat by lia]
        · rfl
    · intro l _ hl next' s a' h'
      rw [hab] at hl
      have hl' := toNat_sub_bandAbove_add (k := k) (j := j) (l := l) (by rw [hab]; exact hl)
      have hr := toNat_sub_bandAbove_add' (k := k) (j := j) (l := l) hku (by rw [hab]; exact hl)
      have hq : (y.off.toUSize + y.inc.toUSize * (j - bandAbove k j + l)).toNat =
          y.off + y.inc * (j.toNat - min j.toNat k + l.toNat) := by
        rw [y.toNat_index hs.2.2 (by rw [hl'.1]; lia), hl'.1]
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, hq, hl'.1, hr.1]
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/--
The value of element `i` of the upper product, from its value `v` after the scaling: `v` plus the
diagonal term and `α` times the dot product of column `i`, then the terms
`α * x[j] * A[k + i - j, j]` for `j = i + 1, …, i + min (n - 1 - i) k`.
-/
@[expose] public def sbmvUpperAt (k : Nat) (α : Float) (A : Mat (k + 1) n) (x : Vec n) (i : Nat)
    (v : Float) : Float :=
  Nat.fold (min (n - 1 - i) k) (fun t _ s =>
      s + α * x.data[x.off + x.inc * (i + 1 + t)]! *
        A.data[A.off + A.ld * (i + 1 + t) + (k - 1 - t)]!)
    (v + α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i + k]! + α * sbmvUpperDot k A x i)

/-- The loops of the upper product map the array of the scaled `y` by `sbmvUpperAt`. -/
public theorem sbmvUpperData_eq (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    sbmvUpperData k α A x y hs o cc ho hcc c hc =
      c.modifyAt y.stride.idx 0 n (sbmvUpperAt k α A x) := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  rw [sbmvUpperData_eq_iterRange, show sbmvUpperStep k α A x y = fun j c =>
      c.modifyAt y.stride.idx 0 n fun i v =>
        if i = j then
          v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + k]! +
            α * sbmvUpperDot k A x j
        else if j - min j k ≤ i ∧ i < j - min j k + min j k then
          v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (k + i - j)]!
        else v from rfl, iterRange_modifyAt _ _ hinj]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [fold_upper_band hi k (fun j s => s + α * x.data[x.off + x.inc * j]! *
      A.data[A.off + A.ld * j + k]! + α * sbmvUpperDot k A x j)
    (fun j s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (k + i - j)]!),
    sbmvUpperAt]
  congr 1
  funext t ht s
  rw [show k + i - (i + 1 + t) = k - 1 - t by lia]

/-! ## The lower triangle -/

/--
The dot product of column `j` of the lower band, below the diagonal, with `x`: the terms
`A[1 + l, j] * x[j + 1 + l]` for `l < min (n - 1 - j) k`, from `0`.
-/
@[expose] public def sbmvLowerDot (k : Nat) (A : Mat (k + 1) n) (x : Vec n) (j : Nat) : Float :=
  Nat.fold (min (n - 1 - j) k) (fun l _ s =>
    s + A.data[A.off + A.ld * j + (1 + l)]! * x.data[x.off + x.inc * (j + 1 + l)]!) 0

/--
The step `j` of the lower product: add `α * x[j]` times column `j` of the band to the elements
below `j`, and the diagonal term and `α` times `sbmvLowerDot k A x j` to element `j`.
-/
@[expose] public def sbmvLowerStep (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt y.stride.idx 0 n fun i v =>
    if i = j then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j]! + α * sbmvLowerDot k A x j
    else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (i - j)]!
    else v

/-- The loops of the lower product on the array `c` of `y`, already scaled by `β`. -/
public def sbmvLowerData (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) : Float64Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      have hq : (o + cc * j).toNat < c.size := hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hjn
      let d := c[o + cc * j] + t * A.uget ao al rfl rfl hs.1 0 j (by simp) hjn
      for l in 0...bandBelow n k j with (s := 0) do
        have hl := toNat_bandBelow_add hn hjn (by assumption)
        have hr := toNat_one_add_bandBelow (k := k) hn (by assumption)
        have hi : (j + 1 + l).toNat < n := hl.1 ▸ hl.2
        have hq' : (o + cc * (j + 1 + l)).toNat < c.size :=
          hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        let aij := A.uget ao al rfl rfl hs.1 (1 + l) j (hr.1 ▸ hr.2) hjn
        c[o + cc * (j + 1 + l)] := c[o + cc * (j + 1 + l)] + t * aij
        s := s + aij * x.uget xo xc rfl rfl hs.2.1 (j + 1 + l) hi
      c[o + cc * j] := d + α * s

public theorem sbmvLowerData_eq_iterRange (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    sbmvLowerData k α A x y hs o cc ho hcc c hc = iterRange (sbmvLowerStep k α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2.1
  subst ho hcc
  unfold sbmvLowerData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := sbmvLowerStep k α A x y)
    (hF := fun _ _ => by unfold sbmvLowerStep; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hp : (y.off.toUSize + y.inc.toUSize * j).toNat = y.off + y.inc * j.toNat :=
      y.toNat_index hs.2.2 hj
    have hbe := toNat_bandBelow hn k j
    simp only [Tail.run_readThen]
    rw [Tail.run_forInFrom (f := fun l p =>
        (p.1 + A.data[A.off + A.ld * j.toNat + (1 + l)]! *
            x.data[x.off + x.inc * (j.toNat + 1 + l)]!,
          p.2.set! (y.off + y.inc * (j.toNat + 1 + l)) (p.2[y.off + y.inc * (j.toNat + 1 + l)]! +
            α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + (1 + l)]!)))
      (hf := by simp)]
    · have hpair := iterRange_pair
        (fun l => A.data[A.off + A.ld * j.toNat + (1 + l)]! *
          x.data[x.off + x.inc * (j.toNat + 1 + l)]!)
        (fun l c => c.set! (y.off + y.inc * (j.toNat + 1 + l))
          (c[y.off + y.inc * (j.toNat + 1 + l)]! + α * x.data[x.off + x.inc * j.toNat]! *
            A.data[A.off + A.ld * j.toNat + (1 + l)]!)) (min (n - 1 - j.toNat) k) 0 a
      rw [iterRange_set!_self a (fun l => y.off + y.inc * (j.toNat + 1 + l)) (fun l v =>
        v + α * x.data[x.off + x.inc * j.toNat]! *
          A.data[A.off + A.ld * j.toNat + (1 + l)]!)] at hpair
      simp only [USize.toNat_zero, Tail.run_writeThen, hbe]
      apply run_congr
      simp only [hpair, Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, hp,
        USize.toNat_zero, Nat.add_zero]
      rw [set_eq_set!]
      simp only [getElem_eq_getElem!]
      have hne := getElem!_modifyAt_of_ne a (fun l => y.off + y.inc * (j.toNat + 1 + l))
        (lo := 0) (hi := min (n - 1 - j.toNat) k) (fun l v =>
          v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat + (1 + l)]!)
        (p := y.off + y.inc * j.toNat) (fun l _ hl e => by
          have := y.fits.injOn (lo := 0) (Nat.le_refl _) (j.toNat + 1 + l) (Nat.zero_le _)
            (by lia) j.toNat (Nat.zero_le _) hj e
          lia)
      rw [← hne]
      rw [set!_modifyAt_band y a (h.trans hc) (j.toNat + 1) (min (n - 1 - j.toNat) k) j.toNat
        (by lia) hj (by lia) (w := fun v =>
          v + α * x.data[x.off + x.inc * j.toNat]! * A.data[A.off + A.ld * j.toNat]! +
            α * Nat.fold (min (n - 1 - j.toNat) k) (fun i _ s =>
              s + A.data[A.off + A.ld * j.toNat + (1 + i)]! *
                x.data[x.off + x.inc * (j.toNat + 1 + i)]!) 0), sbmvLowerStep]
      apply modifyAt_congr_fun
      intro i v _ _
      by_cases h₁ : i = j.toNat
      · simp only [h₁, ↓reduceIte, sbmvLowerDot]
      · simp only [h₁, ↓reduceIte]
        split
        · rw [show 1 + (i - (j.toNat + 1)) = i - j.toNat by lia]
        · rfl
    · intro l _ hl next' s a' h'
      rw [hbe] at hl
      have hl' := toNat_bandBelow_add (k := k) hn hj (l := l) (by rw [hbe]; exact hl)
      have hr := toNat_one_add_bandBelow (k := k) hn (j := j) (l := l) (by rw [hbe]; exact hl)
      have hq : (y.off.toUSize + y.inc.toUSize * (j + 1 + l)).toNat =
          y.off + y.inc * (j.toNat + 1 + l.toNat) := by
        rw [y.toNat_index hs.2.2 (by rw [hl'.1]; exact hl'.2), hl'.1]
      simp only [Tail.run_readThen, Tail.run_writeThen, Vec.uget_eq_getElem, uget_eq_getElem,
        Vec.getElem_def, getElem_def, hq, hl'.1, hr.1]
      simp only [getElem_eq_getElem!]
      exact run_congr _ (set_eq_set! _ _ _ _) _ _

/--
The value of element `i` of the lower product, from its value `v` after the scaling: `v` plus the
terms `α * x[j] * A[i - j, j]` for `j = i - min i k, …, i - 1`, then the diagonal term and `α`
times the dot product of column `i`.
-/
@[expose] public def sbmvLowerAt (k : Nat) (α : Float) (A : Mat (k + 1) n) (x : Vec n) (i : Nat)
    (v : Float) : Float :=
  Nat.fold (min i k) (fun t _ s =>
      s + α * x.data[x.off + x.inc * (i - min i k + t)]! *
        A.data[A.off + A.ld * (i - min i k + t) + (min i k - t)]!) v +
    α * x.data[x.off + x.inc * i]! * A.data[A.off + A.ld * i]! + α * sbmvLowerDot k A x i

/-- The loops of the lower product map the array of the scaled `y` by `sbmvLowerAt`. -/
public theorem sbmvLowerData_eq (k : Nat) (α : Float) (A : Mat (k + 1) n) (x y : Vec n)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    sbmvLowerData k α A x y hs o cc ho hcc c hc =
      c.modifyAt y.stride.idx 0 n (sbmvLowerAt k α A x) := by
  have hinj : ∀ i, 0 ≤ i → i < n → ∀ j, 0 ≤ j → j < n → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits n c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  rw [sbmvLowerData_eq_iterRange, show sbmvLowerStep k α A x y = fun j c =>
      c.modifyAt y.stride.idx 0 n fun i v =>
        if i = j then
          v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j]! + α * sbmvLowerDot k A x j
        else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then
          v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (i - j)]!
        else v from rfl, iterRange_modifyAt _ _ hinj]
  apply modifyAt_congr_fun
  intro i v _ hi
  rw [fold_lower_band hi k (fun j s => s + α * x.data[x.off + x.inc * j]! *
      A.data[A.off + A.ld * j]! + α * sbmvLowerDot k A x j)
    (fun j s => s + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (i - j)]!),
    sbmvLowerAt]
  congr 3
  funext t ht s
  rw [show i - (i - min i k + t) = min i k - t by lia]

/-! ## `sbmv` -/

/-- The value of element `i` of the product on the triangle `uplo`, from its scaled value `v`. -/
@[expose] public def sbmvAt (uplo : Uplo) (k : Nat) (α : Float) (A : Mat (k + 1) n) (x : Vec n) :
    Nat → Float → Float :=
  match uplo with
  | .upper => sbmvUpperAt k α A x
  | .lower => sbmvLowerAt k α A x

/--
The value of `sbmv` at the index `i` of `y`, from its old value `v`: `betaMul β v` when `α = 0`,
and otherwise `sbmvAt` of it.
-/
@[expose] public def sbmvVal (uplo : Uplo) (k : Nat) (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (i : Nat) (v : Float) : Float :=
  if α == 0 then betaMul β v else sbmvAt uplo k α A x i (betaMul β v)

/-- The array of `sbmv`. -/
public def sbmvData (uplo : Uplo) (k : Nat) (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let o := y.off.toUSize
    let cc := y.inc.toUSize
    if α == 0 then y.scalBetaData β
    else match uplo with
      | .upper => sbmvUpperData k α A x y hs o cc rfl rfl (y.scalBetaData β)
          (by rw [Vec.scalBetaData_eq, size_modifyAt])
      | .lower => sbmvLowerData k α A x y hs o cc rfl rfl (y.scalBetaData β)
          (by rw [Vec.scalBetaData_eq, size_modifyAt])
  else y.data.modifyAt y.stride.idx 0 n (sbmvVal uplo k α A x β)

public theorem sbmvData_eq (uplo : Uplo) (k : Nat) (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) :
    sbmvData uplo k α A x β y = y.data.modifyAt y.stride.idx 0 n (sbmvVal uplo k α A x β) := by
  have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
  unfold sbmvData
  split
  · rename_i hs
    cases hα : α == 0
    · cases uplo
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [sbmvUpperData_eq, Vec.scalBetaData_eq, modifyAt_modifyAt _ _ hinj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp [sbmvVal, sbmvAt, hα]
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [sbmvLowerData_eq, Vec.scalBetaData_eq, modifyAt_modifyAt _ _ hinj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp [sbmvVal, sbmvAt, hα]
    · simp only [↓reduceIte]
      rw [Vec.scalBetaData_eq]
      apply modifyAt_congr_fun
      intro i v _ _
      simp [sbmvVal, hα]
  · rfl

/--
`sbmv uplo α A x β y` is `α * A * x + β * y` for the symmetric band matrix with `k` sub- and
superdiagonals stored by its triangle `uplo` in `A : Mat (k + 1) n`, over `y`, by the loops of the
reference BLAS (`dsbmv`). It updates `y` in place when its array is not shared, leaves the elements
of the array outside `y` unchanged, and reads only the band of the triangle `uplo`. As in the
reference BLAS, it sets `y` to `0` before adding the terms when `β = 0`, and only scales `y` when
`α = 0`.
-/
@[expose] public def sbmv (uplo : Uplo) {k : Nat} (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) : Vec n where
  data := sbmvData uplo k α A x β y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [sbmvData_eq, size_modifyAt]; exact y.bound

/-- The array of `sbmv uplo α A x β y` is the array of `y` with its elements updated. -/
public theorem data_sbmv (uplo : Uplo) {k : Nat} (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) :
    (sbmv uplo α A x β y).data = y.data.modifyAt y.stride.idx 0 n (sbmvVal uplo k α A x β) :=
  sbmvData_eq uplo k α A x β y

@[simp] public theorem off_sbmv (uplo : Uplo) {k : Nat} (α : Float) (A : Mat (k + 1) n)
    (x : Vec n) (β : Float) (y : Vec n) : (sbmv uplo α A x β y).off = y.off := rfl

@[simp] public theorem inc_sbmv (uplo : Uplo) {k : Nat} (α : Float) (A : Mat (k + 1) n)
    (x : Vec n) (β : Float) (y : Vec n) : (sbmv uplo α A x β y).inc = y.inc := rfl

/-- Element `i` of `sbmv uplo α A x β y` is `sbmvVal` of `y[i]`. -/
public theorem getElem_sbmv (uplo : Uplo) {k : Nat} (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) (i : Nat) (h : i < n) :
    (sbmv uplo α A x β y)[i] = sbmvVal uplo k α A x β i y[i] :=
  Vec.getElem_of_data_eq_modifyAt _ (data_sbmv uplo α A x β y) (off_sbmv uplo α A x β y)
    (inc_sbmv uplo α A x β y) i h

/--
Element `i` of `sbmv .upper α A x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i] + α * x[i] * A[k, i] + α * t`, with `t` the sum of the terms
`A[k - min i k + l, i] * x[i - min i k + l]` for `l < min i k`, plus the terms
`α * x[i + 1 + t] * A[k - 1 - t, i + 1 + t]` for `t < min (n - 1 - i) k`.
-/
public theorem getElem_sbmv_upper {k : Nat} (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) (i : Nat) (h : i < n) :
    (sbmv .upper α A x β y)[i] =
      if α == 0 then betaMul β y[i]
      else Nat.fold (min (n - 1 - i) k) (fun t _ s =>
          s + α * x[i + 1 + t]'(by lia) * A[(k - 1 - t, i + 1 + t)]'⟨by lia, by lia⟩)
        (betaMul β y[i] + α * x[i] * A[(k, i)]'⟨by lia, h⟩ +
          α * Nat.fold (min i k) (fun l _ s =>
            s + A[(k - min i k + l, i)]'⟨by lia, h⟩ * x[i - min i k + l]'(by lia)) 0) := by
  rw [getElem_sbmv _ _ _ _ _ _ _ h, sbmvVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, sbmvAt, sbmvUpperAt, sbmvUpperDot]
    rw [getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt (by lia) h)]
    congr 1
    · funext t ht s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
      rfl
    · congr 3
      funext l hl s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt (by lia) h)]
      rfl
  · simp only [↓reduceIte]

/--
Element `i` of `sbmv .lower α A x β y` is `betaMul β y[i]` when `α = 0`, and otherwise
`betaMul β y[i]` plus the terms `α * x[j] * A[i - j, j]` for `j = i - min i k, …, i - 1`, plus
`α * x[i] * A[0, i] + α * t`, with `t` the sum of the terms `A[1 + l, i] * x[i + 1 + l]` for
`l < min (n - 1 - i) k`.
-/
public theorem getElem_sbmv_lower {k : Nat} (α : Float) (A : Mat (k + 1) n) (x : Vec n)
    (β : Float) (y : Vec n) (i : Nat) (h : i < n) :
    (sbmv .lower α A x β y)[i] =
      if α == 0 then betaMul β y[i]
      else Nat.fold (min i k) (fun t _ s =>
          s + α * x[i - min i k + t]'(by lia) *
            A[(min i k - t, i - min i k + t)]'⟨by lia, by lia⟩) (betaMul β y[i]) +
        α * x[i] * A[(0, i)]'⟨by lia, h⟩ +
        α * Nat.fold (min (n - 1 - i) k) (fun l _ s =>
          s + A[(1 + l, i)]'⟨by lia, h⟩ * x[i + 1 + l]'(by lia)) 0 := by
  rw [getElem_sbmv _ _ _ _ _ _ _ h, sbmvVal]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, sbmvAt, sbmvLowerAt, sbmvLowerDot]
    rw [getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data (A.off + A.ld * i)
      (by have := A.index_lt (i := 0) (by lia) h; simpa using this)]
    congr 2
    · congr 1
      · congr 1
        funext t ht s
        rw [getElem!_pos x.data _ (x.index_lt (by lia)),
          getElem!_pos A.data _ (A.index_lt (by lia) (by lia))]
        rfl
    · congr 2
      funext l hl s
      rw [getElem!_pos x.data _ (x.index_lt (by lia)),
        getElem!_pos A.data _ (A.index_lt (by lia) h)]
      rfl
  · simp only [↓reduceIte]

end Mat

end BLAS.Float64
