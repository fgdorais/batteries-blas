/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray

/-!
# `USize` indices

The bounds of the column windows of a column-major matrix, for `USize` indices. They are
nonlinear, so `grind` needs the bound `X * y + X ≤ X * Y` spelled out. The linear `toNat` facts
about `USize` indices that don't wrap around are left to `grind` where they are used. These lemmas
don't depend on the element type, so they live in the namespace `BLAS`.

They are private: they are not part of the library's API. The files that need them use
`import all BLAS.Internal`.
-/

namespace BLAS

/--
`(m * j).toNat + m.toNat ≤ p` for `j < n` and `m * n ≤ p`: column `j` fits. A product that wraps
around only gets smaller, so this needs no bound on `p`.
-/
private theorem toNat_mul_add_le {m j : USize} {n p : Nat} (hj : j.toNat < n)
    (hmn : m.toNat * n ≤ p) : (m * j).toNat + m.toNat ≤ p := by
  have : m.toNat * j.toNat + m.toNat ≤ m.toNat * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  grind

/--
The window of `len` elements at `x * y + z` fits in an `X × Y` matrix, for `y < Y` and
`z + len ≤ X`. As for `toNat_mul_add_le`, this needs no bound on `X * Y`.
-/
private theorem toNat_mul_add_add_le {x y z len : USize} {X Y : Nat} (hx : x.toNat = X)
    (hy : y.toNat < Y) (hz : z.toNat + len.toNat ≤ X) :
    (x * y + z).toNat + len.toNat ≤ X * Y := by
  have : X * y.toNat + X ≤ X * Y := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  grind

/-- `(x * y + z).toNat` for an element `z ≤ X` of the column `y < Y` of an `X × Y` matrix. -/
private theorem toNat_mul_add_eq {x y z : USize} {X Y : Nat} (hx : x.toNat = X) (hy : y.toNat < Y)
    (hz : z.toNat ≤ X) (hs : X * Y < USize.size) : (x * y + z).toNat = X * y.toNat + z.toNat := by
  have : X * y.toNat + X ≤ X * Y := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  grind

/-- The elements of two distinct columns of a column-major matrix are at distinct indices. -/
private theorem col_index_ne {off ld m i j i' j' : Nat} (hi : i < m) (hi' : i' < m) (hml : m ≤ ld)
    (hj : j ≠ j') : off + ld * j + i ≠ off + ld * j' + i' := by
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · have : ld * (j + 1) ≤ ld * j' := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at this; lia
  · have : ld * (j' + 1) ≤ ld * j := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at this; lia

/-- The steps of a stride of `1`, such as the rows of a column of a matrix, are distinct. -/
private theorem col_injOn (o lo hi : Nat) :
    ∀ i, lo ≤ i → i < hi → ∀ j, lo ≤ j → j < hi →
      (ScalarArray.Stride.mk o 1).idx i = (ScalarArray.Stride.mk o 1).idx j → i = j :=
  fun _ _ _ _ _ _ e => by simp only [ScalarArray.Stride.idx] at e; lia

/-! ## Folds over a range -/

/--
A fold whose steps outside `[lo, hi)` leave the value unchanged is a fold over the steps of
`[lo, hi)` below `n`.
-/
private theorem fold_ite_range {α : Type _} (n lo hi : Nat) (f : Nat → α → α) (init : α) :
    Nat.fold n (fun j _ s => if lo ≤ j ∧ j < hi then f j s else s) init =
      Nat.fold (min n hi - lo) (fun t _ s => f (lo + t) s) init := by
  induction n with
  | zero => rw [Nat.fold_zero, Nat.fold_congr (show min 0 hi - lo = 0 by lia), Nat.fold_zero]
  | succ n ih =>
    rw [Nat.fold_succ, ih]
    by_cases h : lo ≤ n ∧ n < hi
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
        Nat.fold_congr (show min (n + 1) hi - lo = (min n hi - lo) + 1 by lia),
        Nat.fold_succ, show lo + (min n hi - lo) = n by lia]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        Nat.fold_congr (show min (n + 1) hi - lo = min n hi - lo by lia)]

/-- The first step of a fold, taken out of it. -/
private theorem fold_succ_left {α : Type _} (n : Nat) (f : (i : Nat) → i < n + 1 → α → α)
    (init : α) :
    Nat.fold (n + 1) f init = Nat.fold n (fun i h => f (i + 1) (by lia)) (f 0 (by lia) init) := by
  rw [Nat.fold_congr (Nat.add_comm n 1), Nat.fold_add]
  simp only [Nat.fold_succ, Nat.fold_zero]
  congr 1
  funext i h s
  congr 1
  lia

/-! ## Band storage -/

/--
`j - k`, or `0` when `j ≤ k`, as a `USize`: the first row of column `j` of a band matrix with `k`
superdiagonals.
-/
@[noinline] public def bandLo (k : Nat) (j : USize) : USize := (j.toNat - k).toUSize

/--
`k - j`, or `0` when `k ≤ j`, as a `USize`: the row of the band storage of the first element of
column `j`, for `k` superdiagonals.
-/
@[noinline] public def bandRow0 (k : Nat) (j : USize) : USize := (k - j.toNat).toUSize

/--
`min m (j + kl + 1) - (j - ku)`, as a `USize`: the number of rows of column `j` of an `m`-row band
matrix with `kl` subdiagonals and `ku` superdiagonals.
-/
@[noinline] public def bandCount (m kl ku : Nat) (j : USize) : USize :=
  (min m (j.toNat + kl + 1) - (j.toNat - ku)).toUSize

private theorem toNat_bandLo (k : Nat) (j : USize) : (bandLo k j).toNat = j.toNat - k := by
  unfold bandLo
  have := j.toNat_lt_size
  grind

private theorem toNat_bandRow0 {k : Nat} (hk : k < USize.size) (j : USize) :
    (bandRow0 k j).toNat = k - j.toNat := by
  unfold bandRow0
  grind

private theorem toNat_bandCount {m : Nat} (hm : m < USize.size) (kl ku : Nat) (j : USize) :
    (bandCount m kl ku j).toNat = min m (j.toNat + kl + 1) - (j.toNat - ku) := by
  unfold bandCount
  grind

/-- Step `l` of column `j` of a band matrix is row `j - ku + l`, which is below `m`. -/
private theorem toNat_bandLo_add {m : Nat} (hm : m < USize.size) {kl ku : Nat} {j l : USize}
    (hl : l.toNat < (bandCount m kl ku j).toNat) :
    (bandLo ku j + l).toNat = j.toNat - ku + l.toNat ∧ j.toNat - ku + l.toNat < m := by
  rw [toNat_bandCount hm] at hl
  have := toNat_bandLo ku j
  constructor
  · grind
  · lia

/-- Step `l` of column `j` of a band matrix is in row `ku - j + l` of its storage. -/
private theorem toNat_bandRow0_add {m kl ku : Nat} (hm : m < USize.size)
    (hk : kl + ku + 1 < USize.size)
    {j l : USize} (hl : l.toNat < (bandCount m kl ku j).toNat) :
    (bandRow0 ku j + l).toNat = ku - j.toNat + l.toNat ∧ ku - j.toNat + l.toNat < kl + ku + 1 := by
  rw [toNat_bandCount hm] at hl
  have := toNat_bandRow0 (k := ku) (by lia) j
  constructor
  · grind
  · lia

/--
`min j k`, as a `USize`: the number of rows above the diagonal in column `j` of a band matrix with
`k` superdiagonals.
-/
@[noinline] public def bandAbove (k : Nat) (j : USize) : USize := (min j.toNat k).toUSize

/--
`min (n - 1 - j) k`, as a `USize`: the number of rows below the diagonal in column `j` of an
`n × n` band matrix with `k` subdiagonals.
-/
@[noinline] public def bandBelow (n k : Nat) (j : USize) : USize :=
  (min (n - 1 - j.toNat) k).toUSize

private theorem toNat_bandAbove (k : Nat) (j : USize) : (bandAbove k j).toNat = min j.toNat k := by
  unfold bandAbove
  have := j.toNat_lt_size
  grind

private theorem toNat_bandBelow {n : Nat} (hn : n < USize.size) (k : Nat) (j : USize) :
    (bandBelow n k j).toNat = min (n - 1 - j.toNat) k := by
  unfold bandBelow
  grind

/-- Step `l` above the diagonal of column `j` is row `j - min j k + l`, which is above `j`. -/
private theorem toNat_sub_bandAbove_add {k : Nat} {j l : USize}
    (hl : l.toNat < (bandAbove k j).toNat) :
    (j - bandAbove k j + l).toNat = j.toNat - min j.toNat k + l.toNat ∧
      j.toNat - min j.toNat k + l.toNat < j.toNat := by
  rw [toNat_bandAbove] at hl
  have := toNat_bandAbove k j
  constructor
  · grind
  · lia

/--
Step `l` above the diagonal of column `j` is in row `k - min j k + l` of the storage of the upper
band, given `k` as the `USize` `ku`.
-/
private theorem toNat_sub_bandAbove_add' {k : Nat} {ku j l : USize} (hku : ku.toNat = k)
    (hl : l.toNat < (bandAbove k j).toNat) :
    (ku - bandAbove k j + l).toNat = k - min j.toNat k + l.toNat ∧
      k - min j.toNat k + l.toNat < k := by
  rw [toNat_bandAbove] at hl
  have := toNat_bandAbove k j
  constructor
  · grind
  · lia

/-- Step `l` below the diagonal of column `j < n` is row `j + 1 + l`, which is below `n`. -/
private theorem toNat_bandBelow_add {n k : Nat} (hn : n < USize.size) {j l : USize}
    (hj : j.toNat < n) (hl : l.toNat < (bandBelow n k j).toNat) :
    (j + 1 + l).toNat = j.toNat + 1 + l.toNat ∧ j.toNat + 1 + l.toNat < n := by
  rw [toNat_bandBelow hn] at hl
  constructor
  · grind
  · lia

/-- Step `l` below the diagonal is in row `1 + l` of the storage of the lower band. -/
private theorem toNat_one_add_bandBelow {n k : Nat} (hn : n < USize.size) {j l : USize}
    (hl : l.toNat < (bandBelow n k j).toNat) :
    (1 + l).toNat = 1 + l.toNat ∧ 1 + l.toNat < k + 1 := by
  rw [toNat_bandBelow hn] at hl
  constructor
  · grind
  · lia

/-- `k.toUSize.toNat = k` for `k < USize.size`. -/
private theorem toNat_toUSize_of_lt {k : Nat} (hk : k < USize.size) : k.toUSize.toNat = k := by
  grind

/-! ## The rows of a band column -/

/--
Row `i` of the steps of an upper band with `k` superdiagonals, where step `j` updates row `j` by
`D` and the rows `j - min j k, …, j - 1` by `T j`: `D`, then `T` of the columns
`i + 1, …, i + min (n - 1 - i) k`.
-/
private theorem fold_upper_band {α : Type _} {n i : Nat} (hi : i < n) (k : Nat)
    (D : Nat → α → α) (T : Nat → α → α) (v : α) :
    Nat.fold n (fun j _ s =>
        if i = j then D j s else if j - min j k ≤ i ∧ i < j - min j k + min j k then T j s else s)
        v =
      Nat.fold (min (n - 1 - i) k) (fun t _ s => T (i + 1 + t) s) (D i v) := by
  rw [show (fun j (_ : j < n) s =>
        if i = j then D j s else if j - min j k ≤ i ∧ i < j - min j k + min j k then T j s else s) =
      fun j _ s => if i ≤ j ∧ j < i + k + 1 then (if j = i then D j s else T j s) else s from by
    funext j _ s
    by_cases h : i = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
        ite_eq_left_of_eq_true _ _ (eq_true h.symm)]
    · by_cases h' : j - min j k ≤ i ∧ i < j - min j k + min j k
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true h'),
          ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
          ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h'),
          ite_eq_right_of_eq_false _ _ (eq_false (by lia))],
    fold_ite_range, Nat.fold_congr (show min n (i + k + 1) - i = min (n - 1 - i) k + 1 by lia),
    fold_succ_left]
  congr 1
  · funext t ht s
    split
    · next h => exact absurd h (by lia)
    · rw [show i + (t + 1) = i + 1 + t by lia]
  · split
    · rfl
    · next h => exact absurd h (by lia)

/--
Row `i` of the steps of a lower band with `k` subdiagonals, where step `j` updates row `j` by `D`
and the rows `j + 1, …, j + min (n - 1 - j) k` by `T j`: `T` of the columns
`i - min i k, …, i - 1`, then `D`.
-/
private theorem fold_lower_band {α : Type _} {n i : Nat} (hi : i < n) (k : Nat)
    (D : Nat → α → α) (T : Nat → α → α) (v : α) :
    Nat.fold n (fun j _ s =>
        if i = j then D j s else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then T j s else s)
        v =
      D i (Nat.fold (min i k) (fun t _ s => T (i - min i k + t) s) v) := by
  rw [show (fun j (_ : j < n) s =>
        if i = j then D j s else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then T j s else s) =
      fun j _ s => if i - k ≤ j ∧ j < i + 1 then (if j = i then D j s else T j s) else s from by
    funext j _ s
    by_cases h : i = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
        ite_eq_left_of_eq_true _ _ (eq_true h.symm)]
    · by_cases h' : j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true h'),
          ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
          ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h'),
          ite_eq_right_of_eq_false _ _ (eq_false (by lia))],
    fold_ite_range, Nat.fold_congr (show min n (i + 1) - (i - k) = min i k + 1 by lia),
    Nat.fold_succ]
  split
  · next h =>
    rw [h]
    congr 1
    congr 1
    funext t ht s
    split
    · next h => exact absurd h (by lia)
    · rw [show i - k + t = i - min i k + t by lia]
  · next h => exact absurd h (by lia)

/--
`fold_lower_band` for the steps in the reverse order, the step `kk` for the column `n - 1 - kk`:
`D`, then `T` of the columns `i - 1, …, i - min i k`.
-/
private theorem fold_lower_band_rev {α : Type _} {n i : Nat} (hi : i < n) (k : Nat)
    (D : Nat → α → α) (T : Nat → α → α) (v : α) :
    Nat.fold n (fun kk _ s =>
        if i = n - 1 - kk then D (n - 1 - kk) s
        else if n - 1 - kk + 1 ≤ i ∧ i < n - 1 - kk + 1 + min (n - 1 - (n - 1 - kk)) k then
          T (n - 1 - kk) s
        else s) v =
      Nat.fold (min i k) (fun t _ s => T (i - 1 - t) s) (D i v) := by
  rw [show (fun kk (_ : kk < n) s =>
        if i = n - 1 - kk then D (n - 1 - kk) s
        else if n - 1 - kk + 1 ≤ i ∧ i < n - 1 - kk + 1 + min (n - 1 - (n - 1 - kk)) k then
          T (n - 1 - kk) s
        else s) =
      fun kk _ s => if n - 1 - i ≤ kk ∧ kk < n - 1 - i + min i k + 1 then
        (if kk = n - 1 - i then D (n - 1 - kk) s else T (n - 1 - kk) s) else s from by
    funext kk hkk s
    by_cases h : i = n - 1 - kk
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
        ite_eq_left_of_eq_true _ _ (eq_true (by lia))]
    · by_cases h' : n - 1 - kk + 1 ≤ i ∧ i < n - 1 - kk + 1 + min (n - 1 - (n - 1 - kk)) k
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true h'),
          ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
          ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h'),
          ite_eq_right_of_eq_false _ _ (eq_false (by lia))],
    fold_ite_range,
    Nat.fold_congr (show min n (n - 1 - i + min i k + 1) - (n - 1 - i) = min i k + 1 by lia),
    fold_succ_left]
  congr 1
  · funext t ht s
    split
    · next h => exact absurd h (by lia)
    · rw [show n - 1 - (n - 1 - i + (t + 1)) = i - 1 - t by lia]
  · split
    · rw [show n - 1 - (n - 1 - i + 0) = i by lia]
    · next h => exact absurd h (by lia)

/--
`fold_upper_band` for the steps in the reverse order, the step `kk` for the column `n - 1 - kk`:
`T` of the columns `i + min (n - 1 - i) k, …, i + 1`, then `D`.
-/
private theorem fold_upper_band_rev {α : Type _} {n i : Nat} (hi : i < n) (k : Nat)
    (D : Nat → α → α) (T : Nat → α → α) (v : α) :
    Nat.fold n (fun kk _ s =>
        if i = n - 1 - kk then D (n - 1 - kk) s
        else if n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
            i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k then
          T (n - 1 - kk) s
        else s) v =
      D i (Nat.fold (min (n - 1 - i) k) (fun t _ s => T (i + min (n - 1 - i) k - t) s) v) := by
  rw [show (fun kk (_ : kk < n) s =>
        if i = n - 1 - kk then D (n - 1 - kk) s
        else if n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
            i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k then
          T (n - 1 - kk) s
        else s) =
      fun kk _ s => if n - 1 - i - min (n - 1 - i) k ≤ kk ∧ kk < n - 1 - i + 1 then
        (if kk = n - 1 - i then D (n - 1 - kk) s else T (n - 1 - kk) s) else s from by
    funext kk hkk s
    by_cases h : i = n - 1 - kk
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
        ite_eq_left_of_eq_true _ _ (eq_true (by lia))]
    · by_cases h' : n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
          i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true h'),
          ite_eq_left_of_eq_true _ _ (eq_true (by lia)),
          ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h'),
          ite_eq_right_of_eq_false _ _ (eq_false (by lia))],
    fold_ite_range,
    Nat.fold_congr (show min n (n - 1 - i + 1) - (n - 1 - i - min (n - 1 - i) k) =
      min (n - 1 - i) k + 1 by lia),
    Nat.fold_succ]
  split
  · next h =>
    rw [show n - 1 - (n - 1 - i - min (n - 1 - i) k + min (n - 1 - i) k) = i by lia]
    congr 1
    congr 1
    funext t ht s
    split
    · next h => exact absurd h (by lia)
    · rw [show n - 1 - (n - 1 - i - min (n - 1 - i) k + t) = i + min (n - 1 - i) k - t by lia]
  · next h => exact absurd h (by lia)

/-- Step `t` above the diagonal of column `j`, from the diagonal up, is row `j - 1 - t`. -/
private theorem toNat_sub_one_sub_bandAbove {k : Nat} {j t : USize}
    (ht : t.toNat < (bandAbove k j).toNat) :
    (j - 1 - t).toNat = j.toNat - 1 - t.toNat ∧ j.toNat - 1 - t.toNat < j.toNat := by
  rw [toNat_bandAbove] at ht
  constructor
  · grind
  · lia

/--
Step `t` above the diagonal of column `j`, from the diagonal up, is in row `k - 1 - t` of the
storage of the upper band, given `k` as the `USize` `ku`.
-/
private theorem toNat_sub_one_sub_bandAbove' {k : Nat} {ku j t : USize} (hku : ku.toNat = k)
    (ht : t.toNat < (bandAbove k j).toNat) :
    (ku - 1 - t).toNat = k - 1 - t.toNat ∧ k - 1 - t.toNat < k := by
  rw [toNat_bandAbove] at ht
  constructor
  · grind
  · lia

/--
The steps of `fold_lower_band` before the step for column `i`: `T` of the columns
`i - min i k, …, i - 1`.
-/
private theorem fold_lower_band_pre {α : Type _} {n i : Nat} (hi : i < n) (k : Nat)
    (D : Nat → α → α) (T : Nat → α → α) (v : α) :
    Nat.fold i (fun j _ s =>
        if i = j then D j s else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then T j s else s)
        v =
      Nat.fold (min i k) (fun t _ s => T (i - min i k + t) s) v := by
  rw [show (fun j (_ : j < i) s =>
        if i = j then D j s else if j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k then T j s else s) =
      fun j _ s => if i - k ≤ j ∧ j < i then T j s else s from by
    funext j hj s
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
    by_cases h' : j + 1 ≤ i ∧ i < j + 1 + min (n - 1 - j) k
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true (by lia))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false (by lia))],
    fold_ite_range, Nat.fold_congr (show min i i - (i - k) = min i k by lia)]
  congr 1
  funext t ht s
  rw [show i - k + t = i - min i k + t by lia]

/--
The steps of `fold_upper_band_rev` before the step for column `i`: `T` of the columns
`i + min (n - 1 - i) k, …, i + 1`.
-/
private theorem fold_upper_band_rev_pre {α : Type _} {n i : Nat} (hi : i < n) (k : Nat)
    (D : Nat → α → α) (T : Nat → α → α) (v : α) :
    Nat.fold (n - 1 - i) (fun kk _ s =>
        if i = n - 1 - kk then D (n - 1 - kk) s
        else if n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
            i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k then
          T (n - 1 - kk) s
        else s) v =
      Nat.fold (min (n - 1 - i) k) (fun t _ s => T (i + min (n - 1 - i) k - t) s) v := by
  rw [show (fun kk (_ : kk < n - 1 - i) s =>
        if i = n - 1 - kk then D (n - 1 - kk) s
        else if n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
            i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k then
          T (n - 1 - kk) s
        else s) =
      fun kk _ s => if n - 1 - i - min (n - 1 - i) k ≤ kk ∧ kk < n - 1 - i then
        T (n - 1 - kk) s else s from by
    funext kk hkk s
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia))]
    by_cases h' : n - 1 - kk - min (n - 1 - kk) k ≤ i ∧
        i < n - 1 - kk - min (n - 1 - kk) k + min (n - 1 - kk) k
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true (by lia))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false (by lia))],
    fold_ite_range, Nat.fold_congr (show min (n - 1 - i) (n - 1 - i) -
      (n - 1 - i - min (n - 1 - i) k) = min (n - 1 - i) k by lia)]
  congr 1
  funext t ht s
  rw [show n - 1 - (n - 1 - i - min (n - 1 - i) k + t) = i + min (n - 1 - i) k - t by lia]

private theorem toNat_add_bandBelow_sub {n k : Nat} (hn : n < USize.size) {j t : USize}
    (hj : j.toNat < n) (ht : t.toNat < (bandBelow n k j).toNat) :
    (j + bandBelow n k j - t).toNat = j.toNat + min (n - 1 - j.toNat) k - t.toNat ∧
      j.toNat + min (n - 1 - j.toNat) k - t.toNat < n := by
  have hb := toNat_bandBelow hn k j
  rw [hb] at ht
  constructor
  · grind
  · lia

private theorem toNat_bandBelow_sub {n k : Nat} (hn : n < USize.size) {j t : USize}
    (ht : t.toNat < (bandBelow n k j).toNat) :
    (bandBelow n k j - t).toNat = min (n - 1 - j.toNat) k - t.toNat ∧
      min (n - 1 - j.toNat) k - t.toNat < k + 1 := by
  have hb := toNat_bandBelow hn k j
  rw [hb] at ht
  constructor
  · rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; lia), hb]
  · lia

end BLAS
