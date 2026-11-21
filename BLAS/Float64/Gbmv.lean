/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Level2
import all BLAS.Internal

/-!
# General band matrix-vector products

A band matrix is stored as in the reference BLAS: an `m × n` matrix with `kl` subdiagonals and `ku`
superdiagonals is a matrix `A : Mat (kl + ku + 1) n` whose column `j` holds the elements of column
`j` of the band, with the element in row `i` of the band matrix in row `ku + i - j` of `A`, for
`j - ku ≤ i ≤ j + kl` and `i < m`. The other elements of `A` are not part of the band matrix, and
the routines don't read them.

`Mat.gbmv kl ku α A x β y` computes `α * A * x + β * y` and `Mat.gbmvT kl ku α A x β y` computes
`α * Aᵀ * x + β * y`, by the loops of the reference BLAS (`dgbmv`), with its special cases. Row `i`
of the band matrix has the columns `i - kl, …, min (n, i + ku + 1) - 1`, and column `j` the rows
`j - ku, …, min (m, j + kl + 1) - 1`, with subtractions that stop at `0`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {m n : Nat}

/-! ## The band storage -/

/--
The number of rows of a matrix with a column fits in a `USize`, when its array does, as the rows of
the storage of a band matrix.
-/
public theorem rows_lt_size {r : Nat} (A : Mat r n) (hs : A.data.size < USize.size) (hr : 0 < r)
    (hn : 0 < n) : r < USize.size := by
  have := A.index_lt (i := r - 1) (j := 0) (by lia) hn
  lia

/-- Element `l` of the rows `j - ku, …` of a band column is in the vector `y`. -/
private theorem band_index_eq (y : Vec m) (hs : y.data.size < USize.size) {kl ku : Nat}
    {j l : USize} (hl : l.toNat < (bandCount m kl ku j).toNat) :
    (y.off.toUSize + y.inc.toUSize * (bandLo ku j + l)).toNat =
      y.off + y.inc * (j.toNat - ku + l.toNat) := by
  have hm := Nat.lt_of_le_of_lt y.le_size hs
  have h := toNat_bandLo_add hm hl
  rw [y.toNat_index hs (by rw [h.1]; exact h.2), h.1]

/--
A loop over the rows `lo, …, lo + cnt - 1` of `y` is a `modifyAt` over all of `y` that maps the
elements `i` of the rows `lo ≤ i < lo + cnt`, if `lo + cnt ≤ m` or `cnt = 0`.
-/
public theorem modifyAt_band (y : Vec m) (c : Float64Array) (lo cnt : Nat)
    (hc : lo + cnt ≤ m ∨ cnt = 0) (G : Nat → Float → Float) :
    c.modifyAt (fun l => y.off + y.inc * (lo + l)) 0 cnt G =
      c.modifyAt y.stride.idx 0 m fun i v => if lo ≤ i ∧ i < lo + cnt then G (i - lo) v else v := by
  rcases hc with hc | hc
  · have e : (fun l => y.off + y.inc * (lo + l)) = (y.stride.shift lo).idx := by
      funext l; rw [Stride.idx_shift]; rfl
    rw [e, modifyAt_shift, modifyAt_widen (lo' := 0) (hi' := m) _ _ _ (Nat.zero_le _)
      (by lia) hc]
  · subst hc
    rw [modifyAt_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp only [Nat.add_zero, ite_eq_right_iff]
    intro h; lia

/--
A loop over the rows `lo, …, lo + cnt - 1` of `y`, followed by a write at row `j` outside them of a
value `w` of its element, is a `modifyAt` over all of `y`.
-/
public theorem set!_modifyAt_band (y : Vec m) (c : Float64Array) (hc : c.size = y.data.size)
    (lo cnt j : Nat) (hr : lo + cnt ≤ m ∨ cnt = 0) (hj : j < m) (hd : ¬(lo ≤ j ∧ j < lo + cnt))
    (G : Nat → Float → Float) (w : Float → Float) :
    (c.modifyAt (fun l => y.off + y.inc * (lo + l)) 0 cnt G).set! (y.off + y.inc * j)
        (w (c.modifyAt (fun l => y.off + y.inc * (lo + l)) 0 cnt G)[y.off + y.inc * j]!) =
      c.modifyAt y.stride.idx 0 m fun i v =>
        if i = j then w v else if lo ≤ i ∧ i < lo + cnt then G (i - lo) v else v := by
  have hinj : ∀ i, 0 ≤ i → i < m → ∀ j, 0 ≤ j → j < m → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits m c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  have hlt : y.stride.idx j < c.size := by rw [hc]; exact y.index_lt hj
  rw [modifyAt_band y c lo cnt hr G]
  have e : ∀ b : Float64Array, b.size = c.size →
      b.set! (y.off + y.inc * j) (w b[y.off + y.inc * j]!) =
        b.modifyAt y.stride.idx j (j + 1) fun _ v => w v := by
    intro b hb
    rw [modifyAt_of_lt _ _ (Nat.lt_succ_self j), modifyAt_self]
    rfl
  rw [e _ (by simp), modifyAt_widen (lo' := 0) (hi' := m) _ _ _ (Nat.zero_le _) (by lia) hj,
    modifyAt_modifyAt _ _ hinj]
  apply modifyAt_congr_fun
  intro i v _ _
  by_cases h : i = j
  · subst h; simp [hd]
  · simp [h, show ¬(j ≤ i ∧ i < j + 1) by lia]

/-- A write at element `j` of `x` is a `modifyAt` over all of `x`. -/
public theorem set!_eq_modifyAt_ite (x : Vec m) (a : Float64Array) (ha : a.size = x.data.size)
    {j : Nat} (hj : j < m) (w : Float) :
    a.set! (x.off + x.inc * j) w =
      a.modifyAt x.stride.idx 0 m fun i v => if i = j then w else v := by
  change a.set! (x.stride.idx j) w = _
  rw [← set_eq_set! _ (x.stride.idx j) _ (by rw [ha]; exact x.index_lt hj), set_eq_modifyAt,
    modifyAt_widen (lo' := 0) (hi' := m) _ _ _ (Nat.zero_le _) (by lia) hj]
  apply modifyAt_congr_fun
  intro i v _ _
  by_cases h : i = j
  · simp [h]
  · simp [h, show ¬(j ≤ i ∧ i < j + 1) by lia]

/--
A write at row `j` of `y` of a value `w` of its element, followed by a loop over the rows
`lo, …, lo + cnt - 1` of `y`, which don't include `j`, is a `modifyAt` over all of `y`.
-/
public theorem modifyAt_band_set! (y : Vec m) (c : Float64Array) (hc : c.size = y.data.size)
    (lo cnt j : Nat) (hr : lo + cnt ≤ m ∨ cnt = 0) (hj : j < m) (hd : ¬(lo ≤ j ∧ j < lo + cnt))
    (G : Nat → Float → Float) (w : Float → Float) :
    (c.set! (y.off + y.inc * j) (w c[y.off + y.inc * j]!)).modifyAt
        (fun l => y.off + y.inc * (lo + l)) 0 cnt G =
      c.modifyAt y.stride.idx 0 m fun i v =>
        if i = j then w v else if lo ≤ i ∧ i < lo + cnt then G (i - lo) v else v := by
  have hinj : ∀ i, 0 ≤ i → i < m → ∀ j, 0 ≤ j → j < m → y.stride.idx i = y.stride.idx j → i = j :=
    (show y.stride.Fits m c.size by rw [hc]; exact y.fits).injOn (Nat.le_refl _)
  have e : c.set! (y.off + y.inc * j) (w c[y.off + y.inc * j]!) =
      c.modifyAt y.stride.idx j (j + 1) fun _ v => w v := by
    rw [modifyAt_of_lt _ _ (Nat.lt_succ_self j), modifyAt_self]
    rfl
  rw [modifyAt_band y _ lo cnt hr G, e, modifyAt_widen (lo' := 0) (hi' := m) _ _ _
    (Nat.zero_le _) (by lia) hj, modifyAt_modifyAt _ _ hinj]
  apply modifyAt_congr_fun
  intro i v _ _
  by_cases h : i = j
  · subst h; simp [hd]
  · simp [h, show ¬(j ≤ i ∧ i < j + 1) by lia]

/-! ## `gbmv` -/

/--
The value of the loops of `gbmv` at the index `i` of `y`, from its old value `v`, on the arrays:
`betaMul β v`, plus the terms `α * x[j] * A[i, j]` of the columns `j` of row `i` of the band.
-/
@[expose] public def gbmvSumAt (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (i : Nat) (v : Float) : Float :=
  Nat.fold (min n (i + ku + 1) - (i - kl)) (fun t _ s =>
      s + α * x.data[x.off + x.inc * (i - kl + t)]! *
        A.data[A.off + A.ld * (i - kl + t) + (ku + i - (i - kl + t))]!)
    (betaMul β v)

/--
The step of `gbmv` for column `j`: adds `α * x[j] * A[i, j]` to `y[i]`, for the rows `i` of column
`j` of the band, in the array `c`.
-/
@[expose] public def gbmvCol (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (y : Vec m) (j : Nat) (c : Float64Array) : Float64Array :=
  c.modifyAt y.stride.idx 0 m fun i v =>
    if i - kl ≤ j ∧ j < i + ku + 1 then
      v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (ku + i - j)]!
    else v

/-- The loops of `gbmv` on the array `c` of `y`, already scaled by `β`. -/
public def gbmvCols (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n) (y : Vec m)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) : Float64Array :=
  have hnu : n.toUSize.toNat = n := x.toNat_toUSize hs.2.1
  have hm : m < USize.size := Nat.lt_of_le_of_lt y.le_size hs.2.2
  let nu := n.toUSize
  let xo := x.off.toUSize
  let xc := x.inc.toUSize
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  (inplace c do
    for j in 0...nu do
      have hjn : j.toNat < n := by lia
      have hk : kl + ku + 1 < USize.size := A.rows_lt_size hs.1 (by lia) (by lia)
      let t := α * x.uget xo xc rfl rfl hs.2.1 j hjn
      let lo := bandLo ku j
      let r0 := bandRow0 ku j
      for l in 0...bandCount m kl ku j do
        have hl := toNat_bandLo_add hm (by assumption)
        have hr := toNat_bandRow0_add hm hk (by assumption)
        have hi : (lo + l).toNat < m := hl.1 ▸ hl.2
        have hq : (o + cc * (lo + l)).toNat < c.size :=
          hc ▸ ho ▸ hcc ▸ y.toNat_index_lt hs.2.2 hi
        c[o + cc * (lo + l)] :=
          c[o + cc * (lo + l)] + t * A.uget ao al rfl rfl hs.1 (r0 + l) j (hr.1 ▸ hr.2) hjn).2

public theorem gbmvCols_eq (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (y : Vec m)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size)
    (o cc : USize) (ho : y.off.toUSize = o) (hcc : y.inc.toUSize = cc)
    (c : Float64Array) (hc : c.size = y.data.size) :
    gbmvCols kl ku α A x y hs o cc ho hcc c hc = iterRange (gbmvCol kl ku α A x y) 0 n c := by
  have hnu := x.toNat_toUSize hs.2.1
  have hm : m < USize.size := Nat.lt_of_le_of_lt y.le_size hs.2.2
  subst ho hcc
  unfold gbmvCols
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := gbmvCol kl ku α A x y)
    (hF := fun _ _ => by unfold gbmvCol; exact size_modifyAt _ _ _ _ _)]
  · simp only [Tail.run_done, USize.toNat_zero, hnu]
  · intro j _ hj next a h
    rw [hnu] at hj
    have hk : kl + ku + 1 < USize.size := A.rows_lt_size hs.1 (by lia) (by lia)
    rw [Tail.run_forInFrom_modify (idx := fun l => y.off + y.inc * (j.toNat - ku + l))
      (he := fun l _ hl => band_index_eq y hs.2.2 hl)
      (G := fun l v => v + α * x.data[x.off + x.inc * j.toNat]! *
        A.data[A.off + A.ld * j.toNat + (ku - j.toNat + l)]!)]
    · congr 1
      rw [toNat_bandCount hm, USize.toNat_zero, modifyAt_band y a _ _ (by lia), gbmvCol]
      apply modifyAt_congr_fun
      intro i v _ hi
      by_cases hb : i - kl ≤ j.toNat ∧ j.toNat < i + ku + 1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by lia)), ite_eq_left_of_eq_true _ _ (eq_true hb),
          show ku - j.toNat + (i - (j.toNat - ku)) = ku + i - j.toNat by lia]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by lia)),
          ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · intro l hl₀ hl v
      have hr := toNat_bandRow0_add hm hk hl
      simp only [Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, hr.1,
        getElem_eq_getElem!]

/-- The array of `gbmv`. -/
public def gbmvData (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n) (β : Float)
    (y : Vec m) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    gbmvCols kl ku α A x y hs y.off.toUSize y.inc.toUSize rfl rfl (y.scalBetaData β)
      (by rw [Vec.scalBetaData_eq, size_modifyAt])
  else y.data.modifyAt y.stride.idx 0 m (gbmvSumAt kl ku α A x β)

public theorem gbmvData_eq (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) :
    gbmvData kl ku α A x β y = y.data.modifyAt y.stride.idx 0 m (gbmvSumAt kl ku α A x β) := by
  unfold gbmvData
  split
  · rename_i hs
    have hinj := y.fits.injOn (lo := 0) (Nat.le_refl _)
    rw [gbmvCols_eq, Vec.scalBetaData_eq]
    rw [show gbmvCol kl ku α A x y = fun j c => c.modifyAt y.stride.idx 0 m fun i v =>
        if i - kl ≤ j ∧ j < i + ku + 1 then
          v + α * x.data[x.off + x.inc * j]! * A.data[A.off + A.ld * j + (ku + i - j)]!
        else v from rfl,
      iterRange_modifyAt _ _ hinj, modifyAt_modifyAt _ _ hinj]
    apply modifyAt_congr_fun
    intro i v _ _
    rw [fold_ite_range, gbmvSumAt]
  · rfl

/--
The value of `gbmv` at the index `i` of `y`, from its old value `v`, on the arrays, with the special
cases of the reference BLAS: `v` when `n = 0`, and `betaMul β v` when `α = 0`.
-/
@[expose] public def gbmvAt (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (i : Nat) (v : Float) : Float :=
  if n = 0 then v else if α == 0 then betaMul β v else gbmvSumAt kl ku α A x β i v

/--
`gbmv kl ku α A x β y` is `α * A * x + β * y` for the `m × n` band matrix with `kl` subdiagonals
and `ku` superdiagonals stored in `A`, with the operations of the reference BLAS (`dgbmv` with
`TRANS = 'N'`), in its order for each element: it scales `y` by `β`, then adds `α * x[j]` times
column `j` of the band to the rows `j - ku, …, j + kl` of `y`, for `j = 0, …, n - 1`. As in the
reference BLAS, it returns `y` when `n = 0`, sets `y` to `0` without reading it when `β = 0`, and
only scales `y` when `α = 0`, without reading `A` or `x`. It updates `y` in place when its array is
not shared, leaves the elements of the array outside `y` unchanged, and reads only the band of `A`.
-/
@[expose] public def gbmv (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) : Vec m :=
  if n = 0 then y
  else if α == 0 then
    { data := y.scalBetaData β
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [Vec.scalBetaData_eq, size_modifyAt]; exact y.bound }
  else
    { data := gbmvData kl ku α A x β y
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [gbmvData_eq, size_modifyAt]; exact y.bound }

/-- The array of `gbmv kl ku α A x β y` is the array of `y` with its elements updated. -/
public theorem data_gbmv (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) :
    (gbmv kl ku α A x β y).data = y.data.modifyAt y.stride.idx 0 m (gbmvAt kl ku α A x β) := by
  unfold gbmv
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
    rw [modifyAt_congr_fun _ _ (g' := fun _ v => v) (fun i v _ _ => by simp [gbmvAt, hn]),
      modifyAt_id]
  · simp only [hn, ↓reduceIte]
    cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte, gbmvData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gbmvAt, hn, hα]
    · simp only [↓reduceIte, Vec.scalBetaData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gbmvAt, hn, hα]

@[simp] public theorem off_gbmv (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) : (gbmv kl ku α A x β y).off = y.off := by
  unfold gbmv; split <;> (try split) <;> rfl

@[simp] public theorem inc_gbmv (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) : (gbmv kl ku α A x β y).inc = y.inc := by
  unfold gbmv; split <;> (try split) <;> rfl

/--
Element `i` of `gbmv kl ku α A x β y` is `y[i]` when `n = 0`, `betaMul β y[i]` when `α = 0`, and
otherwise `betaMul β y[i]`, plus the terms `α * x[j] * A[ku + i - j, j]` for
`j = i - kl, …, min (n, i + ku + 1) - 1`, added from the left.
-/
public theorem getElem_gbmv (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec n)
    (β : Float) (y : Vec m) (i : Nat) (h : i < m) :
    (gbmv kl ku α A x β y)[i] =
      if n = 0 then y[i] else if α == 0 then betaMul β y[i]
      else Nat.fold (min n (i + ku + 1) - (i - kl)) (fun t _ s =>
        s + α * x[i - kl + t]'(by lia) * A[(ku + i - (i - kl + t), i - kl + t)]'⟨by lia, by lia⟩)
        (betaMul β y[i]) := by
  rw [Vec.getElem_of_data_eq_modifyAt _ (data_gbmv kl ku α A x β y) (off_gbmv kl ku α A x β y)
    (inc_gbmv kl ku α A x β y) i h, gbmvAt, gbmvSumAt]
  congr
  funext t ht s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt (by lia)
    (by lia))]
  rfl

/-! ## `gbmvT` -/

/--
The dot product of the band of column `j` of `A` and of `x`, on the arrays: the terms
`A[ku + i - j, j] * x[i]` for the rows `i = j - ku, …, min (m, j + kl + 1) - 1`, from `0`.
-/
@[expose] public def gbmvTDot (kl ku : Nat) (A : Mat (kl + ku + 1) n) (x : Vec m) (j : Nat) :
    Float :=
  Nat.fold (min m (j + kl + 1) - (j - ku)) (fun l _ s =>
      s + A.data[A.off + A.ld * j + (ku - j + l)]! * x.data[x.off + x.inc * (j - ku + l)]!) 0

/--
The value of the loops of `gbmvT` at the index `j` of `y`, from its old value `v`, on the arrays:
`betaMul β v + α * gbmvTDot kl ku A x j`.
-/
@[expose] public def gbmvTSumAt (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (j : Nat) (v : Float) : Float :=
  betaMul β v + α * gbmvTDot kl ku A x j

/-- `gbmvTDot`, as a loop over `USize` indices. -/
public def gbmvTDotU (kl ku : Nat) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size) (ao al xo xc : USize)
    (hao : A.off.toUSize = ao) (hal : A.ld.toUSize = al) (hxo : x.off.toUSize = xo)
    (hxc : x.inc.toUSize = xc) (j : USize) (hj : j.toNat < n) : Float :=
  have hm : m < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
  have hk : kl + ku + 1 < USize.size := A.rows_lt_size hs.1 (by lia) (by lia)
  let lo := bandLo ku j
  let r0 := bandRow0 ku j
  foldUpTo (bandCount m kl ku j).toNat
    (fun l _ s => s + A.data[A.off + A.ld * j.toNat + (ku - j.toNat + l)]! *
      x.data[x.off + x.inc * (j.toNat - ku + l)]!)
    (fun l hl s =>
      have hl' := toNat_bandLo_add hm hl
      have hr := toNat_bandRow0_add hm hk hl
      s + A.uget ao al hao hal hs.1 (r0 + l) j (hr.1 ▸ hr.2) hj *
        x.uget xo xc hxo hxc hs.2 (lo + l) (hl'.1 ▸ hl'.2)) 0

public theorem gbmvTDotU_eq (kl ku : Nat) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (hs : A.data.size < USize.size ∧ x.data.size < USize.size) (ao al xo xc : USize)
    (hao : A.off.toUSize = ao) (hal : A.ld.toUSize = al) (hxo : x.off.toUSize = xo)
    (hxc : x.inc.toUSize = xc) (j : USize) (hj : j.toNat < n) :
    gbmvTDotU kl ku A x hs ao al xo xc hao hal hxo hxc j hj = gbmvTDot kl ku A x j.toNat := by
  have hm : m < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
  have hk : kl + ku + 1 < USize.size := A.rows_lt_size hs.1 (by lia) (by lia)
  unfold gbmvTDotU
  rw [foldUpTo_eq _ _ _ (fun l hl s => by
    have hl' := toNat_bandLo_add hm hl
    have hr := toNat_bandRow0_add hm hk hl
    simp only [Vec.uget_eq_getElem, uget_eq_getElem, Vec.getElem_def, getElem_def, hl'.1, hr.1,
      getElem_eq_getElem!]), gbmvTDot]
  exact Nat.fold_congr (toNat_bandCount hm _ _ _) _ _

/-- The array of `gbmvT`. -/
public def gbmvTData (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m) (β : Float)
    (y : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2.2
    let a := y.data
    let o := y.off.toUSize
    let c := y.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    (inplace a do
      for j in 0...nu do
        have hk : (o + c * j).toNat < a.size := y.toNat_index_lt hs.2.2 (by lia)
        a[o + c * j] := betaMul β a[o + c * j] +
          α * gbmvTDotU kl ku A x ⟨hs.1, hs.2.1⟩ ao al xo xc rfl rfl rfl rfl j (by lia)).2
  else y.data.modifyAt y.stride.idx 0 n (gbmvTSumAt kl ku α A x β)

public theorem gbmvTData_eq (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (y : Vec n) :
    gbmvTData kl ku α A x β y = y.data.modifyAt y.stride.idx 0 n (gbmvTSumAt kl ku α A x β) := by
  unfold gbmvTData
  split
  · rename_i hs
    have he := y.loop_idx hs.2.2
    have hnu := y.toNat_toUSize hs.2.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify (G := gbmvTSumAt kl ku α A x β) (he := he)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro j _ hj v
      rw [gbmvTDotU_eq]
      rfl
  · rfl

/--
The value of `gbmvT` at the index `j` of `y`, from its old value `v`, on the arrays, with the
special cases of the reference BLAS: `v` when `m = 0`, and `betaMul β v` when `α = 0`.
-/
@[expose] public def gbmvTAt (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (j : Nat) (v : Float) : Float :=
  if m = 0 then v else if α == 0 then betaMul β v else gbmvTSumAt kl ku α A x β j v

/--
`gbmvT kl ku α A x β y` is `α * Aᵀ * x + β * y` for the `m × n` band matrix with `kl` subdiagonals
and `ku` superdiagonals stored in `A`, with the operations of the reference BLAS (`dgbmv` with
`TRANS = 'T'`), in its order for each element: for each `j`, it sums the products `A[i, j] * x[i]`
of the band of column `j` and of `x`, for `i = j - ku, …, j + kl`, from `0`, and adds `α` times the
sum to `β * y[j]`. As in the reference BLAS, it returns `y` when `m = 0`, sets `y[j]` to `0`
without reading it before adding the sum when `β = 0`, and only scales `y` when `α = 0`, without
reading `A` or `x`. It updates `y` in place when its array is not shared, leaves the elements of the
array outside `y` unchanged, and reads only the band of `A`.
-/
@[expose] public def gbmvT (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (y : Vec n) : Vec n :=
  if m = 0 then y
  else if α == 0 then
    { data := y.scalBetaData β
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [Vec.scalBetaData_eq, size_modifyAt]; exact y.bound }
  else
    { data := gbmvTData kl ku α A x β y
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [gbmvTData_eq, size_modifyAt]; exact y.bound }

/-- The array of `gbmvT kl ku α A x β y` is the array of `y` with its elements updated. -/
public theorem data_gbmvT (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (y : Vec n) :
    (gbmvT kl ku α A x β y).data = y.data.modifyAt y.stride.idx 0 n (gbmvTAt kl ku α A x β) := by
  unfold gbmvT
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]
    rw [modifyAt_congr_fun _ _ (g' := fun _ v => v) (fun i v _ _ => by simp [gbmvTAt, hm]),
      modifyAt_id]
  · simp only [hm, ↓reduceIte]
    cases hα : α == 0
    · simp only [Bool.false_eq_true, ↓reduceIte, gbmvTData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gbmvTAt, hm, hα]
    · simp only [↓reduceIte, Vec.scalBetaData_eq]
      exact modifyAt_congr_fun _ _ fun i v _ _ => by simp [gbmvTAt, hm, hα]

@[simp] public theorem off_gbmvT (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (y : Vec n) : (gbmvT kl ku α A x β y).off = y.off := by
  unfold gbmvT; split <;> (try split) <;> rfl

@[simp] public theorem inc_gbmvT (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (y : Vec n) : (gbmvT kl ku α A x β y).inc = y.inc := by
  unfold gbmvT; split <;> (try split) <;> rfl

/--
Element `j` of `gbmvT kl ku α A x β y` is `y[j]` when `m = 0`, `betaMul β y[j]` when `α = 0`, and
otherwise `betaMul β y[j] + α * s`, where `s` sums the terms `A[ku + i - j, j] * x[i]` for
`i = j - ku, …, min (m, j + kl + 1) - 1` from the left, starting at `0`.
-/
public theorem getElem_gbmvT (kl ku : Nat) (α : Float) (A : Mat (kl + ku + 1) n) (x : Vec m)
    (β : Float) (y : Vec n) (j : Nat) (h : j < n) :
    (gbmvT kl ku α A x β y)[j] =
      if m = 0 then y[j] else if α == 0 then betaMul β y[j]
      else betaMul β y[j] + α * Nat.fold (min m (j + kl + 1) - (j - ku)) (fun l _ s =>
        s + A[(ku - j + l, j)]'⟨by lia, h⟩ * x[j - ku + l]'(by lia)) 0 := by
  rw [Vec.getElem_of_data_eq_modifyAt _ (data_gbmvT kl ku α A x β y) (off_gbmvT kl ku α A x β y)
    (inc_gbmvT kl ku α A x β y) j h, gbmvTAt, gbmvTSumAt, gbmvTDot]
  congr
  funext l hl s
  rw [getElem!_pos x.data _ (x.index_lt (by lia)), getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

end Mat

end BLAS.Float64
