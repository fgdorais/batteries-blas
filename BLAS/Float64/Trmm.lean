/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Trmv
public import BLAS.Float64.Trsm
import all BLAS.Internal

/-!
# Triangular product with several columns, on the left

`Mat.trmm uplo d α A B` computes `α * A * B` and `Mat.trmmT uplo d α A B` computes
`α * Aᵀ * B`,
for a triangular matrix `A`, over `B`, by the loops of the reference BLAS for `SIDE = 'L'`. Each
element gets the operations of those loops, in the same order. As in the reference BLAS, both set
`B` to `0` without reading `A` or `B` when `α = 0`.

`trmm` multiplies each column of `B` by the loops of `trmv`, after scaling it by `α`: the reference
loops compute `α * B[k, j]` as they reach element `k`, before they write it, which is the same
value. `trmmT` multiplies each column by the dot products of `trmvT`, and scales the result by `α`,
as the reference loops do. For the upper triangle, the reference `trmm` adds the terms of each
element in increasing order, unlike `trmv`, so `trmmT` multiplies its columns by `trmvTUpperAsc`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {m n : Nat}

/-- Element `l` of a vector, by `getElem!` on its array. -/
private theorem getElem!_index (x : Vec n) {l : Nat} (hl : l < n) :
    x.data[x.off + x.inc * l]! = x[l] := by
  rw [getElem!_pos x.data _ (x.index_lt hl)]; rfl

/-! ## The transposed upper product, with the terms in increasing order -/

/--
Element `j` of `Aᵀ * x` for the upper triangle of `A`, on the arrays, with the terms in increasing
order: `x[j] * A[j, j]`, plus the terms `A[i, j] * x[i]` for `i = 0, …, j - 1`.
-/
@[expose] public def trmvTUpperAsc (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float :=
  Nat.fold j (fun t _ s => s + A.data[A.off + A.ld * j + t]! * x.data[x.off + x.inc * t]!)
    (d.mul x.data[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged and
maps the variable by a fold.
-/
private theorem iterRange_fst (g : Nat → Float64Array → Float → Float) (k : Nat) (t : Float)
    (a : Float64Array) :
    iterRange (fun i p => (g i p.2 p.1, p.2)) 0 k (t, a) =
      (Nat.fold k (fun i _ s => g i a s) t, a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/--
The step `k` of the transposed upper product in increasing order: set element `j = n - 1 - k` from
the elements above it, which are still those of `x`.
-/
@[expose] public def trmvTUpperAscStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float64Array) : Float64Array :=
  let j := n - 1 - k
  let t := Nat.fold j (fun t _ s =>
      s + A.data[A.off + A.ld * j + t]! * b[x.off + x.inc * t]!)
    (d.mul b[x.off + x.inc * j]! A.data[A.off + A.ld * j + j]!)
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The array of the transposed upper product in increasing order. -/
public def trmvTUpperAscData (d : Diag) (A : Mat n n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    (inplace a do
      for k in 0...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        for t in 0...(nu - 1 - k) with
            (s := d.mul v (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)) do
          have hi : t.toNat < n := by grind
          have hk' : (o + c * t).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s + A.uget ao al rfl rfl hs.1 t (nu - 1 - k) hi hjn * a[o + c * t]
        a[o + c * (nu - 1 - k)] := s).2
  else iterRange (trmvTUpperAscStep d A x) 0 n x.data

public theorem trmvTUpperAscData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTUpperAscData d A x = iterRange (trmvTUpperAscStep d A x) 0 n x.data := by
  unfold trmvTUpperAscData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trmvTUpperAscStep d A x)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro k _ hk next a h
      rw [hnu] at hk
      have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 + A.data[A.off + A.ld * (n - 1 - k.toNat) + t]! * p.2[x.off + x.inc * t]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, hj, iterRange_fst (fun t a s =>
          s + A.data[A.off + A.ld * (n - 1 - k.toNat) + t]! * a[x.off + x.inc * t]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
            x.off + x.inc * (n - 1 - k.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hj]
        rw [trmvTUpperAscStep, ← set_eq_modifyAt _ _ _ _
          (by rw [Vec.idx_stride, h]; exact x.index_lt (by lia))]
        simp only [hp, hj, Vec.idx_stride, uget_eq_getElem, getElem_def,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
            (A.index_lt (by lia) (by lia))]
      · intro t _ ht next' b a' h'
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
        rw [hj] at ht
        have hp : (x.off.toUSize + x.inc.toUSize * t).toNat = x.off + x.inc * t.toNat :=
          x.toNat_index hs.2 (by lia)
        simp only [hp, hj, getElem!_pos a' (x.off + x.inc * t.toNat)
            (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + t.toNat)
            (A.index_lt (by lia) (by lia))]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are multiplied, and the others are unchanged.
-/
theorem iterRange_trmvTUpperAscStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k ≤ n) :
    iterRange (trmvTUpperAscStep d A x) 0 k x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v =>
        if n - k ≤ i then trmvTUpperAsc d A x i else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, i ≤ n - 1 - k → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trmvTUpperAsc d A x i else v)[x.off + x.inc * i]! =
        x.data[x.off + x.inc * i]! := by
      intro i hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt (by lia : i < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        ite_eq_right (by lia), getElem!_pos x.data _ (x.index_lt (by lia))]
    have ht : Nat.fold (n - 1 - k) (fun t _ s =>
          s + A.data[A.off + A.ld * (n - 1 - k) + t]! *
            (x.data.modifyAt x.stride.idx 0 n fun i v =>
              if n - k ≤ i then trmvTUpperAsc d A x i else v)[x.off + x.inc * t]!)
          (d.mul (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if n - k ≤ i then trmvTUpperAsc d A x i else v)[x.off + x.inc * (n - 1 - k)]!
            A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]!) =
        trmvTUpperAsc d A x (n - 1 - k) := by
      rw [hr (n - 1 - k) (Nat.le_refl _), trmvTUpperAsc]
      congr 1
      funext t ht s
      rw [hr t (by lia)]
    simp only [trmvTUpperAscStep, ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _
      (Nat.zero_le _) (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/-- The array of the transposed upper product in increasing order. -/
public theorem trmvTUpperAscData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTUpperAscData d A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => trmvTUpperAsc d A x i := by
  rw [trmvTUpperAscData_eq_iterRange, iterRange_trmvTUpperAscStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-- The column product of `trmmT`: `trmvTUpperAsc`, or `trmvTLower` for the lower triangle. -/
@[expose] public def trmvTAscProd (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => trmvTUpperAsc d A x
  | .lower => trmvTLower d A x

/-- The array of the column product of `trmmT`. -/
@[expose] public def trmvTAscData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => trmvTUpperAscData d A x
  | .lower => trmvTLowerData d A x

public theorem trmvTAscData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trmvTAscData uplo d A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => trmvTAscProd uplo d A x i := by
  cases uplo
  · exact trmvTUpperAscData_eq d A x
  · exact trmvTLowerData_eq d A x

/-- The column product of `trmmT`, as a vector over `x`. -/
@[expose] public def trmvTAsc (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Vec n where
  data := trmvTAscData uplo d A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [trmvTAscData_eq, size_modifyAt]; exact x.bound

/-! ## The column products depend only on the elements of the vector -/

theorem trmvProd_congr (uplo : Uplo) (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) (i : Nat)
    (hi : i < n) : trmvProd uplo d A x i = trmvProd uplo d A y i := by
  cases uplo
  · simp only [trmvProd, trmvUpper, h i hi]
    congr 1
    funext t ht s
    rw [h _ (by lia)]
  · simp only [trmvProd, trmvLower, h i hi]
    congr 1
    funext t ht s
    rw [h _ (by lia)]

theorem trmvTAscProd_congr (uplo : Uplo) (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) (i : Nat)
    (hi : i < n) : trmvTAscProd uplo d A x i = trmvTAscProd uplo d A y i := by
  cases uplo
  · simp only [trmvTAscProd, trmvTUpperAsc, h i hi]
    congr 1
    funext t ht s
    rw [h _ (by lia)]
  · simp only [trmvTAscProd, trmvTLower, h i hi]
    congr 1
    funext t ht s
    rw [h _ (by lia)]

/-! ## A loop over the columns -/

/-- Column `j` of the array `a` of a matrix with offset `off` and leading dimension `ld`. -/
@[expose] public def colVec (a : Float64Array) (off ld j : Nat) : Vec m :=
  Vec.ofFn fun l => a[off + ld * j + l.val]!

private theorem size_colOf (F : Vec m → Float64Array) (hF : ∀ x, (F x).size = x.data.size)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array)
    (hb : b.size = sz) (j : Nat) (hj : j < n) : (F (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [hF]; exact hb

/--
The loop over the columns from `j` of the array `b` of an `m × n` matrix, which maps each column
`x` to the array `F x`. It takes the offset and the leading dimension of the matrix rather than the
matrix, which would keep a second reference to its array.
-/
public def colLoop (F : Vec m → Float64Array) (hF : ∀ x, (F x).size = x.data.size)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (j : Nat)
    (b : Float64Array) (hb : b.size = sz) : Float64Array :=
  if hj : j < n then
    colLoop F hF off ld sz hsz (j + 1) (F (colOf off ld sz hsz b hb j hj))
      (size_colOf F hF off ld sz hsz b hb j hj)
  else b
termination_by n - j

/-- An element of a column `j` outside the columns of a `mapMat` is unchanged. -/
private theorem getElem!_mapMat_col_of_not (a : Float64Array) (off ld lo hi : Nat)
    (g : Nat → Nat → Float → Float) (hml : m ≤ ld) {j : Nat} (hj : ¬(lo ≤ j ∧ j < hi))
    {l : Nat}
    (hl : l < m) : (mapMat a off ld m lo hi g)[off + ld * j + l]! = a[off + ld * j + l]! := by
  by_cases hq : off + ld * j + l < a.size
  · rw [getElem!_pos _ _ (by rw [size_mapMat]; exact hq), getElem!_pos a _ hq,
      getElem_mapMat_of_ne _ _ _ _ _ _ _ (fun i' j' hi' h₁ h₂ e' => by
        by_cases hjj : j = j'
        · subst hjj; exact hj ⟨h₁, h₂⟩
        · exact col_index_ne hl hi' hml hjj e') hq]
  · rw [getElem!_neg _ _ (by rw [size_mapMat]; exact hq), getElem!_neg a _ hq]

/--
`colLoop` maps each column `j` of `B` to the elements `G (colVec B.data B.off B.ld j) i`, when `F`
maps the elements of a vector `x` to `G x i`, which depends only on the elements of `x`.
-/
public theorem colLoop_eq (F : Vec m → Float64Array) (hF : ∀ x, (F x).size = x.data.size)
    (G : Vec m → Nat → Float)
    (hFG : ∀ x, F x = x.data.modifyAt x.stride.idx 0 m fun i _ => G x i)
    (hG : ∀ x y : Vec m,
      (∀ l, l < m → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) →
      ∀ i, i < m → G x i = G y i)
    (B : Mat m n) :
    colLoop F hF B.off B.ld B.data.size B.bound 0 B.data rfl =
      mapMat B.data B.off B.ld m 0 n fun i j _ => G (colVec B.data B.off B.ld j) i := by
  suffices ∀ j, j ≤ n → ∀ b hb, b = mapMat B.data B.off B.ld m 0 j
      (fun i j _ => G (colVec B.data B.off B.ld j) i) →
      colLoop F hF B.off B.ld B.data.size B.bound j b hb =
        mapMat B.data B.off B.ld m 0 n fun i j _ => G (colVec B.data B.off B.ld j) i from
    this 0 (Nat.zero_le _) _ rfl (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm
  intro j hj b hb hinv
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j b with
  | ind e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he0
    · obtain rfl : j = n := by lia
      rw [colLoop, dite_eq_right (Nat.lt_irrefl _), hinv]
    have hjn : j < n := by lia
    rw [colLoop, dite_eq_left hjn]
    refine ih (n - (j + 1)) (by lia) (j + 1) hjn _ _ ?_ rfl
    have hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = B.data[B.off + B.ld * j + l]! := by
      intro l hl
      rw [hinv, getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hl]
    rw [hFG, ← modifyAt_col_mapMat _ _ _ B.le_ld j, ← hinv]
    simp only [colOf, Vec.stride]
    apply modifyAt_congr_fun
    intro i v _ hi
    apply hG _ _ _ i hi
    intro l hl
    rw [getElem!_index (colVec B.data B.off B.ld j) hl, colVec, Vec.getElem_ofFn]
    dsimp only
    rw [Nat.one_mul, hcol l hl]

/-! ## `trmm` -/

/-- The column map of `trmm`: scale the column by `α`, then multiply it by `trmv`. -/
@[expose] public def trmmCol (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (x : Vec m) :
    Float64Array :=
  trmvData uplo d A (Vec.scal α x)

private theorem size_trmmCol (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (x : Vec m) :
    (trmmCol uplo d α A x).size = x.data.size := by
  rw [trmmCol, trmvData_eq, size_modifyAt]
  show (Vec.scalData α x).size = _
  rw [Vec.scalData_eq, size_modifyAt]

/--
The value of `trmm` at `(i, j)`: `0` when `α = 0`, and element `i` of the product of `A` with
`α * B[:, j]` by `trmv` otherwise.
-/
@[expose] public def trmmAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) : Float :=
  if α == 0 then 0 else trmvProd uplo d A (scaledCol α B j) i

/-- The array of `trmm`. -/
public def trmmData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0
  else colLoop (trmmCol uplo d α A) (size_trmmCol uplo d α A) B.off B.ld B.data.size B.bound 0
    B.data rfl

/-- The elements of `Vec.scal α x` are `α` times those of `x`, by `getElem!`. -/
private theorem getElem!_scal (α : Float) (x : Vec n) {l : Nat} (hl : l < n) :
    (Vec.scal α x).data[(Vec.scal α x).off + (Vec.scal α x).inc * l]! =
      α * x.data[x.off + x.inc * l]! := by
  rw [getElem!_index _ hl, Vec.getElem_scal, getElem!_index _ hl]

public theorem trmmData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    trmmData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trmmAt uplo d α A B i j := by
  unfold trmmData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [colLoop_eq _ _ (fun x i => trmvProd uplo d A (Vec.scal α x) i)]
    · apply mapMat_congr
      intro i j v hi _ _
      simp only [trmmAt, hα, Bool.false_eq_true, ↓reduceIte]
      apply trmvProd_congr _ _ _ _ i hi
      intro l hl
      rw [getElem!_scal α _ hl, getElem!_index _ hl, getElem!_index _ hl, colVec, scaledCol,
        Vec.getElem_ofFn, Vec.getElem_ofFn]
    · intro x
      rw [trmmCol, trmvData_eq]
      show (Vec.scalData α x).modifyAt x.stride.idx 0 m _ = _
      rw [Vec.scalData_eq, modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    · intro x y h i hi
      apply trmvProd_congr _ _ _ _ i hi
      intro l hl
      rw [getElem!_scal α _ hl, getElem!_scal α _ hl, h l hl]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trmmAt, betaMul, hα, show ((0 : Float) == 0) = true from rfl]

/--
`trmm uplo d α A B` is `α * A * B` for the triangle `uplo` of `A`, with a unit diagonal if `d` is
`.unit`, over `B`, by the loops of the reference BLAS for `SIDE = 'L'` and `TRANSA = 'N'`: for each
column `j` of `B`, it multiplies `α * B[:, j]` by `A` with the loops of `trmv`. It updates `B` in
place when its array is not shared, and leaves the elements of the array outside `B` unchanged. As
in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when `α = 0`, and reads only
the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`.
-/
@[expose] public def trmm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Mat m n where
  data := trmmData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trmmData_eq, size_mapMat]; exact B.bound

/-- The array of `trmm uplo d α A B` is the array of `B` with its elements multiplied. -/
public theorem data_trmm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    (trmm uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trmmAt uplo d α A B i j :=
  trmmData_eq uplo d α A B

@[simp] public theorem off_trmm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trmm uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trmm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trmm uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trmm uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trmm (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) : (trmm uplo d α A B)[(i, j)] = trmmAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trmm uplo d α A B) rfl rfl i j h

/-- An element of `scaledCol α B j`, by `getElem!`, is `α * B[l, j]`. -/
private theorem getElem!_scaledCol (α : Float) (B : Mat m n) {l j : Nat} (hl : l < m)
    (hj : j < n) :
    (scaledCol α B j).data[(scaledCol α B j).off + (scaledCol α B j).inc * l]! =
      α * B[(l, j)] := by
  rw [getElem!_index _ hl, scaledCol, Vec.getElem_ofFn]
  dsimp only
  rw [getElem!_pos B.data _ (B.index_lt hl hj)]
  rfl

/--
Element `(i, j)` of `trmm .upper d α A B` is `0` when `α = 0`, and otherwise
`(α * B[i, j]) * A[i, i]`, or `α * B[i, j]` for a unit diagonal, plus the terms
`(α * B[k, j]) * A[i, k]` for `k = i + 1, …, m - 1`.
-/
public theorem getElem_trmm_upper (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trmm .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else Nat.fold (m - 1 - i) (fun t _ s =>
          s + α * B[(i + 1 + t, j)]'⟨by lia, h.2⟩ * A[(i, i + 1 + t)]'⟨h.1, by lia⟩)
        (d.mul (α * B[(i, j)]) A[(i, i)]) := by
  rw [getElem_trmm _ _ _ _ _ _ _ h, trmmAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmvProd, trmvUpper,
      getElem!_scaledCol α B h.1 h.2]
    rw [getElem!_pos A.data (A.off + A.ld * i + i) (A.index_lt h.1 h.1)]
    congr 1
    funext t ht s
    rw [getElem!_scaledCol α B (by lia) h.2, getElem!_pos A.data _ (A.index_lt h.1 (by lia))]
    rfl
  · rfl

/--
Element `(i, j)` of `trmm .lower d α A B` is `0` when `α = 0`, and otherwise
`(α * B[i, j]) * A[i, i]`, or `α * B[i, j]` for a unit diagonal, plus the terms
`(α * B[k, j]) * A[i, k]` for `k = i - 1, …, 0`.
-/
public theorem getElem_trmm_lower (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trmm .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else Nat.fold i (fun t _ s =>
          s + α * B[(i - 1 - t, j)]'⟨by lia, h.2⟩ * A[(i, i - 1 - t)]'⟨h.1, by lia⟩)
        (d.mul (α * B[(i, j)]) A[(i, i)]) := by
  rw [getElem_trmm _ _ _ _ _ _ _ h, trmmAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmvProd, trmvLower,
      getElem!_scaledCol α B h.1 h.2]
    rw [getElem!_pos A.data (A.off + A.ld * i + i) (A.index_lt h.1 h.1)]
    congr 1
    funext t ht s
    rw [getElem!_scaledCol α B (by lia) h.2, getElem!_pos A.data _ (A.index_lt h.1 (by lia))]
    rfl
  · rfl

/-! ## `trmmT` -/

/-- The column map of `trmmT`: multiply the column by `trmvTAsc`, then scale it by `α`. -/
@[expose] public def trmmTCol (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (x : Vec m) :
    Float64Array :=
  Vec.scalData α (trmvTAsc uplo d A x)


/--
The value of `trmmT` at `(i, j)`: `0` when `α = 0`, and `α` times element `i` of the product of
`Aᵀ` with `B[:, j]` by `trmvTAscProd` otherwise.
-/
@[expose] public def trmmTAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) : Float :=
  if α == 0 then 0 else α * trmvTAscProd uplo d A (colVec B.data B.off B.ld j) i

/-! ### Four columns at a time -/

/--
Element `j = m - 1 - k` of the transposed upper product in increasing order of the column at the
index `o` of `b`, with stride `1`: the value that `trmvTUpperAscStep` writes.
-/
@[expose] public def colUpperTMulVal (d : Diag) (A : Mat m m) (o k : Nat) (b : Float64Array) :
    Float :=
  Nat.fold (m - 1 - k) (fun t _ s => s + A.data[A.off + A.ld * (m - 1 - k) + t]! * b[o + t]!)
    (d.mul b[o + (m - 1 - k)]! A.data[A.off + A.ld * (m - 1 - k) + (m - 1 - k)]!)

/-- The step `k` of the transposed upper product of the column at `o`, with stride `1`. -/
@[expose] public def colUpperTMulStep (d : Diag) (A : Mat m m) (o k : Nat) (b : Float64Array) :
    Float64Array :=
  b.set! (o + (m - 1 - k)) (colUpperTMulVal d A o k b)

/--
Element `j` of the transposed lower product of the column at the index `o` of `b`, with stride
`1`: the value that `trmvTLowerStep` writes.
-/
@[expose] public def colLowerTMulVal (d : Diag) (A : Mat m m) (o j : Nat) (b : Float64Array) :
    Float :=
  Nat.fold (m - 1 - j) (fun t _ s =>
      s + A.data[A.off + A.ld * j + (j + 1 + t)]! * b[o + (j + 1 + t)]!)
    (d.mul b[o + j]! A.data[A.off + A.ld * j + j]!)

/-- The step `j` of the transposed lower product of the column at `o`, with stride `1`. -/
@[expose] public def colLowerTMulStep (d : Diag) (A : Mat m m) (o j : Nat) (b : Float64Array) :
    Float64Array :=
  b.set! (o + j) (colLowerTMulVal d A o j b)

private theorem colUpperTMulVal_congr (d : Diag) (A : Mat m m) {o k : Nat} (hk : k < m)
    {b b' : Float64Array} (h : ∀ p, colIdx o m p → b[p]! = b'[p]!) :
    colUpperTMulVal d A o k b = colUpperTMulVal d A o k b' := by
  unfold colUpperTMulVal
  rw [h (o + (m - 1 - k)) ⟨by lia, by lia⟩]
  congr 1
  funext t ht s
  rw [h (o + t) ⟨by lia, by lia⟩]

private theorem colLowerTMulVal_congr (d : Diag) (A : Mat m m) {o j : Nat} (hj : j < m)
    {b b' : Float64Array} (h : ∀ p, colIdx o m p → b[p]! = b'[p]!) :
    colLowerTMulVal d A o j b = colLowerTMulVal d A o j b' := by
  unfold colLowerTMulVal
  rw [h (o + j) ⟨by lia, by lia⟩]
  congr 1
  funext t ht s
  rw [h (o + (j + 1 + t)) ⟨by lia, by lia⟩]

private theorem local_colUpperTMulStep (d : Diag) (A : Mat m m) (o : Nat) {k : Nat} (hk : k < m) :
    Local (colIdx o m) (colUpperTMulStep d A o k) :=
  local_set! (o + (m - 1 - k)) ⟨by lia, by lia⟩ _ fun _ _ _ h => colUpperTMulVal_congr d A hk h

private theorem local_colLowerTMulStep (d : Diag) (A : Mat m m) (o : Nat) {j : Nat} (hj : j < m) :
    Local (colIdx o m) (colLowerTMulStep d A o j) :=
  local_set! (o + j) ⟨by lia, by lia⟩ _ fun _ _ _ h => colLowerTMulVal_congr d A hj h

private theorem colUpperTMulVal_set! (d : Diag) (A : Mat m m) {o k p : Nat} (hk : k < m)
    (hp : ¬colIdx o m p) (b : Float64Array) (v : Float) :
    colUpperTMulVal d A o k (b.set! p v) = colUpperTMulVal d A o k b :=
  colUpperTMulVal_congr d A hk fun q hq => by
    by_cases hq' : q < b.size
    · rw [getElem!_set!_of_lt _ _ _ hq', ite_eq_right (fun e' => hp (by rw [e']; exact hq))]
    · rw [getElem!_neg _ _ (by simpa using hq'), getElem!_neg b _ hq']

private theorem colLowerTMulVal_set! (d : Diag) (A : Mat m m) {o j p : Nat} (hj : j < m)
    (hp : ¬colIdx o m p) (b : Float64Array) (v : Float) :
    colLowerTMulVal d A o j (b.set! p v) = colLowerTMulVal d A o j b :=
  colLowerTMulVal_congr d A hj fun q hq => by
    by_cases hq' : q < b.size
    · rw [getElem!_set!_of_lt _ _ _ hq', ite_eq_right (fun e' => hp (by rw [e']; exact hq))]
    · rw [getElem!_neg _ _ (by simpa using hq'), getElem!_neg b _ hq']

private theorem trmvTUpperAscStep_eq_col (d : Diag) (A : Mat m m) (x : Vec m) (hx : x.inc = 1) :
    trmvTUpperAscStep d A x = colUpperTMulStep d A x.off := by
  funext k b
  rw [trmvTUpperAscStep, modifyAt_of_lt _ _ (Nat.lt_succ_self _), modifyAt_self]
  simp [colUpperTMulStep, colUpperTMulVal, Vec.stride, Stride.idx, hx]

private theorem trmvTLowerStep_eq_col (d : Diag) (A : Mat m m) (x : Vec m) (hx : x.inc = 1) :
    trmvTLowerStep d A x = colLowerTMulStep d A x.off := by
  funext j b
  rw [trmvTLowerStep, modifyAt_of_lt _ _ (Nat.lt_succ_self _), modifyAt_self]
  simp [colLowerTMulStep, colLowerTMulVal, Vec.stride, Stride.idx, hx]

/--
The transposed upper products of `trmmT` for the four columns at the indices `o₀` to `o₃` of `b`,
with stride `1`, together: at step `k`, it computes the four dot products of element
`j = m - 1 - k`, which share the reads of column `j` of `A`, then writes the four elements. The four
sums are independent, so that their additions overlap. Each element gets the operations of
`trmvTUpperAsc`, in the same order.
-/
public def trmmTUpper4Data (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  let c₀ := o₀.toUSize
  have e₀ : c₀.toNat = o₀ := by grind
  let c₁ := o₁.toUSize
  have e₁ : c₁.toNat = o₁ := by grind
  let c₂ := o₂.toUSize
  have e₂ : c₂.toNat = o₂ := by grind
  let c₃ := o₃.toUSize
  have e₃ : c₃.toNat = o₃ := by grind
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  (inplace b do
    for k in 0...mu do
      have hj : (mu - 1 - k).toNat = m - 1 - k.toNat := by grind
      have hjn : (mu - 1 - k).toNat < m := by lia
      have q₀ : (c₀ + (mu - 1 - k)).toNat < b.size := by grind
      have q₁ : (c₁ + (mu - 1 - k)).toNat < b.size := by grind
      have q₂ : (c₂ + (mu - 1 - k)).toNat < b.size := by grind
      have q₃ : (c₃ + (mu - 1 - k)).toNat < b.size := by grind
      let ajj := A.uget ao al rfl rfl hs.1 (mu - 1 - k) (mu - 1 - k) hjn hjn
      let v₀ := b[c₀ + (mu - 1 - k)]
      let v₁ := b[c₁ + (mu - 1 - k)]
      let v₂ := b[c₂ + (mu - 1 - k)]
      let v₃ := b[c₃ + (mu - 1 - k)]
      for t in 0...(mu - 1 - k) with (s₀ := d.mul v₀ ajj) (s₁ := d.mul v₁ ajj)
          (s₂ := d.mul v₂ ajj) (s₃ := d.mul v₃ ajj) do
        have hi : t.toNat < m := by grind
        have p₀ : (c₀ + t).toNat < b.size := by grind
        have p₁ : (c₁ + t).toNat < b.size := by grind
        have p₂ : (c₂ + t).toNat < b.size := by grind
        have p₃ : (c₃ + t).toNat < b.size := by grind
        let a := A.uget ao al rfl rfl hs.1 t (mu - 1 - k) hi hjn
        s₀ := s₀ + a * b[c₀ + t]
        s₁ := s₁ + a * b[c₁ + t]
        s₂ := s₂ + a * b[c₂ + t]
        s₃ := s₃ + a * b[c₃ + t]
      b[c₀ + (mu - 1 - k)] := s₀
      b[c₁ + (mu - 1 - k)] := s₁
      b[c₂ + (mu - 1 - k)] := s₂
      b[c₃ + (mu - 1 - k)] := s₃).2

public theorem trmmTUpper4Data_eq (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trmmTUpper4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs =
      iterRange (fun k c => colUpperTMulStep d A o₃ k (colUpperTMulStep d A o₂ k
        (colUpperTMulStep d A o₁ k (colUpperTMulStep d A o₀ k c)))) 0 m b := by
  have hmu : m.toUSize.toNat = m := by grind
  have e₀ : o₀.toUSize.toNat = o₀ := by grind
  have e₁ : o₁.toUSize.toNat = o₁ := by grind
  have e₂ : o₂.toUSize.toNat = o₂ := by grind
  have e₃ : o₃.toUSize.toNat = o₃ := by grind
  unfold trmmTUpper4Data
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun k c => colUpperTMulStep d A o₃ k (colUpperTMulStep d A o₂ k
    (colUpperTMulStep d A o₁ k (colUpperTMulStep d A o₀ k c))))
    (hF := fun _ _ => by simp [colUpperTMulStep])]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
  · intro k _ hk next a h
    rw [hmu] at hk
    have hb : b.size < USize.size := hs.2
    have hj : (m.toUSize - 1 - k).toNat = m - 1 - k.toNat := by grind
    have t₀ : (o₀.toUSize + (m.toUSize - 1 - k)).toNat = o₀ + (m - 1 - k.toNat) := by grind
    have t₁ : (o₁.toUSize + (m.toUSize - 1 - k)).toNat = o₁ + (m - 1 - k.toNat) := by grind
    have t₂ : (o₂.toUSize + (m.toUSize - 1 - k)).toNat = o₂ + (m - 1 - k.toNat) := by grind
    have t₃ : (o₃.toUSize + (m.toUSize - 1 - k)).toNat = o₃ + (m - 1 - k.toNat) := by grind
    simp only [Tail.run_readThen, Tail.forIn4_eq]
    rw [run_forIn4From_read
      (f₀ := fun t s => s + A.data[A.off + A.ld * (m - 1 - k.toNat) + t]! * a[o₀ + t]!)
      (f₁ := fun t s => s + A.data[A.off + A.ld * (m - 1 - k.toNat) + t]! * a[o₁ + t]!)
      (f₂ := fun t s => s + A.data[A.off + A.ld * (m - 1 - k.toNat) + t]! * a[o₂ + t]!)
      (f₃ := fun t s => s + A.data[A.off + A.ld * (m - 1 - k.toNat) + t]! * a[o₃ + t]!)]
    · simp only [Tail.run_writeThen, USize.toNat_zero, hj]
      simp only [iterRange_eq_fold]
      apply run_congr
      have n₁₀ : ¬colIdx o₁ m (o₀ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₂₀ : ¬colIdx o₂ m (o₀ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₃₀ : ¬colIdx o₃ m (o₀ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₂₁ : ¬colIdx o₂ m (o₁ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₃₁ : ¬colIdx o₃ m (o₁ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₃₂ : ¬colIdx o₃ m (o₂ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      simp only [colUpperTMulStep, colUpperTMulVal_set! d A hk n₁₀,
        colUpperTMulVal_set! d A hk n₂₀, colUpperTMulVal_set! d A hk n₃₀,
        colUpperTMulVal_set! d A hk n₂₁, colUpperTMulVal_set! d A hk n₃₁,
        colUpperTMulVal_set! d A hk n₃₂]
      simp only [colUpperTMulVal, t₀, t₁, t₂, t₃, hj, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]
    · intro t _ ht next' s₀ s₁ s₂ s₃
      rw [hj] at ht
      have u₀ : (o₀.toUSize + t).toNat = o₀ + t.toNat := by grind
      have u₁ : (o₁.toUSize + t).toNat = o₁ + t.toNat := by grind
      have u₂ : (o₂.toUSize + t).toNat = o₂ + t.toNat := by grind
      have u₃ : (o₃.toUSize + t).toNat = o₃ + t.toNat := by grind
      simp only [Tail.run_readThen, u₀, u₁, u₂, u₃, hj, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]

/--
The transposed lower products of `trmmT` for the four columns at the indices `o₀` to `o₃` of `b`,
with stride `1`, together, as `trmmTUpper4Data` does: at step `j`, it computes the four dot
products of element `j`, then writes the four elements. Each element gets the operations of
`trmvTLower`, in the same order.
-/
public def trmmTLower4Data (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  let c₀ := o₀.toUSize
  have e₀ : c₀.toNat = o₀ := by grind
  let c₁ := o₁.toUSize
  have e₁ : c₁.toNat = o₁ := by grind
  let c₂ := o₂.toUSize
  have e₂ : c₂.toNat = o₂ := by grind
  let c₃ := o₃.toUSize
  have e₃ : c₃.toNat = o₃ := by grind
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  (inplace b do
    for j in 0...mu do
      have q₀ : (c₀ + j).toNat < b.size := by grind
      have q₁ : (c₁ + j).toNat < b.size := by grind
      have q₂ : (c₂ + j).toNat < b.size := by grind
      have q₃ : (c₃ + j).toNat < b.size := by grind
      let ajj := A.uget ao al rfl rfl hs.1 j j (by lia) (by lia)
      let v₀ := b[c₀ + j]
      let v₁ := b[c₁ + j]
      let v₂ := b[c₂ + j]
      let v₃ := b[c₃ + j]
      for t in 0...(mu - 1 - j) with (s₀ := d.mul v₀ ajj) (s₁ := d.mul v₁ ajj)
          (s₂ := d.mul v₂ ajj) (s₃ := d.mul v₃ ajj) do
        have hi : (j + 1 + t).toNat < m := by grind
        have p₀ : (c₀ + (j + 1 + t)).toNat < b.size := by grind
        have p₁ : (c₁ + (j + 1 + t)).toNat < b.size := by grind
        have p₂ : (c₂ + (j + 1 + t)).toNat < b.size := by grind
        have p₃ : (c₃ + (j + 1 + t)).toNat < b.size := by grind
        let a := A.uget ao al rfl rfl hs.1 (j + 1 + t) j hi (by lia)
        s₀ := s₀ + a * b[c₀ + (j + 1 + t)]
        s₁ := s₁ + a * b[c₁ + (j + 1 + t)]
        s₂ := s₂ + a * b[c₂ + (j + 1 + t)]
        s₃ := s₃ + a * b[c₃ + (j + 1 + t)]
      b[c₀ + j] := s₀
      b[c₁ + j] := s₁
      b[c₂ + j] := s₂
      b[c₃ + j] := s₃).2

public theorem trmmTLower4Data_eq (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trmmTLower4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs =
      iterRange (fun j c => colLowerTMulStep d A o₃ j (colLowerTMulStep d A o₂ j
        (colLowerTMulStep d A o₁ j (colLowerTMulStep d A o₀ j c)))) 0 m b := by
  have hmu : m.toUSize.toNat = m := by grind
  have e₀ : o₀.toUSize.toNat = o₀ := by grind
  have e₁ : o₁.toUSize.toNat = o₁ := by grind
  have e₂ : o₂.toUSize.toNat = o₂ := by grind
  have e₃ : o₃.toUSize.toNat = o₃ := by grind
  unfold trmmTLower4Data
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun j c => colLowerTMulStep d A o₃ j (colLowerTMulStep d A o₂ j
    (colLowerTMulStep d A o₁ j (colLowerTMulStep d A o₀ j c))))
    (hF := fun _ _ => by simp [colLowerTMulStep])]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
  · intro j _ hj next a h
    rw [hmu] at hj
    have hb : b.size < USize.size := hs.2
    have hr : (m.toUSize - 1 - j).toNat = m - 1 - j.toNat := by grind
    have t₀ : (o₀.toUSize + j).toNat = o₀ + j.toNat := by grind
    have t₁ : (o₁.toUSize + j).toNat = o₁ + j.toNat := by grind
    have t₂ : (o₂.toUSize + j).toNat = o₂ + j.toNat := by grind
    have t₃ : (o₃.toUSize + j).toNat = o₃ + j.toNat := by grind
    simp only [Tail.run_readThen, Tail.forIn4_eq]
    rw [run_forIn4From_read
      (f₀ := fun t s => s + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + t)]! *
        a[o₀ + (j.toNat + 1 + t)]!)
      (f₁ := fun t s => s + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + t)]! *
        a[o₁ + (j.toNat + 1 + t)]!)
      (f₂ := fun t s => s + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + t)]! *
        a[o₂ + (j.toNat + 1 + t)]!)
      (f₃ := fun t s => s + A.data[A.off + A.ld * j.toNat + (j.toNat + 1 + t)]! *
        a[o₃ + (j.toNat + 1 + t)]!)]
    · simp only [Tail.run_writeThen, USize.toNat_zero, hr]
      simp only [iterRange_eq_fold]
      apply run_congr
      have n₁₀ : ¬colIdx o₁ m (o₀ + j.toNat) := by simp only [colIdx]; lia
      have n₂₀ : ¬colIdx o₂ m (o₀ + j.toNat) := by simp only [colIdx]; lia
      have n₃₀ : ¬colIdx o₃ m (o₀ + j.toNat) := by simp only [colIdx]; lia
      have n₂₁ : ¬colIdx o₂ m (o₁ + j.toNat) := by simp only [colIdx]; lia
      have n₃₁ : ¬colIdx o₃ m (o₁ + j.toNat) := by simp only [colIdx]; lia
      have n₃₂ : ¬colIdx o₃ m (o₂ + j.toNat) := by simp only [colIdx]; lia
      simp only [colLowerTMulStep, colLowerTMulVal_set! d A hj n₁₀,
        colLowerTMulVal_set! d A hj n₂₀, colLowerTMulVal_set! d A hj n₃₀,
        colLowerTMulVal_set! d A hj n₂₁, colLowerTMulVal_set! d A hj n₃₁,
        colLowerTMulVal_set! d A hj n₃₂]
      simp only [colLowerTMulVal, t₀, t₁, t₂, t₃, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]
    · intro t _ ht next' s₀ s₁ s₂ s₃
      rw [hr] at ht
      have hjt : (j + 1 + t).toNat = j.toNat + 1 + t.toNat := by grind
      have u₀ : (o₀.toUSize + (j + 1 + t)).toNat = o₀ + (j.toNat + 1 + t.toNat) := by grind
      have u₁ : (o₁.toUSize + (j + 1 + t)).toNat = o₁ + (j.toNat + 1 + t.toNat) := by grind
      have u₂ : (o₂.toUSize + (j + 1 + t)).toNat = o₂ + (j.toNat + 1 + t.toNat) := by grind
      have u₃ : (o₃.toUSize + (j + 1 + t)).toNat = o₃ + (j.toNat + 1 + t.toNat) := by grind
      simp only [Tail.run_readThen, u₀, u₁, u₂, u₃, hjt, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]

/-- The step of the column product of `trmmT` for the triangle `uplo`, on the column at `o`. -/
@[expose] public def colTMulStep (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat) :
    Nat → Float64Array → Float64Array :=
  match uplo with
  | .upper => colUpperTMulStep d A o
  | .lower => colLowerTMulStep d A o

/-- The column product of `trmmT` on the column at `o`, with stride `1`. -/
@[expose] public def colTMul (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat)
    (c : Float64Array) : Float64Array :=
  iterRange (colTMulStep uplo d A o) 0 m c

private theorem local_colTMulStep (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat) {k : Nat}
    (hk : k < m) : Local (colIdx o m) (colTMulStep uplo d A o k) := by
  cases uplo
  · exact local_colUpperTMulStep d A o hk
  · exact local_colLowerTMulStep d A o hk

private theorem local_colTMul (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat) :
    Local (colIdx o m) (colTMul uplo d A o) :=
  Local.iterRange fun _ _ hk => local_colTMulStep uplo d A o hk

/-- The four column products of `trmmT` for the triangle `uplo`, together. -/
public def trmmT4Data (uplo : Uplo) (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat)
    (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  match uplo with
  | .upper => trmmTUpper4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs
  | .lower => trmmTLower4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs

/-- The four column products together are the four products, one column after the other. -/
public theorem trmmT4Data_eq (uplo : Uplo) (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat)
    (b : Float64Array) (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃)
    (h₄ : o₃ + m ≤ b.size) (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trmmT4Data uplo d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs =
      colTMul uplo d A o₃ (colTMul uplo d A o₂ (colTMul uplo d A o₁ (colTMul uplo d A o₀ b))) := by
  cases uplo
  · rw [trmmT4Data, trmmTUpper4Data_eq]
    exact iterRange_four_cols h₁ h₂ h₃ (fun _ hk => local_colUpperTMulStep d A o₀ hk)
      (fun _ hk => local_colUpperTMulStep d A o₁ hk) (fun _ hk => local_colUpperTMulStep d A o₂ hk)
      (fun _ hk => local_colUpperTMulStep d A o₃ hk) b
  · rw [trmmT4Data, trmmTLower4Data_eq]
    exact iterRange_four_cols h₁ h₂ h₃ (fun _ hk => local_colLowerTMulStep d A o₀ hk)
      (fun _ hk => local_colLowerTMulStep d A o₁ hk) (fun _ hk => local_colLowerTMulStep d A o₂ hk)
      (fun _ hk => local_colLowerTMulStep d A o₃ hk) b

/-- The column map of `trmmT` on a column of an array: the product, then the scaling. -/
private theorem trmmTCol_colOf (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array)
    (hb : b.size = sz) (j : Nat) (hj : j < n) :
    trmmTCol uplo d α A (colOf off ld sz hsz b hb j hj) =
      colScale α (off + ld * j) m (colTMul uplo d A (off + ld * j) b) := by
  rw [trmmTCol, Vec.scalData_eq]
  cases uplo
  · show (trmvTUpperAscData d A _).modifyAt _ _ _ _ = _
    rw [trmvTUpperAscData_eq_iterRange, trmvTUpperAscStep_eq_col d A _ rfl]; rfl
  · show (trmvTLowerData d A _).modifyAt _ _ _ _ = _
    rw [trmvTLowerData_eq_iterRange, trmvTLowerStep_eq_col d A _ rfl]; rfl

private theorem colLoop_congr (F : Vec m → Float64Array) (hF : ∀ x, (F x).size = x.data.size)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) {j j' : Nat}
    (hj : j = j') {b b' : Float64Array} (e : b = b') (hb : b.size = sz) (hb' : b'.size = sz) :
    colLoop F hF off ld sz hsz j b hb = colLoop F hF off ld sz hsz j' b' hb' := by
  subst hj e; rfl

private theorem size_trmmTCol (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (x : Vec m) :
    (trmmTCol uplo d α A x).size = x.data.size := by
  rw [trmmTCol, Vec.scalData_eq, size_modifyAt]
  show (trmvTAscData uplo d A x).size = _
  rw [trmvTAscData_eq, size_modifyAt]

/-- A step of the column loop of `trmmT` multiplies column `j`, then scales it. -/
private theorem colLoop_trmmT_succ (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) {j : Nat} (hj : j < n)
    (b : Float64Array) (hb : b.size = sz) :
    colLoop (trmmTCol uplo d α A) (size_trmmTCol uplo d α A) off ld sz hsz j b hb =
      colLoop (trmmTCol uplo d α A) (size_trmmTCol uplo d α A) off ld sz hsz (j + 1)
        (colScale α (off + ld * j) m (colTMul uplo d A (off + ld * j) b))
        (by simpa [(local_colTMul uplo d A _).1] using hb) := by
  rw [colLoop, dite_eq_left hj]
  apply colLoop_congr _ _ _ _ _ _ rfl
  rw [trmmTCol_colOf]

private theorem col_add_le' {off ld j : Nat} (hml : m ≤ ld) :
    off + ld * j + m ≤ off + ld * (j + 1) := by
  rw [Nat.mul_succ]; lia

/--
The column loop of `trmmT` from column `j`, as `colLoop` of `trmmTCol`, but four columns at a time
by `trmmT4Data`, then one at a time. It needs sizes that fit a `USize`.
-/
public def trmmTLoop4 (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (hml : m ≤ ld)
    (hs : A.data.size < USize.size ∧ sz < USize.size) (j : Nat) (b : Float64Array)
    (hb : b.size = sz) : Float64Array :=
  if h4 : j + 4 ≤ n ∧ off + ld * (j + 3) + m ≤ sz then
    let c := trmmT4Data uplo d A (off + ld * j) (off + ld * (j + 1)) (off + ld * (j + 2))
      (off + ld * (j + 3)) b (col_add_le' hml) (col_add_le' hml) (col_add_le' hml)
      (by rw [hb]; exact h4.2) ⟨hs.1, by rw [hb]; exact hs.2⟩
    have hc : c.size = sz := by
      simp only [c]; rw [trmmT4Data_eq]; simpa [(local_colTMul uplo d A _).1] using hb
    let c₀ := Vec.scalData α (colOf off ld sz hsz c hc j (by lia))
    have hc₀ : c₀.size = sz := by
      simp only [c₀]; rw [Vec.scalData_eq, size_modifyAt]; exact hc
    let c₁ := Vec.scalData α (colOf off ld sz hsz c₀ hc₀ (j + 1) (by lia))
    have hc₁ : c₁.size = sz := by
      simp only [c₁]; rw [Vec.scalData_eq, size_modifyAt]; exact hc₀
    let c₂ := Vec.scalData α (colOf off ld sz hsz c₁ hc₁ (j + 2) (by lia))
    have hc₂ : c₂.size = sz := by
      simp only [c₂]; rw [Vec.scalData_eq, size_modifyAt]; exact hc₁
    let c₃ := Vec.scalData α (colOf off ld sz hsz c₂ hc₂ (j + 3) (by lia))
    have hc₃ : c₃.size = sz := by
      simp only [c₃]; rw [Vec.scalData_eq, size_modifyAt]; exact hc₂
    trmmTLoop4 uplo d α A off ld sz hsz hml hs (j + 4) c₃ hc₃
  else if hj : j < n then
    trmmTLoop4 uplo d α A off ld sz hsz hml hs (j + 1)
      (trmmTCol uplo d α A (colOf off ld sz hsz b hb j hj))
      (by rw [size_trmmTCol]; exact hb)
  else b
termination_by n - j

private theorem scalData_colOf' (α : Float) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) :
    Vec.scalData α (colOf off ld sz hsz b hb j hj) = colScale α (off + ld * j) m b := by
  rw [Vec.scalData_eq]; rfl

/-- `trmmTLoop4` is the column loop of `trmmT`. -/
private theorem trmmTLoop4_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (hml : m ≤ ld)
    (hs : A.data.size < USize.size ∧ sz < USize.size) (j : Nat) (b : Float64Array)
    (hb : b.size = sz) :
    trmmTLoop4 uplo d α A off ld sz hsz hml hs j b hb =
      colLoop (trmmTCol uplo d α A) (size_trmmTCol uplo d α A) off ld sz hsz j b hb := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j b with
  | ind e ih =>
    rw [trmmTLoop4]
    split
    · rename_i h4
      rw [ih (n - (j + 4)) (by lia) _ _ _ rfl]
      symm
      rw [colLoop_trmmT_succ (j := j) uplo d α A off ld sz hsz (by lia),
        colLoop_trmmT_succ (j := j + 1) uplo d α A off ld sz hsz (by lia),
        colLoop_trmmT_succ (j := j + 1 + 1) uplo d α A off ld sz hsz (by lia),
        colLoop_trmmT_succ (j := j + 1 + 1 + 1) uplo d α A off ld sz hsz (by lia)]
      apply colLoop_congr _ _ _ _ _ _ (by lia)
      symm
      simp only [trmmT4Data_eq, scalData_colOf']
      exact four_cols_reorder (col_add_le' hml) (col_add_le' hml) (col_add_le' hml)
        (local_colTMul _ _ _ _) (local_colTMul _ _ _ _) (local_colTMul _ _ _ _)
        (local_colScale _ _ _) (local_colScale _ _ _) (local_colScale _ _ _) b
    · split
      · rename_i h4 hj
        rw [ih (n - (j + 1)) (by lia) _ _ _ rfl]
        conv => rhs; rw [colLoop, dite_eq_left hj]
      · rename_i h4 hj
        rw [colLoop, dite_eq_right hj]

/-- The array of `trmmT`. -/
public def trmmTData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0
  else if hs : A.data.size < USize.size ∧ B.data.size < USize.size then
    trmmTLoop4 uplo d α A B.off B.ld B.data.size B.bound B.le_ld hs 0 B.data rfl
  else colLoop (trmmTCol uplo d α A) (size_trmmTCol uplo d α A) B.off B.ld B.data.size B.bound 0
    B.data rfl

public theorem trmmTData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    trmmTData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trmmTAt uplo d α A B i j := by
  unfold trmmTData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have e : (if hs : A.data.size < USize.size ∧ B.data.size < USize.size then
        trmmTLoop4 uplo d α A B.off B.ld B.data.size B.bound B.le_ld hs 0 B.data rfl
      else colLoop (trmmTCol uplo d α A) (size_trmmTCol uplo d α A) B.off B.ld B.data.size
        B.bound 0 B.data rfl) =
        colLoop (trmmTCol uplo d α A) (size_trmmTCol uplo d α A) B.off B.ld B.data.size B.bound 0
          B.data rfl := by
      split
      · exact trmmTLoop4_eq ..
      · rfl
    rw [e, colLoop_eq _ _ (fun x i => α * trmvTAscProd uplo d A x i)]
    · apply mapMat_congr
      intro i j v hi _ _
      simp only [trmmTAt, hα, Bool.false_eq_true, ↓reduceIte]
    · intro x
      rw [trmmTCol, Vec.scalData_eq]
      show (trmvTAscData uplo d A x).modifyAt x.stride.idx 0 m _ = _
      rw [trmvTAscData_eq, modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    · intro x y h i hi
      rw [trmvTAscProd_congr _ _ _ h i hi]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trmmTAt, betaMul, hα, show ((0 : Float) == 0) = true from rfl]

/--
`trmmT uplo d α A B` is `α * Aᵀ * B` for the triangle `uplo` of `A`, with a unit diagonal if `d`
is `.unit`, over `B`, by the loops of the reference BLAS for `SIDE = 'L'` and `TRANSA = 'T'`: for
each column `j` of `B`, it sets element `i` to `α` times `B[i, j] * A[i, i]` plus the dot product of
the other elements of column `i` of the triangle with those of `B[:, j]`, in increasing order of
the rows, from `i = m - 1` down to `0` for the upper triangle and from `i = 0` up for the lower one.
It updates `B` in place when its array is not shared, and leaves the elements of the array outside
`B` unchanged. As in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when
`α = 0`, and reads only the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`.
-/
@[expose] public def trmmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Mat m n where
  data := trmmTData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trmmTData_eq, size_mapMat]; exact B.bound

/-- The array of `trmmT uplo d α A B` is the array of `B` with its elements multiplied. -/
public theorem data_trmmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    (trmmT uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trmmTAt uplo d α A B i j :=
  trmmTData_eq uplo d α A B

@[simp] public theorem off_trmmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trmmT uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trmmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trmmT uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trmmT uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trmmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) : (trmmT uplo d α A B)[(i, j)] = trmmTAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trmmT uplo d α A B) rfl rfl i j h

/-- An element of `colVec`, by `getElem!`, is the element of the matrix. -/
private theorem getElem!_colVec (B : Mat m n) {l j : Nat} (hl : l < m) (hj : j < n) :
    (colVec (m := m) B.data B.off B.ld j).data[(colVec (m := m) B.data B.off B.ld j).off +
      (colVec (m := m) B.data B.off B.ld j).inc * l]! = B[(l, j)] := by
  rw [getElem!_index _ hl, colVec, Vec.getElem_ofFn]
  dsimp only
  rw [getElem!_pos B.data _ (B.index_lt hl hj)]
  rfl

/--
Element `(i, j)` of `trmmT .upper d α A B` is `0` when `α = 0`, and otherwise `α` times
`B[i, j] * A[i, i]`, or `B[i, j]` for a unit diagonal, plus the terms `A[k, i] * B[k, j]` for
`k = 0, …, i - 1`.
-/
public theorem getElem_trmmT_upper (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trmmT .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else α * Nat.fold i (fun k _ s =>
          s + A[(k, i)]'⟨by lia, h.1⟩ * B[(k, j)]'⟨by lia, h.2⟩)
        (d.mul B[(i, j)] A[(i, i)]) := by
  rw [getElem_trmmT _ _ _ _ _ _ _ h, trmmTAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmvTAscProd, trmvTUpperAsc]
    rw [getElem!_colVec B h.1 h.2, getElem!_pos A.data (A.off + A.ld * i + i) (A.index_lt h.1 h.1)]
    congr 1
    congr 1
    funext k hk s
    rw [getElem!_colVec B (by lia) h.2,
      getElem!_pos A.data (A.off + A.ld * i + k) (A.index_lt (by lia) h.1)]
    rfl
  · simp only [↓reduceIte]

/--
Element `(i, j)` of `trmmT .lower d α A B` is `0` when `α = 0`, and otherwise `α` times
`B[i, j] * A[i, i]`, or `B[i, j]` for a unit diagonal, plus the terms `A[k, i] * B[k, j]` for
`k = i + 1, …, m - 1`.
-/
public theorem getElem_trmmT_lower (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trmmT .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else α * Nat.fold (m - 1 - i) (fun t _ s =>
          s + A[(i + 1 + t, i)]'⟨by lia, h.1⟩ * B[(i + 1 + t, j)]'⟨by lia, h.2⟩)
        (d.mul B[(i, j)] A[(i, i)]) := by
  rw [getElem_trmmT _ _ _ _ _ _ _ h, trmmTAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trmvTAscProd, trmvTLower]
    rw [getElem!_colVec B h.1 h.2, getElem!_pos A.data (A.off + A.ld * i + i) (A.index_lt h.1 h.1)]
    congr 1
    congr 1
    funext t ht s
    rw [getElem!_colVec B (by lia) h.2,
      getElem!_pos A.data (A.off + A.ld * i + (i + 1 + t)) (A.index_lt (by lia) h.1)]
    rfl
  · simp only [↓reduceIte]

end Mat

end BLAS.Float64
