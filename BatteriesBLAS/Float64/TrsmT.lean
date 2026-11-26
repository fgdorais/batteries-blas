/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float64.Trsm
public import BatteriesBLAS.Float64.TrsvT
import all BatteriesBLAS.Internal

/-!
# Transposed triangular solve with several right-hand sides

`Mat.trsmT uplo d α A B` solves `Aᵀ * X = α * B` and `Mat.trsmRightT uplo d α A B` solves
`X * Aᵀ = α * B`, for a triangular matrix `A`, over `B`, by the loops of the reference BLAS for
`TRANSA = 'T'`. Each element gets the operations of those loops, in the same order. As in the
reference BLAS, both set `B` to `0` without reading `A` or `B` when `α = 0`, and neither checks for
a zero on the diagonal.

`trsmT` solves each column of `B` by the loops of `trsvT`, after scaling it by `α`: the reference
loops compute `α * B[i, j]` as they reach element `i`, before they write it, which is the same
value. For the lower triangle, the reference `trsm` subtracts the terms of each element in
increasing order, unlike `trsv`, so `trsmT` solves its columns by `trsvTLowerAsc`. Its
specification is that of `trsvTUpper` or `trsvTLowerAsc` on the scaled column.

`trsmRightT` updates each column of `B` with the columns already solved, and scales `B` by `α`
last, as the reference loops do: they scale a column once they have subtracted it from the others.
Its specification is `α` times the recursive model `trsmRightTUpper` or `trsmRightTLower`.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {m n : Nat}

/-- Element `l` of a vector, by `getElem!` on its array. -/
private theorem getElem!_index (x : Vec n) {l : Nat} (hl : l < n) :
    x.data[x.off + x.inc * l]! = x[l] := by
  rw [getElem!_pos x.data _ (x.index_lt hl)]; rfl

/-! ## The column solves of `trsmT` depend only on the elements of the vector -/

theorem trsvTUpper_congr (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) :
    ∀ i, i < n → trsvTUpper d A x i = trsvTUpper d A y i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [trsvTUpper_eq d A x hi, trsvTUpper_eq d A y hi, Vec.getElem_def, Vec.getElem_def,
      ← getElem!_pos x.data _ (x.index_lt hi), ← getElem!_pos y.data _ (y.index_lt hi), h i hi]
    congr 2
    funext l hl s
    rw [ih l hl (by lia)]

theorem trsvTLowerAsc_congr (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) :
    ∀ i, i < n → trsvTLowerAsc d A x i = trsvTLowerAsc d A y i := by
  intro i hi
  obtain ⟨e, he⟩ : ∃ e, n - i = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing i with
  | ind e ih =>
    rw [trsvTLowerAsc_eq d A x hi, trsvTLowerAsc_eq d A y hi, Vec.getElem_def, Vec.getElem_def,
      ← getElem!_pos x.data _ (x.index_lt hi), ← getElem!_pos y.data _ (y.index_lt hi), h i hi]
    congr 2
    funext t ht s
    rw [ih (n - (i + 1 + t)) (by lia) (i + 1 + t) (by lia) rfl]

theorem trsvTAscSol_congr (uplo : Uplo) (d : Diag) (A : Mat n n) {x y : Vec n}
    (h : ∀ l, l < n → x.data[x.off + x.inc * l]! = y.data[y.off + y.inc * l]!) (i : Nat)
    (hi : i < n) : trsvTAscSol uplo d A x i = trsvTAscSol uplo d A y i := by
  cases uplo
  · exact trsvTUpper_congr d A h i hi
  · exact trsvTLowerAsc_congr d A h i hi

/-! ## `trsmT` -/

/--
The value of `trsmT` at `(i, j)`: `0` when `α = 0`, and element `i` of the solution of
`Aᵀ * y = α * B[:, j]` by `trsvTAscSol` otherwise.
-/
@[expose] public def trsmTAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) : Float :=
  if α == 0 then 0 else trsvTAscSol uplo d A (scaledCol α B j) i

private theorem size_scalData_colOf (α : Float) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) : (Vec.scalData α (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [Vec.scalData_eq, size_modifyAt]; exact hb

private theorem size_trsvTAscData_colOf (uplo : Uplo) (d : Diag) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) : (trsvTAscData uplo d A (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [trsvTAscData_eq, size_modifyAt]; exact hb

/--
The loop of `trsmT` over the columns from `j`, on the array `b` of an `m × n` matrix: it scales
column `j` by `α`, then solves it by `trsvTAscData`. It takes the offset and the leading dimension
of the matrix rather than the matrix, which would keep a second reference to its array.
-/
public def trsmTLoop (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (j : Nat) (b : Float64Array)
    (hb : b.size = sz) : Float64Array :=
  if hj : j < n then
    trsmTLoop uplo d α A off ld sz hsz (j + 1)
      (trsvTAscData uplo d A (colOf off ld sz hsz (Vec.scalData α (colOf off ld sz hsz b hb j hj))
        (size_scalData_colOf ..) j hj))
      (size_trsvTAscData_colOf ..)
  else b
termination_by n - j

/-- The value at `(i, j)` of `trsmT` for `α ≠ 0`, from the column `j` of the array `a`. -/
private def trsmTColAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (a : Float64Array) (i j : Nat) (_ : Float) : Float :=
  trsvTAscSol uplo d A (Vec.ofFn fun l : Fin m => α * a[B.off + B.ld * j + l.val]!) i

/-- A step of `trsmTLoop` maps column `j` to its solution. -/
private theorem trsmTLoop_step (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j < n) (b : Float64Array) (hb : b.size = B.data.size)
    (a : Float64Array) (hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = a[B.off + B.ld * j + l]!) :
    trsvTAscData uplo d A (colOf B.off B.ld B.data.size B.bound
        (Vec.scalData α (colOf B.off B.ld B.data.size B.bound b hb j hj))
        (size_scalData_colOf α B.off B.ld B.data.size B.bound b hb j hj) j hj) =
      b.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m
        (fun i v => trsmTColAt uplo d α A B a i j v) := by
  rw [trsvTAscData_eq]
  simp only [colOf, Vec.stride, Vec.scalData_eq]
  rw [modifyAt_modifyAt _ _ (col_injOn _ _ _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  unfold trsmTColAt
  apply trsvTAscSol_congr _ _ _ _ i hi
  intro l hl
  have hq : B.off + B.ld * j + l < b.size := by rw [hb]; exact B.index_lt hl hj
  rw [getElem!_index (Vec.ofFn fun l : Fin m => α * a[B.off + B.ld * j + l.val]!) hl,
    Vec.getElem_ofFn]
  dsimp only
  rw [Nat.one_mul, getElem!_modifyAt_col _ _ _ _ hl, ite_eq_left hq, hcol l hl]

/-- An element of a column `j` outside the columns of a `mapMat` is unchanged. -/
private theorem getElem!_mapMat_col_of_not (a : Float64Array) (off ld lo hi : Nat)
    (g : Nat → Nat → Float → Float) (hml : m ≤ ld) {j : Nat} (hj : ¬(lo ≤ j ∧ j < hi)) {l : Nat}
    (hl : l < m) : (mapMat a off ld m lo hi g)[off + ld * j + l]! = a[off + ld * j + l]! := by
  by_cases hq : off + ld * j + l < a.size
  · rw [getElem!_pos _ _ (by rw [size_mapMat]; exact hq), getElem!_pos a _ hq,
      getElem_mapMat_of_ne _ _ _ _ _ _ _ (fun i' j' hi' h₁ h₂ e' => by
        by_cases hjj : j = j'
        · subst hjj; exact hj ⟨h₁, h₂⟩
        · exact col_index_ne hl hi' hml hjj e') hq]
  · rw [getElem!_neg _ _ (by rw [size_mapMat]; exact hq), getElem!_neg a _ hq]

/-- `trsmTLoop` from column `j`, after the columns before `j` are solved, solves all of them. -/
private theorem trsmTLoop_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j ≤ n) (b : Float64Array) (hb : b.size = B.data.size)
    (hinv : b = mapMat B.data B.off B.ld m 0 j (trsmTColAt uplo d α A B B.data)) :
    trsmTLoop uplo d α A B.off B.ld B.data.size B.bound j b hb =
      mapMat B.data B.off B.ld m 0 n (trsmTColAt uplo d α A B B.data) := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j b with
  | ind e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he0
    · obtain rfl : j = n := by lia
      rw [trsmTLoop, dite_eq_right (Nat.lt_irrefl _), hinv]
    have hjn : j < n := by lia
    rw [trsmTLoop, dite_eq_left hjn]
    refine ih (n - (j + 1)) (by lia) (j + 1) hjn _ _ ?_ rfl
    have hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = B.data[B.off + B.ld * j + l]! := by
      intro l hl
      rw [hinv, getElem!_mapMat_col_of_not _ _ _ _ _ _ B.le_ld (by lia) hl]
    rw [trsmTLoop_step uplo d α A B j hjn b hb B.data hcol, hinv]
    exact modifyAt_col_mapMat _ _ _ B.le_ld j _

/-! ## Four columns at a time -/

/--
Element `j` of the upper solve of the column at the index `o` of `b`, with stride `1`, from the
elements above it: the value that `trsvTUpperStep` writes.
-/
@[expose] public def colUpperVal (d : Diag) (A : Mat m m) (o j : Nat) (b : Float64Array) :
    Float :=
  d.apply (Nat.fold j (fun i _ s => s - A.data[A.off + A.ld * j + i]! * b[o + i]!) b[o + j]!)
    A.data[A.off + A.ld * j + j]!

/-- The step `j` of the upper solve of the column at `o`: `trsvTUpperStep` with stride `1`. -/
@[expose] public def colUpperStep (d : Diag) (A : Mat m m) (o j : Nat) (b : Float64Array) :
    Float64Array :=
  b.set! (o + j) (colUpperVal d A o j b)

/--
Element `j = m - 1 - k` of the lower solve in increasing order of the column at the index `o` of
`b`, with stride `1`, from the elements below it: the value that `trsvTLowerAscStep` writes.
-/
@[expose] public def colLowerVal (d : Diag) (A : Mat m m) (o k : Nat) (b : Float64Array) :
    Float :=
  d.apply (Nat.fold k (fun t _ s =>
      s - A.data[A.off + A.ld * (m - 1 - k) + (m - 1 - k + 1 + t)]! * b[o + (m - 1 - k + 1 + t)]!)
      b[o + (m - 1 - k)]!) A.data[A.off + A.ld * (m - 1 - k) + (m - 1 - k)]!

/-- The step `k` of the lower solve of the column at `o`: `trsvTLowerAscStep` with stride `1`. -/
@[expose] public def colLowerStep (d : Diag) (A : Mat m m) (o k : Nat) (b : Float64Array) :
    Float64Array :=
  b.set! (o + (m - 1 - k)) (colLowerVal d A o k b)

private theorem colUpperVal_congr (d : Diag) (A : Mat m m) {o j : Nat} (hj : j < m)
    {b b' : Float64Array} (h : ∀ p, colIdx o m p → b[p]! = b'[p]!) :
    colUpperVal d A o j b = colUpperVal d A o j b' := by
  unfold colUpperVal
  rw [h (o + j) ⟨by lia, by lia⟩]
  congr 2
  funext i hi s
  rw [h (o + i) ⟨by lia, by lia⟩]

private theorem colLowerVal_congr (d : Diag) (A : Mat m m) {o k : Nat} (hk : k < m)
    {b b' : Float64Array} (h : ∀ p, colIdx o m p → b[p]! = b'[p]!) :
    colLowerVal d A o k b = colLowerVal d A o k b' := by
  unfold colLowerVal
  rw [h (o + (m - 1 - k)) ⟨by lia, by lia⟩]
  congr 2
  funext t ht s
  rw [h (o + (m - 1 - k + 1 + t)) ⟨by lia, by lia⟩]

private theorem local_colUpperStep (d : Diag) (A : Mat m m) (o : Nat) {j : Nat} (hj : j < m) :
    Local (colIdx o m) (colUpperStep d A o j) :=
  local_set! (o + j) ⟨by lia, by lia⟩ _ fun _ _ _ h => colUpperVal_congr d A hj h

private theorem local_colLowerStep (d : Diag) (A : Mat m m) (o : Nat) {k : Nat} (hk : k < m) :
    Local (colIdx o m) (colLowerStep d A o k) :=
  local_set! (o + (m - 1 - k)) ⟨by lia, by lia⟩ _ fun _ _ _ h => colLowerVal_congr d A hk h

private theorem colUpperVal_set! (d : Diag) (A : Mat m m) {o j p : Nat} (hj : j < m)
    (hp : ¬colIdx o m p) (b : Float64Array) (v : Float) :
    colUpperVal d A o j (b.set! p v) = colUpperVal d A o j b :=
  colUpperVal_congr d A hj fun q hq => by
    by_cases hq' : q < b.size
    · rw [getElem!_set!_of_lt _ _ _ hq', ite_eq_right (fun e' => hp (by rw [e']; exact hq))]
    · rw [getElem!_neg _ _ (by simpa using hq'), getElem!_neg b _ hq']

private theorem colLowerVal_set! (d : Diag) (A : Mat m m) {o k p : Nat} (hk : k < m)
    (hp : ¬colIdx o m p) (b : Float64Array) (v : Float) :
    colLowerVal d A o k (b.set! p v) = colLowerVal d A o k b :=
  colLowerVal_congr d A hk fun q hq => by
    by_cases hq' : q < b.size
    · rw [getElem!_set!_of_lt _ _ _ hq', ite_eq_right (fun e' => hp (by rw [e']; exact hq))]
    · rw [getElem!_neg _ _ (by simpa using hq'), getElem!_neg b _ hq']

/-- `trsvTUpperStep` on a vector with stride `1` is `colUpperStep` at its offset. -/
private theorem trsvTUpperStep_eq_col (d : Diag) (A : Mat m m) (x : Vec m) (hx : x.inc = 1) :
    trsvTUpperStep d A x = colUpperStep d A x.off := by
  funext j b
  rw [trsvTUpperStep, modifyAt_of_lt _ _ (Nat.lt_succ_self j), modifyAt_self]
  simp [colUpperStep, colUpperVal, Vec.stride, Stride.idx, hx]

/-- `trsvTLowerAscStep` on a vector with stride `1` is `colLowerStep` at its offset. -/
private theorem trsvTLowerAscStep_eq_col (d : Diag) (A : Mat m m) (x : Vec m)
    (hx : x.inc = 1) : trsvTLowerAscStep d A x = colLowerStep d A x.off := by
  funext k b
  rw [trsvTLowerAscStep, modifyAt_of_lt _ _ (Nat.lt_succ_self _), modifyAt_self]
  simp [colLowerStep, colLowerVal, Vec.stride, Stride.idx, hx]

/--
The upper solves of `trsmT` for the four columns at the indices `o₀` to `o₃` of `b`, with stride
`1`, together: at step `j`, it computes the four dot products of element `j`, which share the reads
of column `j` of `A`, then writes the four elements. The four sums are independent, so that their
additions overlap. Each element gets the operations of `trsvTUpper`, in the same order.
-/
public def trsmTUpper4Data (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
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
  inplace b do
    for j in 0...mu do
      have q₀ : (c₀ + j).toNat < b.size := by grind
      have q₁ : (c₁ + j).toNat < b.size := by grind
      have q₂ : (c₂ + j).toNat < b.size := by grind
      have q₃ : (c₃ + j).toNat < b.size := by grind
      let v₀ := b[c₀ + j]
      let v₁ := b[c₁ + j]
      let v₂ := b[c₂ + j]
      let v₃ := b[c₃ + j]
      for i in 0...j with (s₀ := v₀) (s₁ := v₁) (s₂ := v₂) (s₃ := v₃) do
        have p₀ : (c₀ + i).toNat < b.size := by grind
        have p₁ : (c₁ + i).toNat < b.size := by grind
        have p₂ : (c₂ + i).toNat < b.size := by grind
        have p₃ : (c₃ + i).toNat < b.size := by grind
        let a := A.uget ao al rfl rfl hs.1 i j (by lia) (by lia)
        s₀ := s₀ - a * b[c₀ + i]
        s₁ := s₁ - a * b[c₁ + i]
        s₂ := s₂ - a * b[c₂ + i]
        s₃ := s₃ - a * b[c₃ + i]
      let ajj := A.uget ao al rfl rfl hs.1 j j (by lia) (by lia)
      b[c₀ + j] := d.apply s₀ ajj
      b[c₁ + j] := d.apply s₁ ajj
      b[c₂ + j] := d.apply s₂ ajj
      b[c₃ + j] := d.apply s₃ ajj

public theorem trsmTUpper4Data_eq (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trsmTUpper4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs =
      iterRange (fun j c => colUpperStep d A o₃ j (colUpperStep d A o₂ j
        (colUpperStep d A o₁ j (colUpperStep d A o₀ j c)))) 0 m b := by
  have hmu : m.toUSize.toNat = m := by grind
  have e₀ : o₀.toUSize.toNat = o₀ := by grind
  have e₁ : o₁.toUSize.toNat = o₁ := by grind
  have e₂ : o₂.toUSize.toNat = o₂ := by grind
  have e₃ : o₃.toUSize.toNat = o₃ := by grind
  unfold trsmTUpper4Data
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun j c => colUpperStep d A o₃ j (colUpperStep d A o₂ j
    (colUpperStep d A o₁ j (colUpperStep d A o₀ j c))))
    (hF := fun _ _ => by simp [colUpperStep])]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
  · intro j _ hj next a h
    rw [hmu] at hj
    have hb : b.size < USize.size := hs.2
    have t₀ : (o₀.toUSize + j).toNat = o₀ + j.toNat := by grind
    have t₁ : (o₁.toUSize + j).toNat = o₁ + j.toNat := by grind
    have t₂ : (o₂.toUSize + j).toNat = o₂ + j.toNat := by grind
    have t₃ : (o₃.toUSize + j).toNat = o₃ + j.toNat := by grind
    simp only [Tail.run_readThen, Tail.forIn4_eq]
    rw [run_forIn4From_read (f₀ := fun i s => s - A.data[A.off + A.ld * j.toNat + i]! * a[o₀ + i]!)
      (f₁ := fun i s => s - A.data[A.off + A.ld * j.toNat + i]! * a[o₁ + i]!)
      (f₂ := fun i s => s - A.data[A.off + A.ld * j.toNat + i]! * a[o₂ + i]!)
      (f₃ := fun i s => s - A.data[A.off + A.ld * j.toNat + i]! * a[o₃ + i]!)]
    · simp only [Tail.run_writeThen, USize.toNat_zero, iterRange_eq_fold]
      apply run_congr
      have n₁₀ : ¬colIdx o₁ m (o₀ + j.toNat) := by simp only [colIdx]; lia
      have n₂₀ : ¬colIdx o₂ m (o₀ + j.toNat) := by simp only [colIdx]; lia
      have n₃₀ : ¬colIdx o₃ m (o₀ + j.toNat) := by simp only [colIdx]; lia
      have n₂₁ : ¬colIdx o₂ m (o₁ + j.toNat) := by simp only [colIdx]; lia
      have n₃₁ : ¬colIdx o₃ m (o₁ + j.toNat) := by simp only [colIdx]; lia
      have n₃₂ : ¬colIdx o₃ m (o₂ + j.toNat) := by simp only [colIdx]; lia
      simp only [colUpperStep, colUpperVal_set! d A hj n₁₀, colUpperVal_set! d A hj n₂₀,
        colUpperVal_set! d A hj n₃₀, colUpperVal_set! d A hj n₂₁, colUpperVal_set! d A hj n₃₁,
        colUpperVal_set! d A hj n₃₂]
      simp only [colUpperVal, t₀, t₁, t₂, t₃, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]
    · intro i _ hi next' s₀ s₁ s₂ s₃
      have u₀ : (o₀.toUSize + i).toNat = o₀ + i.toNat := by grind
      have u₁ : (o₁.toUSize + i).toNat = o₁ + i.toNat := by grind
      have u₂ : (o₂.toUSize + i).toNat = o₂ + i.toNat := by grind
      have u₃ : (o₃.toUSize + i).toNat = o₃ + i.toNat := by grind
      simp only [Tail.run_readThen, u₀, u₁, u₂, u₃, getElem_eq_getElem!, Mat.uget_eq_getElem,
        Mat.getElem_def]

/--
The lower solves in increasing order of `trsmT` for the four columns at the indices `o₀` to `o₃`
of `b`, with stride `1`, together, as `trsmTUpper4Data` does: at step `k`, it computes the four dot
products of element `j = m - 1 - k`, then writes the four elements. Each element gets the
operations of `trsvTLowerAsc`, in the same order.
-/
public def trsmTLower4Data (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
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
  inplace b do
    for k in 0...mu do
      have hj : (mu - 1 - k).toNat = m - 1 - k.toNat := by grind
      have hjn : (mu - 1 - k).toNat < m := by lia
      have q₀ : (c₀ + (mu - 1 - k)).toNat < b.size := by grind
      have q₁ : (c₁ + (mu - 1 - k)).toNat < b.size := by grind
      have q₂ : (c₂ + (mu - 1 - k)).toNat < b.size := by grind
      have q₃ : (c₃ + (mu - 1 - k)).toNat < b.size := by grind
      let v₀ := b[c₀ + (mu - 1 - k)]
      let v₁ := b[c₁ + (mu - 1 - k)]
      let v₂ := b[c₂ + (mu - 1 - k)]
      let v₃ := b[c₃ + (mu - 1 - k)]
      for t in 0...k with (s₀ := v₀) (s₁ := v₁) (s₂ := v₂) (s₃ := v₃) do
        have hi : (mu - 1 - k + 1 + t).toNat < m := by grind
        have p₀ : (c₀ + (mu - 1 - k + 1 + t)).toNat < b.size := by grind
        have p₁ : (c₁ + (mu - 1 - k + 1 + t)).toNat < b.size := by grind
        have p₂ : (c₂ + (mu - 1 - k + 1 + t)).toNat < b.size := by grind
        have p₃ : (c₃ + (mu - 1 - k + 1 + t)).toNat < b.size := by grind
        let a := A.uget ao al rfl rfl hs.1 (mu - 1 - k + 1 + t) (mu - 1 - k) hi hjn
        s₀ := s₀ - a * b[c₀ + (mu - 1 - k + 1 + t)]
        s₁ := s₁ - a * b[c₁ + (mu - 1 - k + 1 + t)]
        s₂ := s₂ - a * b[c₂ + (mu - 1 - k + 1 + t)]
        s₃ := s₃ - a * b[c₃ + (mu - 1 - k + 1 + t)]
      let ajj := A.uget ao al rfl rfl hs.1 (mu - 1 - k) (mu - 1 - k) hjn hjn
      b[c₀ + (mu - 1 - k)] := d.apply s₀ ajj
      b[c₁ + (mu - 1 - k)] := d.apply s₁ ajj
      b[c₂ + (mu - 1 - k)] := d.apply s₂ ajj
      b[c₃ + (mu - 1 - k)] := d.apply s₃ ajj

public theorem trsmTLower4Data_eq (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat) (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trsmTLower4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs =
      iterRange (fun k c => colLowerStep d A o₃ k (colLowerStep d A o₂ k
        (colLowerStep d A o₁ k (colLowerStep d A o₀ k c)))) 0 m b := by
  have hmu : m.toUSize.toNat = m := by grind
  have e₀ : o₀.toUSize.toNat = o₀ := by grind
  have e₁ : o₁.toUSize.toNat = o₁ := by grind
  have e₂ : o₂.toUSize.toNat = o₂ := by grind
  have e₃ : o₃.toUSize.toNat = o₃ := by grind
  unfold trsmTLower4Data
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun k c => colLowerStep d A o₃ k (colLowerStep d A o₂ k
    (colLowerStep d A o₁ k (colLowerStep d A o₀ k c))))
    (hF := fun _ _ => by simp [colLowerStep])]
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
    rw [run_forIn4From_read (f₀ := fun t s => s - A.data[A.off + A.ld * (m - 1 - k.toNat) +
        (m - 1 - k.toNat + 1 + t)]! * a[o₀ + (m - 1 - k.toNat + 1 + t)]!)
      (f₁ := fun t s => s - A.data[A.off + A.ld * (m - 1 - k.toNat) +
        (m - 1 - k.toNat + 1 + t)]! * a[o₁ + (m - 1 - k.toNat + 1 + t)]!)
      (f₂ := fun t s => s - A.data[A.off + A.ld * (m - 1 - k.toNat) +
        (m - 1 - k.toNat + 1 + t)]! * a[o₂ + (m - 1 - k.toNat + 1 + t)]!)
      (f₃ := fun t s => s - A.data[A.off + A.ld * (m - 1 - k.toNat) +
        (m - 1 - k.toNat + 1 + t)]! * a[o₃ + (m - 1 - k.toNat + 1 + t)]!)]
    · simp only [Tail.run_writeThen, USize.toNat_zero, iterRange_eq_fold]
      apply run_congr
      have n₁₀ : ¬colIdx o₁ m (o₀ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₂₀ : ¬colIdx o₂ m (o₀ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₃₀ : ¬colIdx o₃ m (o₀ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₂₁ : ¬colIdx o₂ m (o₁ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₃₁ : ¬colIdx o₃ m (o₁ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      have n₃₂ : ¬colIdx o₃ m (o₂ + (m - 1 - k.toNat)) := by simp only [colIdx]; lia
      simp only [colLowerStep, colLowerVal_set! d A hk n₁₀, colLowerVal_set! d A hk n₂₀,
        colLowerVal_set! d A hk n₃₀, colLowerVal_set! d A hk n₂₁, colLowerVal_set! d A hk n₃₁,
        colLowerVal_set! d A hk n₃₂]
      simp only [colLowerVal, t₀, t₁, t₂, t₃, hj, set_eq_set!, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]
    · intro t _ ht next' s₀ s₁ s₂ s₃
      have hjt : (m.toUSize - 1 - k + 1 + t).toNat = m - 1 - k.toNat + 1 + t.toNat := by grind
      have u₀ : (o₀.toUSize + (m.toUSize - 1 - k + 1 + t)).toNat =
          o₀ + (m - 1 - k.toNat + 1 + t.toNat) := by grind
      have u₁ : (o₁.toUSize + (m.toUSize - 1 - k + 1 + t)).toNat =
          o₁ + (m - 1 - k.toNat + 1 + t.toNat) := by grind
      have u₂ : (o₂.toUSize + (m.toUSize - 1 - k + 1 + t)).toNat =
          o₂ + (m - 1 - k.toNat + 1 + t.toNat) := by grind
      have u₃ : (o₃.toUSize + (m.toUSize - 1 - k + 1 + t)).toNat =
          o₃ + (m - 1 - k.toNat + 1 + t.toNat) := by grind
      simp only [Tail.run_readThen, u₀, u₁, u₂, u₃, hj, hjt, getElem_eq_getElem!,
        Mat.uget_eq_getElem, Mat.getElem_def]

/-- The step of the column solve of `trsmT` for the triangle `uplo`, on the column at `o`. -/
@[expose] public def colTStep (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat) :
    Nat → Float64Array → Float64Array :=
  match uplo with
  | .upper => colUpperStep d A o
  | .lower => colLowerStep d A o

/-- The column solve of `trsmT` on the column at `o`, with stride `1`. -/
@[expose] public def colTSolve (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat)
    (c : Float64Array) : Float64Array :=
  iterRange (colTStep uplo d A o) 0 m c

private theorem local_colTStep (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat) {k : Nat}
    (hk : k < m) : Local (colIdx o m) (colTStep uplo d A o k) := by
  cases uplo
  · exact local_colUpperStep d A o hk
  · exact local_colLowerStep d A o hk

private theorem local_colTSolve (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat) :
    Local (colIdx o m) (colTSolve uplo d A o) :=
  Local.iterRange fun _ _ hk => local_colTStep uplo d A o hk

@[simp] private theorem size_colTSolve (uplo : Uplo) (d : Diag) (A : Mat m m) (o : Nat)
    (c : Float64Array) : (colTSolve uplo d A o c).size = c.size :=
  (local_colTSolve uplo d A o).1 c

/-- The four column solves of `trsmT` for the triangle `uplo`, together. -/
public def trsmT4Data (uplo : Uplo) (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat)
    (b : Float64Array)
    (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃) (h₄ : o₃ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size) : Float64Array :=
  match uplo with
  | .upper => trsmTUpper4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs
  | .lower => trsmTLower4Data d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs

/-- The four column solves together are the four solves, one column after the other. -/
public theorem trsmT4Data_eq (uplo : Uplo) (d : Diag) (A : Mat m m) (o₀ o₁ o₂ o₃ : Nat)
    (b : Float64Array) (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ o₂) (h₃ : o₂ + m ≤ o₃)
    (h₄ : o₃ + m ≤ b.size) (hs : A.data.size < USize.size ∧ b.size < USize.size) :
    trsmT4Data uplo d A o₀ o₁ o₂ o₃ b h₁ h₂ h₃ h₄ hs =
      colTSolve uplo d A o₃ (colTSolve uplo d A o₂ (colTSolve uplo d A o₁
        (colTSolve uplo d A o₀ b))) := by
  cases uplo
  · rw [trsmT4Data, trsmTUpper4Data_eq]
    exact iterRange_four_cols h₁ h₂ h₃ (fun _ hk => local_colUpperStep d A o₀ hk)
      (fun _ hk => local_colUpperStep d A o₁ hk) (fun _ hk => local_colUpperStep d A o₂ hk)
      (fun _ hk => local_colUpperStep d A o₃ hk) b
  · rw [trsmT4Data, trsmTLower4Data_eq]
    exact iterRange_four_cols h₁ h₂ h₃ (fun _ hk => local_colLowerStep d A o₀ hk)
      (fun _ hk => local_colLowerStep d A o₁ hk) (fun _ hk => local_colLowerStep d A o₂ hk)
      (fun _ hk => local_colLowerStep d A o₃ hk) b

private theorem scalData_colOf (α : Float) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) :
    Vec.scalData α (colOf off ld sz hsz b hb j hj) = colScale α (off + ld * j) m b := by
  rw [Vec.scalData_eq]; rfl

private theorem trsvTAscData_colOf (uplo : Uplo) (d : Diag) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float64Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) :
    trsvTAscData uplo d A (colOf off ld sz hsz b hb j hj) =
      colTSolve uplo d A (off + ld * j) b := by
  cases uplo
  · show trsvTUpperData d A _ = _
    rw [trsvTUpperData_eq_iterRange, trsvTUpperStep_eq_col d A _ rfl]; rfl
  · show trsvTLowerAscData d A _ = _
    rw [trsvTLowerAscData_eq_iterRange, trsvTLowerAscStep_eq_col d A _ rfl]; rfl

private theorem trsmTLoop_congr (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) {j j' : Nat}
    (hj : j = j') {b b' : Float64Array} (e : b = b') (hb : b.size = sz) (hb' : b'.size = sz) :
    trsmTLoop uplo d α A off ld sz hsz j b hb = trsmTLoop uplo d α A off ld sz hsz j' b' hb' := by
  subst hj e; rfl

/-- A step of `trsmTLoop` scales column `j`, then solves it. -/
private theorem trsmTLoop_succ (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) {j : Nat} (hj : j < n)
    (b : Float64Array) (hb : b.size = sz) :
    trsmTLoop uplo d α A off ld sz hsz j b hb =
      trsmTLoop uplo d α A off ld sz hsz (j + 1)
        (colTSolve uplo d A (off + ld * j) (colScale α (off + ld * j) m b))
        (by simpa using hb) := by
  rw [trsmTLoop, dite_eq_left hj]
  apply trsmTLoop_congr _ _ _ _ _ _ _ _ rfl
  rw [trsvTAscData_colOf, scalData_colOf]

private theorem col_add_le {off ld j : Nat} (hml : m ≤ ld) :
    off + ld * j + m ≤ off + ld * (j + 1) := by
  rw [Nat.mul_succ]; lia

/--
The loop of `trsmT` over the columns from `j`, as `trsmTLoop`, but four columns at a time by
`trsmT4Data`, then one at a time. It needs sizes that fit a `USize`.
-/
public def trsmTLoop4 (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (hml : m ≤ ld)
    (hs : A.data.size < USize.size ∧ sz < USize.size) (j : Nat) (b : Float64Array)
    (hb : b.size = sz) : Float64Array :=
  if h4 : j + 4 ≤ n ∧ off + ld * (j + 3) + m ≤ sz then
    let b₀ := Vec.scalData α (colOf off ld sz hsz b hb j (by lia))
    have hb₀ : b₀.size = sz := size_scalData_colOf ..
    let b₁ := Vec.scalData α (colOf off ld sz hsz b₀ hb₀ (j + 1) (by lia))
    have hb₁ : b₁.size = sz := size_scalData_colOf ..
    let b₂ := Vec.scalData α (colOf off ld sz hsz b₁ hb₁ (j + 2) (by lia))
    have hb₂ : b₂.size = sz := size_scalData_colOf ..
    let b₃ := Vec.scalData α (colOf off ld sz hsz b₂ hb₂ (j + 3) (by lia))
    have hb₃ : b₃.size = sz := size_scalData_colOf ..
    trsmTLoop4 uplo d α A off ld sz hsz hml hs (j + 4)
      (trsmT4Data uplo d A (off + ld * j) (off + ld * (j + 1)) (off + ld * (j + 2))
        (off + ld * (j + 3)) b₃ (col_add_le hml) (col_add_le hml) (col_add_le hml)
        (by rw [hb₃]; exact h4.2) ⟨hs.1, by rw [hb₃]; exact hs.2⟩)
      (by rw [trsmT4Data_eq]; simpa using hb₃)
  else if hj : j < n then
    trsmTLoop4 uplo d α A off ld sz hsz hml hs (j + 1)
      (trsvTAscData uplo d A (colOf off ld sz hsz (Vec.scalData α (colOf off ld sz hsz b hb j hj))
        (size_scalData_colOf ..) j hj))
      (size_trsvTAscData_colOf ..)
  else b
termination_by n - j

/-- `trsmTLoop4` is `trsmTLoop`. -/
private theorem trsmTLoop4_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (off ld sz : Nat) (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (hml : m ≤ ld)
    (hs : A.data.size < USize.size ∧ sz < USize.size) (j : Nat) (b : Float64Array)
    (hb : b.size = sz) :
    trsmTLoop4 uplo d α A off ld sz hsz hml hs j b hb =
      trsmTLoop uplo d α A off ld sz hsz j b hb := by
  obtain ⟨e, he⟩ : ∃ e, n - j = e := ⟨_, rfl⟩
  induction e using Nat.strongRecOn generalizing j b with
  | ind e ih =>
    rw [trsmTLoop4]
    split
    · rename_i h4
      rw [ih (n - (j + 4)) (by lia) _ _ _ rfl]
      symm
      rw [trsmTLoop_succ (j := j) uplo d α A off ld sz hsz (by lia),
        trsmTLoop_succ (j := j + 1) uplo d α A off ld sz hsz (by lia),
        trsmTLoop_succ (j := j + 1 + 1) uplo d α A off ld sz hsz (by lia),
        trsmTLoop_succ (j := j + 1 + 1 + 1) uplo d α A off ld sz hsz (by lia)]
      apply trsmTLoop_congr _ _ _ _ _ _ _ _ (by lia)
      symm
      simp only [trsmT4Data_eq, scalData_colOf]
      exact four_cols_reorder (col_add_le hml) (col_add_le hml) (col_add_le hml)
        (local_colScale _ _ _) (local_colScale _ _ _) (local_colScale _ _ _)
        (local_colTSolve _ _ _ _) (local_colTSolve _ _ _ _) (local_colTSolve _ _ _ _) b
    · split
      · rename_i h4 hj
        rw [ih (n - (j + 1)) (by lia) _ _ _ rfl]
        conv => rhs; rw [trsmTLoop, dite_eq_left hj]
      · rename_i h4 hj
        rw [trsmTLoop, dite_eq_right hj]

/-- The array of `trsmT`. -/
public def trsmTData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0
  else if hs : A.data.size < USize.size ∧ B.data.size < USize.size then
    trsmTLoop4 uplo d α A B.off B.ld B.data.size B.bound B.le_ld hs 0 B.data rfl
  else trsmTLoop uplo d α A B.off B.ld B.data.size B.bound 0 B.data rfl

public theorem trsmTData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    trsmTData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmTAt uplo d α A B i j := by
  unfold trsmTData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have e : (if hs : A.data.size < USize.size ∧ B.data.size < USize.size then
        trsmTLoop4 uplo d α A B.off B.ld B.data.size B.bound B.le_ld hs 0 B.data rfl
      else trsmTLoop uplo d α A B.off B.ld B.data.size B.bound 0 B.data rfl) =
        trsmTLoop uplo d α A B.off B.ld B.data.size B.bound 0 B.data rfl := by
      split
      · exact trsmTLoop4_eq ..
      · rfl
    rw [e, trsmTLoop_eq uplo d α A B 0 (Nat.zero_le _) _ rfl
      (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmTColAt, trsmTAt, scaledCol, hα]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmTAt, betaMul, hα, show ((0 : Float) == 0) = true from rfl]

/--
`trsmT uplo d α A B` solves `Aᵀ * X = α * B` for the triangle `uplo` of `A`, with a unit diagonal
if `d` is `.unit`, over `B`, by the loops of the reference BLAS for `TRANSA = 'T'`: for each column
`j` of `B`, it solves `Aᵀ * x = α * B[:, j]` by the loops of `trsvT`, which subtract dot products
of the columns of `A` with the elements already solved, in increasing order of the rows. It
updates `B` in place when its array is not shared, and leaves the elements of the array outside
`B` unchanged. As in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when
`α = 0`, reads only the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`, and
doesn't check for a zero on the diagonal.
-/
@[expose] public def trsmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    Mat m n where
  data := trsmTData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trsmTData_eq, size_mapMat]; exact B.bound

/-- The array of `trsmT uplo d α A B` is the array of `B` with its elements solved. -/
public theorem data_trsmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) :
    (trsmT uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmTAt uplo d α A B i j :=
  trsmTData_eq uplo d α A B

@[simp] public theorem off_trsmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trsmT uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trsmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m)
    (B : Mat m n) : (trsmT uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trsmT uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trsmT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) : (trsmT uplo d α A B)[(i, j)] = trsmTAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trsmT uplo d α A B) rfl rfl i j h

/--
Element `(i, j)` of `X = trsmT .upper d α A B` is `0` when `α = 0`, and otherwise `α * B[i, j]`,
minus the terms `A[l, i] * X[l, j]` for `l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal
is unit: forward substitution with `Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsmT_upper (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trsmT .upper d α A B)[(i, j)] =
      if α == 0 then 0
      else d.apply (Nat.fold i (fun l hl s =>
          s - A[(l, i)]'⟨by lia, h.1⟩ * (trsmT .upper d α A B)[(l, j)]'⟨by lia, h.2⟩)
        (α * B[(i, j)])) A[(i, i)] := by
  rw [getElem_trsmT _ _ _ _ _ _ _ h, trsmTAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trsvTAscSol]
    rw [trsvTUpper_eq d A _ h.1]
    congr 1
    · congr 1
      · funext l hl s
        rw [getElem_trsmT _ _ _ _ _ _ _ ⟨by lia, h.2⟩, trsmTAt, hα]
        rfl
      · simp only [scaledCol, Vec.getElem_ofFn, getElem_def]
        rw [getElem!_pos B.data _ (B.index_lt h.1 h.2)]
  · rfl

/--
Element `(i, j)` of `X = trsmT .lower d α A B` is `0` when `α = 0`, and otherwise `α * B[i, j]`,
minus the terms `A[l, i] * X[l, j]` for `l = i + 1, …, m - 1`, divided by `A[i, i]` unless the
diagonal is unit: back substitution with `Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsmT_lower (d : Diag) (α : Float) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trsmT .lower d α A B)[(i, j)] =
      if α == 0 then 0
      else d.apply (Nat.fold (m - 1 - i) (fun t _ s =>
          s - A[(i + 1 + t, i)]'⟨by lia, h.1⟩ *
            (trsmT .lower d α A B)[(i + 1 + t, j)]'⟨by lia, h.2⟩)
        (α * B[(i, j)])) A[(i, i)] := by
  rw [getElem_trsmT _ _ _ _ _ _ _ h, trsmTAt]
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, trsvTAscSol]
    rw [trsvTLowerAsc_eq d A _ h.1]
    congr 1
    · congr 1
      · funext t ht s
        rw [getElem_trsmT _ _ _ _ _ _ _ ⟨by lia, h.2⟩, trsmTAt, hα]
        rfl
      · simp only [scaledCol, Vec.getElem_ofFn, getElem_def]
        rw [getElem!_pos B.data _ (B.index_lt h.1 h.2)]
  · rfl

/-! ## `trsmRightT` -/

/--
Element `(i, j)` of the solution `Z` of `Z * Aᵀ = B` for the upper triangle of `A`, on the arrays:
`B[i, j]`, minus the terms `A[j, k] * Z[i, k]` for `k = n - 1, …, j + 1`, divided by `A[j, j]`
unless the diagonal is unit. `trsmRightT` is `α * Z`.
-/
public def trsmRightTUpper (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * (n - 1 - t) + j]! * trsmRightTUpper d A B i (n - 1 - t))
    B.data[B.off + B.ld * j + i]!) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/--
Element `(i, j)` of the solution `Z` of `Z * Aᵀ = B` for the lower triangle of `A`, on the arrays:
`B[i, j]`, minus the terms `A[j, k] * Z[i, k]` for `k = 0, …, j - 1`, divided by `A[j, j]` unless
the diagonal is unit. `trsmRightT` is `α * Z`.
-/
public def trsmRightTLower (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) : Float :=
  d.apply (Nat.fold j (fun k _hk s =>
      s - A.data[A.off + A.ld * k + j]! * trsmRightTLower d A B i k)
    B.data[B.off + B.ld * j + i]!) A.data[A.off + A.ld * j + j]!
termination_by j
decreasing_by exact _hk

/--
Element `(i, j)`, for `i < m` and `j < n`, of the solution `Z` of `Z * Aᵀ = B` for the upper
triangle of `A` is `B[i, j]`, minus the terms `A[j, k] * Z[i, k]` for `k = n - 1, …, j + 1`,
divided by `A[j, j]` unless the diagonal is unit.
-/
public theorem trsmRightTUpper_eq (d : Diag) (A : Mat n n) (B : Mat m n) {i j : Nat}
    (h : i < m ∧ j < n) :
    trsmRightTUpper d A B i j = d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
        s - A[(j, n - 1 - t)]'⟨h.2, by lia⟩ * trsmRightTUpper d A B i (n - 1 - t)) B[(i, j)])
      A[(j, j)] := by
  rw [trsmRightTUpper, getElem!_pos B.data _ (B.index_lt h.1 h.2),
    getElem!_pos A.data _ (A.index_lt h.2 h.2)]
  congr 2
  funext t ht s
  rw [getElem!_pos A.data _ (A.index_lt h.2 (by lia))]
  rfl

/--
Element `(i, j)`, for `i < m` and `j < n`, of the solution `Z` of `Z * Aᵀ = B` for the lower
triangle of `A` is `B[i, j]`, minus the terms `A[j, k] * Z[i, k]` for `k = 0, …, j - 1`, divided by
`A[j, j]` unless the diagonal is unit.
-/
public theorem trsmRightTLower_eq (d : Diag) (A : Mat n n) (B : Mat m n) {i j : Nat}
    (h : i < m ∧ j < n) :
    trsmRightTLower d A B i j = d.apply (Nat.fold j (fun k hk s =>
        s - A[(j, k)]'⟨h.2, by lia⟩ * trsmRightTLower d A B i k) B[(i, j)]) A[(j, j)] := by
  rw [trsmRightTLower, getElem!_pos B.data _ (B.index_lt h.1 h.2),
    getElem!_pos A.data _ (A.index_lt h.2 h.2)]
  congr 2
  funext k hk s
  rw [getElem!_pos A.data _ (A.index_lt h.2 (by lia))]
  rfl

/-- Dividing the rows `0 ≤ i < d.rows m` by `t` is `Diag.apply` on all of them. -/
private theorem modifyAt_rows (b : Float64Array) (idx : Nat → Nat) (d : Diag) {mu : USize}
    (hmu : mu.toNat = m) (t : Float) :
    b.modifyAt idx 0 (d.rows mu).toNat (fun _ v => v / t) =
      b.modifyAt idx 0 m fun _ v => d.apply v t := by
  cases d
  · simp only [Diag.rows, USize.toNat_zero, modifyAt_self, Diag.apply]
    rw [modifyAt_id]
  · simp only [Diag.rows, hmu, Diag.apply]

/--
Subtracting `w k` times column `k` of `c` from column `j`, for the columns `k` from `lo` to
`lo + K - 1`, which are not column `j`, subtracts the terms in that order from each element.
-/
private theorem iterRange_subCols (c : Float64Array) (oj : Nat) (ok : Nat → Nat) (w : Nat → Float)
    (lo K : Nat) (hd : ∀ k, lo ≤ k → k < lo + K → ∀ i, i < m → ∀ i', i' < m → oj + i ≠ ok k + i') :
    iterRange (fun k c => c.modifyAt (Stride.mk oj 1).idx 0 m fun i v => v - w k * c[ok k + i]!)
        lo (lo + K) c =
      c.modifyAt (Stride.mk oj 1).idx 0 m fun i v =>
        Nat.fold K (fun t _ s => s - w (lo + t) * c[ok (lo + t) + i]!) v := by
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

/-! ### The upper triangle -/

/--
The value of column `j` of the upper solve from its old value `v`, with the columns after it.
-/
private def trsmRightTUpperG (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) (v : Float) :
    Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * (n - 1 - t) + j]! * trsmRightTUpper d A B i (n - 1 - t)) v)
    A.data[A.off + A.ld * j + j]!

private theorem trsmRightTUpper_eq_G (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) :
    trsmRightTUpper d A B i j = trsmRightTUpperG d A B i j B.data[B.off + B.ld * j + i]! := by
  rw [trsmRightTUpper]; rfl

/-- The step `t` of the upper solve, for column `j = n - 1 - t`, on the array `c`. -/
private def trsmRightTUpperCol (d : Diag) (A : Mat n n) (B : Mat m n) (t : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - t)) 1).idx 0 m fun i v =>
    d.apply (Nat.fold (n - 1 - (n - 1 - t)) (fun t' _ s =>
        s - A.data[A.off + A.ld * (n - 1 - t') + (n - 1 - t)]! *
          c[B.off + B.ld * (n - 1 - t') + i]!) v)
      A.data[A.off + A.ld * (n - 1 - t) + (n - 1 - t)]!

private theorem iterRange_trsmRightTUpperCol (d : Diag) (A : Mat n n) (B : Mat m n) {T : Nat}
    (hT : T ≤ n) :
    iterRange (trsmRightTUpperCol d A B) 0 T B.data =
      mapMat B.data B.off B.ld m (n - T) n (trsmRightTUpperG d A B) := by
  induction T with
  | zero => rw [iterRange_self, Nat.sub_zero, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ T ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trsmRightTUpperCol,
      show n - T = n - 1 - T + 1 by lia, show n - (T + 1) = n - 1 - T by lia,
      ← modifyAt_col_mapMat_lo _ _ _ B.le_ld (show n - 1 - T < n by lia)]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [trsmRightTUpperG]
    congr 2
    funext t' ht' s
    rw [getElem!_mapMat_col _ _ _ _ _ _ B.le_ld ⟨by lia, by lia⟩ hi (B.index_lt hi (by lia)),
      ← trsmRightTUpper_eq_G]

/-! ### The lower triangle -/

/--
The value of column `j` of the lower solve from its old value `v`, with the columns before it.
-/
private def trsmRightTLowerG (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) (v : Float) :
    Float :=
  d.apply (Nat.fold j (fun k _ s => s - A.data[A.off + A.ld * k + j]! * trsmRightTLower d A B i k)
    v) A.data[A.off + A.ld * j + j]!

private theorem trsmRightTLower_eq_G (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) :
    trsmRightTLower d A B i j = trsmRightTLowerG d A B i j B.data[B.off + B.ld * j + i]! := by
  rw [trsmRightTLower]; rfl

/-- The step of the lower solve for column `j`, on the array `c`. -/
private def trsmRightTLowerCol (d : Diag) (A : Mat n n) (B : Mat m n) (j : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt (Stride.mk (B.off + B.ld * j) 1).idx 0 m fun i v =>
    d.apply (Nat.fold j (fun k _ s => s - A.data[A.off + A.ld * k + j]! * c[B.off + B.ld * k + i]!)
      v) A.data[A.off + A.ld * j + j]!

private theorem iterRange_trsmRightTLowerCol (d : Diag) (A : Mat n n) (B : Mat m n) {J : Nat}
    (hJ : J ≤ n) :
    iterRange (trsmRightTLowerCol d A B) 0 J B.data =
      mapMat B.data B.off B.ld m 0 J (trsmRightTLowerG d A B) := by
  induction J with
  | zero => rw [iterRange_self, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ J ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia), trsmRightTLowerCol,
      ← modifyAt_col_mapMat _ _ _ B.le_ld J]
    apply modifyAt_congr_fun
    intro i v _ hi
    simp only [trsmRightTLowerG]
    congr 2
    funext k hk s
    rw [getElem!_mapMat_col _ _ _ _ _ _ B.le_ld ⟨Nat.zero_le _, hk⟩ hi (B.index_lt hi (by lia)),
      ← trsmRightTLower_eq_G]

/-! ### A column at a time, four columns per pass -/

/--
The column whose terms the solve of a column subtracts at its step `t`: `n - 1 - t`, from the
right, for the upper triangle (`up`), and `t`, from the left, for the lower one.
-/
@[expose] public def subColIdx (n : Nat) (up : Bool) (t : Nat) : Nat := if up then n - 1 - t else t

/-- `subColIdx` on `USize` indices. -/
@[inline] public def subColIdxU (nu : USize) (up : Bool) (t : USize) : USize :=
  if up then nu - 1 - t else t

private theorem toNat_subColIdxU {nu t : USize} (hnu : nu.toNat = n) (up : Bool)
    (ht : t.toNat < n) : (subColIdxU nu up t).toNat = subColIdx n up t.toNat := by
  cases up
  · simp only [subColIdxU, subColIdx, Bool.false_eq_true, ↓reduceIte]
  · simp only [subColIdxU, subColIdx, ↓reduceIte]; grind

/--
The solve of column `j` of `Z * Aᵀ = B`, on the array `c` of a matrix with offset `bo` and leading
dimension `bl`: it subtracts the terms `A[j, k] * c[i, k]` for the columns `k = subColIdx n up t`,
`t = 0, …, cnt - 1`, in that order, from each element `i` of column `j`, then divides it by
`A[j, j]` unless the diagonal is unit.
-/
@[expose] public def trsmRightTColModel (d : Diag) (A : Mat n n) (up : Bool) (bo bl j cnt : Nat)
    (c : Float64Array) : Float64Array :=
  c.modifyAt (Stride.mk (bo + bl * j) 1).idx 0 m fun i v =>
    d.apply (Nat.fold cnt (fun t _ s =>
        s - A.data[A.off + A.ld * subColIdx n up t + j]! * c[bo + bl * subColIdx n up t + i]!) v)
      A.data[A.off + A.ld * j + j]!

/--
Steps that each write `G i c[idx i]! c[r₀ i]! c[r₁ i]! c[r₂ i]! c[r₃ i]!` at `idx i`, where the
indices `r₀` to `r₃` that they read are never written, are a `modifyAt` that reads the elements at
`r₀` to `r₃` in the array before the loop.
-/
private theorem iterRange_set!_read4 (a : Float64Array) (idx r₀ r₁ r₂ r₃ : Nat → Nat)
    (G : Nat → Float → Float → Float → Float → Float → Float) {lo hi : Nat}
    (hd : ∀ i, lo ≤ i → i < hi → ∀ i', lo ≤ i' → i' < hi →
      idx i ≠ r₀ i' ∧ idx i ≠ r₁ i' ∧ idx i ≠ r₂ i' ∧ idx i ≠ r₃ i') :
    iterRange (fun i c => c.set! (idx i) (G i c[idx i]! c[r₀ i]! c[r₁ i]! c[r₂ i]! c[r₃ i]!)) lo hi
        a =
      a.modifyAt idx lo hi fun i v => G i v a[r₀ i]! a[r₁ i]! a[r₂ i]! a[r₃ i]! := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), modifyAt_of_lt _ _ (by lia),
      ih _ (fun i h₁ h₂ i' h₃ h₄ => hd i (by lia) h₂ i' (by lia) h₄) (by lia)]
    apply modifyAt_congr_fun
    intro i v h₁ h₂
    have hne := hd lo (Nat.le_refl _) (by lia) i (by lia) h₂
    have key : ∀ q, idx lo ≠ q → ∀ w : Float, (a.set! (idx lo) w)[q]! = a[q]! := by
      intro q hq w
      by_cases hq' : q < a.size
      · rw [getElem!_set!_of_lt _ _ _ hq', ite_eq_right hq]
      · rw [getElem!_neg _ _ (by simpa using hq'), getElem!_neg a _ hq']
    rw [key _ hne.1, key _ hne.2.1, key _ hne.2.2.1, key _ hne.2.2.2]

private theorem toNat_off_add {o sz : Nat} {i : USize} (h : o + m ≤ sz)
    (hs : sz < USize.size) (hi : i.toNat < m) : (o.toUSize + i).toNat = o + i.toNat := by
  rw [USize.toNat_add, toNat_toUSize_of_lt (by lia)]
  exact Nat.mod_eq_of_lt (by lia)

private theorem col_off_le {bo bl k sz : Nat} (hk : k < n)
    (hb : bo + bl * (n - 1) + m ≤ sz) : bo + bl * k + m ≤ sz := by
  have := Nat.mul_le_mul_left bl (show k ≤ n - 1 by lia); lia

/--
The solve of column `j` of `Z * Aᵀ = B` in the array `b` of a matrix with offset `bo` and leading
dimension `bl`, as `trsmRightTColModel`: it subtracts the columns `subColIdx n up t` for
`t < cnt` four at a time, in one pass over the rows of column `j` that subtracts the four terms of
each element in order, then the rest one at a time, then divides the column by `A[j, j]` unless the
diagonal is unit. Each element gets the operations of the reference loops, in the same order.
-/
public def trsmRightTColData (d : Diag) (A : Mat n n) (up : Bool) (bo bl j cnt : Nat)
    (b : Float64Array) (hj : j < n) (hcnt : cnt ≤ n) (hk : ∀ t, t < cnt → subColIdx n up t < n)
    (hb : bo + bl * (n - 1) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size ∧ m < USize.size ∧ n < USize.size) :
    Float64Array :=
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  let nu := n.toUSize
  have hnu : nu.toNat = n := by grind
  let ju := j.toUSize
  have hju : ju.toNat = j := by grind
  let cu := cnt.toUSize
  have hcu : cu.toNat = cnt := by grind
  let ao := A.off.toUSize
  let al := A.ld.toUSize
  have hcj : bo + bl * j + m ≤ b.size := col_off_le hj hb
  let cj := (bo + bl * j).toUSize
  have ecj : cj.toNat = bo + bl * j := by grind
  let q4 := cu / 4
  have hq4 : q4.toNat = cnt / 4 := by simp only [q4, USize.toNat_div, hcu]; simp
  inplace b do
    for q in 0...q4 do
      have h₀ : (4 * q).toNat = 4 * q.toNat := by grind
      have h₁ : (4 * q + 1).toNat = 4 * q.toNat + 1 := by grind
      have h₂ : (4 * q + 2).toNat = 4 * q.toNat + 2 := by grind
      have h₃ : (4 * q + 3).toNat = 4 * q.toNat + 3 := by grind
      have hk₀ : (subColIdxU nu up (4 * q)).toNat < n := by
        rw [toNat_subColIdxU hnu up (by lia), h₀]; exact hk _ (by lia)
      have hk₁ : (subColIdxU nu up (4 * q + 1)).toNat < n := by
        rw [toNat_subColIdxU hnu up (by lia), h₁]; exact hk _ (by lia)
      have hk₂ : (subColIdxU nu up (4 * q + 2)).toNat < n := by
        rw [toNat_subColIdxU hnu up (by lia), h₂]; exact hk _ (by lia)
      have hk₃ : (subColIdxU nu up (4 * q + 3)).toNat < n := by
        rw [toNat_subColIdxU hnu up (by lia), h₃]; exact hk _ (by lia)
      let w₀ := A.uget ao al rfl rfl hs.1 ju (subColIdxU nu up (4 * q)) (by lia) hk₀
      let w₁ := A.uget ao al rfl rfl hs.1 ju (subColIdxU nu up (4 * q + 1)) (by lia) hk₁
      let w₂ := A.uget ao al rfl rfl hs.1 ju (subColIdxU nu up (4 * q + 2)) (by lia) hk₂
      let w₃ := A.uget ao al rfl rfl hs.1 ju (subColIdxU nu up (4 * q + 3)) (by lia) hk₃
      have g₀ := col_off_le (bo := bo) (bl := bl) hk₀ hb
      have g₁ := col_off_le (bo := bo) (bl := bl) hk₁ hb
      have g₂ := col_off_le (bo := bo) (bl := bl) hk₂ hb
      have g₃ := col_off_le (bo := bo) (bl := bl) hk₃ hb
      let o₀ := (bo + bl * (subColIdxU nu up (4 * q)).toNat).toUSize
      let o₁ := (bo + bl * (subColIdxU nu up (4 * q + 1)).toNat).toUSize
      let o₂ := (bo + bl * (subColIdxU nu up (4 * q + 2)).toNat).toUSize
      let o₃ := (bo + bl * (subColIdxU nu up (4 * q + 3)).toNat).toUSize
      have e₀ : o₀.toNat = bo + bl * (subColIdxU nu up (4 * q)).toNat := by grind
      have e₁ : o₁.toNat = bo + bl * (subColIdxU nu up (4 * q + 1)).toNat := by grind
      have e₂ : o₂.toNat = bo + bl * (subColIdxU nu up (4 * q + 2)).toNat := by grind
      have e₃ : o₃.toNat = bo + bl * (subColIdxU nu up (4 * q + 3)).toNat := by grind
      for i in 0...mu do
        have p : (cj + i).toNat < b.size := by grind
        have p₀ : (o₀ + i).toNat < b.size := by grind
        have p₁ : (o₁ + i).toNat < b.size := by grind
        have p₂ : (o₂ + i).toNat < b.size := by grind
        have p₃ : (o₃ + i).toNat < b.size := by grind
        b[cj + i] := (((b[cj + i] - w₀ * b[o₀ + i]) - w₁ * b[o₁ + i]) - w₂ * b[o₂ + i]) -
          w₃ * b[o₃ + i]
    for t in 4 * q4...cu do
      have hkt : (subColIdxU nu up t).toNat < n := by
        rw [toNat_subColIdxU hnu up (by lia)]; exact hk _ (by lia)
      let w := A.uget ao al rfl rfl hs.1 ju (subColIdxU nu up t) (by lia) hkt
      have g := col_off_le (bo := bo) (bl := bl) hkt hb
      let ok := (bo + bl * (subColIdxU nu up t).toNat).toUSize
      have e : ok.toNat = bo + bl * (subColIdxU nu up t).toNat := by grind
      for i in 0...mu do
        have p : (cj + i).toNat < b.size := by grind
        have p' : (ok + i).toNat < b.size := by grind
        b[cj + i] := b[cj + i] - w * b[ok + i]
    let ajj := A.uget ao al rfl rfl hs.1 ju ju (by lia) (by lia)
    for i in 0...d.rows mu do
      have : i.toNat < m := Nat.lt_of_lt_of_le (by assumption) (hmu ▸ d.toNat_rows_le)
      have p : (cj + i).toNat < b.size := by grind
      b[cj + i] := b[cj + i] / ajj

public theorem trsmRightTColData_eq (d : Diag) (A : Mat n n) (up : Bool) (bo bl j cnt : Nat)
    (b : Float64Array) (hj : j < n) (hcnt : cnt ≤ n) (hk : ∀ t, t < cnt → subColIdx n up t < n)
    (hkj : ∀ t, t < cnt → subColIdx n up t ≠ j) (hml : m ≤ bl)
    (hb : bo + bl * (n - 1) + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ b.size < USize.size ∧ m < USize.size ∧ n < USize.size) :
    trsmRightTColData d A up bo bl j cnt b hj hcnt hk hb hs =
      trsmRightTColModel (m := m) d A up bo bl j cnt b := by
  have hmu : m.toUSize.toNat = m := by grind
  have hnu : n.toUSize.toNat = n := by grind
  have hju : j.toUSize.toNat = j := by grind
  have hcu : cnt.toUSize.toNat = cnt := by grind
  have hcj : bo + bl * j + m ≤ b.size := col_off_le hj hb
  have ecj : (bo + bl * j).toUSize.toNat = bo + bl * j := by grind
  have hq4 : (cnt.toUSize / 4).toNat = cnt / 4 := by simp only [USize.toNat_div, hcu]; simp
  have h4q : (4 * (cnt.toUSize / 4)).toNat = 4 * (cnt / 4) := by grind
  have hcol : ∀ t, t < cnt → ∀ i, i < m → ∀ i', i' < m →
      bo + bl * j + i ≠ bo + bl * subColIdx n up t + i' :=
    fun t ht i hi i' hi' => col_index_ne hi hi' hml (Ne.symm (hkj t ht))
  let oj := bo + bl * j
  let O := fun t => bo + bl * subColIdx n up t
  let W := fun t => A.data[A.off + A.ld * subColIdx n up t + j]!
  let P1 := fun t (c : Float64Array) =>
    c.modifyAt (Stride.mk oj 1).idx 0 m fun i v => v - W t * c[O t + i]!
  let P4 := fun q (c : Float64Array) =>
    c.modifyAt (Stride.mk oj 1).idx 0 m fun i v =>
      (((v - W (4 * q) * c[O (4 * q) + i]!) - W (4 * q + 1) * c[O (4 * q + 1) + i]!) -
        W (4 * q + 2) * c[O (4 * q + 2) + i]!) - W (4 * q + 3) * c[O (4 * q + 3) + i]!
  have hP4 : ∀ q, 4 * q + 3 < cnt → P4 q = iterRange P1 (4 * q) (4 * q + 4) := by
    intro q hq
    funext c
    have := iterRange_subCols (m := m) c oj O W (4 * q) 4
      (fun t h₁ h₂ i hi i' hi' => hcol t (by lia) i hi i' hi')
    simp only [P1] at this ⊢
    rw [this]
    apply modifyAt_congr_fun
    intro i v _ _
    simp [Nat.fold_succ]
  unfold trsmRightTColData
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := P4) (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
  · rw [Tail.run_forInFrom_unit (F := P1) (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · rw [Tail.run_forInFrom_unit (F := fun i (c : Float64Array) =>
          c.set! ((Stride.mk oj 1).idx i)
            (c[(Stride.mk oj 1).idx i]! / A.data[A.off + A.ld * j + j]!))
        (hF := fun _ _ => by simp)]
      · simp only [Tail.run_done]
        rw [USize.toNat_zero, hq4, h4q, hcu]
        have hR := d.toNat_rows_le (mu := m.toUSize)
        rw [hmu] at hR
        rw [iterRange_set!_read4 _ _ (fun _ => oj + m) (fun _ => oj + m) (fun _ => oj + m)
          (fun _ => oj + m) (fun _ v _ _ _ _ => v / A.data[A.off + A.ld * j + j]!)
          (fun i _ hi _ _ _ => by simp only [Stride.idx, oj]; refine ⟨?_, ?_, ?_, ?_⟩ <;> lia)]
        have e₄ : iterRange P4 0 (cnt / 4) b = iterRange P1 0 (4 * (cnt / 4)) b := by
          rw [← iterRange_four]
          exact iterRange_congr (fun q _ hq => hP4 q (by lia)) b
        rw [e₄, ← iterRange_split P1 (Nat.zero_le _) (by lia)]
        have hsub := iterRange_subCols (m := m) b oj O W 0 cnt
          (fun t _ h₂ i hi i' hi' => hcol t (by lia) i hi i' hi')
        simp only [Nat.zero_add] at hsub
        rw [hsub, modifyAt_rows _ _ d hmu, modifyAt_modifyAt _ _ (col_injOn _ _ _)]
        rfl
      · intro i _ hi next' a' h'
        have hi' : i.toNat < m := by
          have h1 := d.toNat_rows_le (mu := m.toUSize)
          simp only [hmu] at hi h1 ⊢; lia
        have hp : ((bo + bl * j).toUSize + i).toNat = (Stride.mk oj 1).idx i.toNat := by
          simp only [Stride.idx, Nat.one_mul, oj]; grind
        simp only [Tail.run_readThen, Tail.run_writeThen]
        apply run_set_eq_set! _ _ _ _ hp
        simp only [Mat.uget_eq_getElem, getElem_def, hju, getElem_eq_getElem!, hp]
    · intro t ht ht' next a h
      rw [h4q] at ht
      rw [hcu] at ht'
      have hkt := hk _ ht'
      have g := col_off_le (bo := bo) (bl := bl) hkt hb
      have ec : ∀ i : USize, i.toNat < m →
          ((bo + bl * j).toUSize + i).toNat = (Stride.mk oj 1).idx i.toNat := by
        intro i hi; simp only [Stride.idx, Nat.one_mul, oj]; exact toNat_off_add hcj hs.2.1 hi
      rw [Tail.run_forInFrom_unit (F := fun i (c : Float64Array) =>
          c.set! ((Stride.mk oj 1).idx i)
            (c[(Stride.mk oj 1).idx i]! - W t.toNat * c[O t.toNat + i]!))
        (hF := fun _ _ => by simp)]
      · apply run_congr
        rw [USize.toNat_zero, hmu, iterRange_set!_read _ _ (fun i => O t.toNat + i)
          (fun _ v w => v - W t.toNat * w)
          (fun i _ hi i' _ hi' e => by
            simp only [Stride.idx, Nat.one_mul, oj, O] at e
            exact hcol t.toNat ht' i hi i' hi' e)]
      · intro i _ hi next' a' h'
        rw [hmu] at hi
        simp only [Tail.run_readThen, Tail.run_writeThen]
        apply run_set_eq_set! _ _ _ _ (ec i hi)
        simp only [Mat.uget_eq_getElem, getElem_def, hju,
          toNat_subColIdxU hnu up (show t.toNat < n by lia), getElem_eq_getElem!, ec i hi, W]
        rw [toNat_off_add g hs.2.1 hi]
  · intro q _ hq next a h
    rw [hq4] at hq
    have h₀ : (4 * q).toNat = 4 * q.toNat := by grind
    have h₁ : (4 * q + 1).toNat = 4 * q.toNat + 1 := by grind
    have h₂ : (4 * q + 2).toNat = 4 * q.toNat + 2 := by grind
    have h₃ : (4 * q + 3).toNat = 4 * q.toNat + 3 := by grind
    have hk₀ := hk (4 * q.toNat) (by lia)
    have hk₁ := hk (4 * q.toNat + 1) (by lia)
    have hk₂ := hk (4 * q.toNat + 2) (by lia)
    have hk₃ := hk (4 * q.toNat + 3) (by lia)
    have g₀ := col_off_le (bo := bo) (bl := bl) hk₀ hb
    have g₁ := col_off_le (bo := bo) (bl := bl) hk₁ hb
    have g₂ := col_off_le (bo := bo) (bl := bl) hk₂ hb
    have g₃ := col_off_le (bo := bo) (bl := bl) hk₃ hb
    have s₀ : (subColIdxU n.toUSize up (4 * q)).toNat = subColIdx n up (4 * q.toNat) := by
      rw [toNat_subColIdxU hnu up (by lia), h₀]
    have s₁ : (subColIdxU n.toUSize up (4 * q + 1)).toNat = subColIdx n up (4 * q.toNat + 1) := by
      rw [toNat_subColIdxU hnu up (by lia), h₁]
    have s₂ : (subColIdxU n.toUSize up (4 * q + 2)).toNat = subColIdx n up (4 * q.toNat + 2) := by
      rw [toNat_subColIdxU hnu up (by lia), h₂]
    have s₃ : (subColIdxU n.toUSize up (4 * q + 3)).toNat = subColIdx n up (4 * q.toNat + 3) := by
      rw [toNat_subColIdxU hnu up (by lia), h₃]
    have ec : ∀ i : USize, i.toNat < m →
        ((bo + bl * j).toUSize + i).toNat = (Stride.mk oj 1).idx i.toNat := by
      intro i hi; simp only [Stride.idx, Nat.one_mul, oj]; exact toNat_off_add hcj hs.2.1 hi
    rw [Tail.run_forInFrom_unit (F := fun i (c : Float64Array) =>
        c.set! ((Stride.mk oj 1).idx i)
          ((((c[(Stride.mk oj 1).idx i]! - W (4 * q.toNat) * c[O (4 * q.toNat) + i]!) -
            W (4 * q.toNat + 1) * c[O (4 * q.toNat + 1) + i]!) -
            W (4 * q.toNat + 2) * c[O (4 * q.toNat + 2) + i]!) -
            W (4 * q.toNat + 3) * c[O (4 * q.toNat + 3) + i]!))
      (hF := fun _ _ => by simp)]
    · apply run_congr
      rw [USize.toNat_zero, hmu, iterRange_set!_read4 _ _ (fun i => O (4 * q.toNat) + i)
        (fun i => O (4 * q.toNat + 1) + i) (fun i => O (4 * q.toNat + 2) + i)
        (fun i => O (4 * q.toNat + 3) + i)
        (fun _ v x₀ x₁ x₂ x₃ => (((v - W (4 * q.toNat) * x₀) - W (4 * q.toNat + 1) * x₁) -
          W (4 * q.toNat + 2) * x₂) - W (4 * q.toNat + 3) * x₃)
        (fun i _ hi i' _ hi' => by
          simp only [Stride.idx, Nat.one_mul, oj, O]
          exact ⟨hcol _ (by lia) i hi i' hi', hcol _ (by lia) i hi i' hi',
            hcol _ (by lia) i hi i' hi', hcol _ (by lia) i hi i' hi'⟩)]
    · intro i _ hi next' a' h'
      rw [hmu] at hi
      simp only [Tail.run_readThen, Tail.run_writeThen]
      apply run_set_eq_set! _ _ _ _ (ec i hi)
      simp only [Mat.uget_eq_getElem, getElem_def, hju, s₀, s₁, s₂, s₃, getElem_eq_getElem!,
        ec i hi, W]
      rw [toNat_off_add g₀ hs.2.1 hi, toNat_off_add g₁ hs.2.1 hi, toNat_off_add g₂ hs.2.1 hi,
        toNat_off_add g₃ hs.2.1 hi]

/-! ### The column loop -/

private theorem subColIdx_lt {t : Nat} (up : Bool) (ht : t < n) : subColIdx n up t < n := by
  cases up <;> simp only [subColIdx, Bool.false_eq_true, ↓reduceIte] <;> lia

private theorem subColIdx_ne {t t' : Nat} (up : Bool) (ht : t < n) (h : t' < t) :
    subColIdx n up t' ≠ subColIdx n up t := by
  cases up <;> simp only [subColIdx, Bool.false_eq_true, ↓reduceIte] <;> lia

/--
The solve of `Z * Aᵀ = B` from step `t` on, in the array `b` of size `sz` of a matrix with offset
`bo` and leading dimension `bl`: step `t` solves column `subColIdx n up t` with the `t` columns
`subColIdx n up t'`, `t' < t`, that the steps before it solved.
-/
public def trsmRightTLoop (d : Diag) (A : Mat n n) (up : Bool) (bo bl sz : Nat) (hml : m ≤ bl)
    (hsz : bo + bl * (n - 1) + m ≤ sz)
    (hs : A.data.size < USize.size ∧ sz < USize.size ∧ m < USize.size ∧ n < USize.size)
    (t : Nat) (b : Float64Array) (hb : b.size = sz) : Float64Array :=
  if ht : t < n then
    have hb' : bo + bl * (n - 1) + m ≤ b.size := hb ▸ hsz
    have hs' : A.data.size < USize.size ∧ b.size < USize.size ∧ m < USize.size ∧
        n < USize.size := hb ▸ hs
    let c := trsmRightTColData d A up bo bl (subColIdx n up t) t b (subColIdx_lt up ht) (by lia)
      (fun _ h => subColIdx_lt up (by lia)) hb' hs'
    have hc : c.size = sz := by
      simp only [c, trsmRightTColData_eq (m := m) d A up bo bl _ t b (subColIdx_lt up ht) (by lia)
        (fun _ h => subColIdx_lt up (by lia)) (fun _ h => subColIdx_ne up ht h) hml hb' hs',
        trsmRightTColModel, size_modifyAt, hb]
    trsmRightTLoop d A up bo bl sz hml hsz hs (t + 1) c hc
  else b
termination_by n - t

private theorem trsmRightTLoop_eq (d : Diag) (A : Mat n n) (up : Bool) (bo bl sz : Nat)
    (hml : m ≤ bl)
    (hsz : bo + bl * (n - 1) + m ≤ sz)
    (hs : A.data.size < USize.size ∧ sz < USize.size ∧ m < USize.size ∧ n < USize.size)
    (t : Nat) (b : Float64Array) (hb : b.size = sz) :
    trsmRightTLoop d A up bo bl sz hml hsz hs t b hb =
      iterRange (fun t c => trsmRightTColModel (m := m) d A up bo bl (subColIdx n up t) t c)
        t n b := by
  obtain ⟨e, he⟩ : ∃ e, n - t = e := ⟨_, rfl⟩
  induction e generalizing t b with
  | zero => rw [trsmRightTLoop, dite_eq_right (by lia), iterRange_of_le _ (by lia)]
  | succ e ih =>
    rw [trsmRightTLoop, dite_eq_left (show t < n by lia), ih (t + 1) _ _ (by lia),
      iterRange_of_lt _ (show t < n by lia), trsmRightTColData_eq (m := m) d A up bo bl _ t b
        (subColIdx_lt up (by lia)) (by lia) (fun _ h => subColIdx_lt up (by lia))
        (fun _ h => subColIdx_ne up (by lia) h) hml]

/-- The array of the solve of `Z * Aᵀ = B` for the upper triangle of `A`. -/
public def trsmRightTUpperData (d : Diag) (A : Mat n n) (B : Mat m n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size ∧ m ≠ 0 ∧ n ≠ 0 then
    trsmRightTLoop d A true B.off B.ld B.data.size B.le_ld (by have := B.bound; lia)
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩ 0 B.data rfl
  else mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTUpper d A B i j

public theorem trsmRightTUpperData_eq (d : Diag) (A : Mat n n) (B : Mat m n) :
    trsmRightTUpperData d A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTUpper d A B i j := by
  unfold trsmRightTUpperData
  split
  · rw [trsmRightTLoop_eq, iterRange_congr (g := trsmRightTUpperCol d A B) (fun t _ ht => by
        funext c
        simp only [trsmRightTColModel, trsmRightTUpperCol, subColIdx, ↓reduceIte]
        apply modifyAt_congr_fun
        intro i v _ _
        congr 1
        exact Nat.fold_congr (show t = n - 1 - (n - 1 - t) by lia) _ _),
      iterRange_trsmRightTUpperCol d A B (Nat.le_refl _), Nat.sub_self]
    apply mapMat_congr_getElem
    intro i j hi _ hj hq
    rw [trsmRightTUpper_eq_G, getElem!_pos B.data _ hq]
  · rfl

/-- The array of the solve of `Z * Aᵀ = B` for the lower triangle of `A`. -/
public def trsmRightTLowerData (d : Diag) (A : Mat n n) (B : Mat m n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size ∧ m ≠ 0 ∧ n ≠ 0 then
    trsmRightTLoop d A false B.off B.ld B.data.size B.le_ld (by have := B.bound; lia)
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩ 0 B.data rfl
  else mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTLower d A B i j

public theorem trsmRightTLowerData_eq (d : Diag) (A : Mat n n) (B : Mat m n) :
    trsmRightTLowerData d A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTLower d A B i j := by
  unfold trsmRightTLowerData
  split
  · rw [trsmRightTLoop_eq, iterRange_congr (g := trsmRightTLowerCol d A B) (fun t _ ht => by
        funext c
        simp only [trsmRightTColModel, trsmRightTLowerCol, subColIdx, Bool.false_eq_true,
          ↓reduceIte]),
      iterRange_trsmRightTLowerCol d A B (Nat.le_refl _)]
    apply mapMat_congr_getElem
    intro i j hi _ hj hq
    rw [trsmRightTLower_eq_G, getElem!_pos B.data _ hq]
  · rfl

/-! ### `trsmRightT` -/

/-- The solution `Z` of `Z * Aᵀ = B` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trsmRightTSol (uplo : Uplo) (d : Diag) (A : Mat n n) (B : Mat m n) :
    Nat → Nat → Float :=
  match uplo with
  | .upper => trsmRightTUpper d A B
  | .lower => trsmRightTLower d A B

/--
The value of `trsmRightT` at `(i, j)`: `0` when `α = 0`, and `α` times the solution of
`Z * Aᵀ = B` otherwise.
-/
@[expose] public def trsmRightTAt (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) (i j : Nat) : Float :=
  if α == 0 then 0 else α * trsmRightTSol uplo d A B i j

/-- The array of the solve of `Z * Aᵀ = B`, before the scaling by `α`. -/
public def trsmRightTSolData (uplo : Uplo) (d : Diag) (A : Mat n n) (B : Mat m n) :
    Float64Array :=
  match uplo with
  | .upper => trsmRightTUpperData d A B
  | .lower => trsmRightTLowerData d A B

public theorem trsmRightTSolData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (B : Mat m n) :
    trsmRightTSolData uplo d A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTSol uplo d A B i j := by
  cases uplo
  · exact trsmRightTUpperData_eq d A B
  · exact trsmRightTLowerData_eq d A B

/--
The matrix with the array `a`, the offset `off` and the leading dimension `ld` of `B`, when `a` has
the size of `B`'s array.
-/
private def withData (B : Mat m n) (off ld : Nat) (ho : off = B.off) (hl : ld = B.ld)
    (a : Float64Array) (h : a.size = B.data.size) : Mat m n where
  data := a
  off := off
  ld := ld
  le_ld := hl ▸ B.le_ld
  bound := by rw [h, ho, hl]; exact B.bound

/--
The array of `trsmRightT`. It takes the offset and the leading dimension of `B` before the solve,
so that `B` is not used after it, and the solve updates its array in place when it is not shared.
-/
public def trsmRightTData (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n) :
    Float64Array :=
  if α == 0 then B.scalBetaData 0
  else
    let off := B.off
    let ld := B.ld
    Mat.scalBetaData α (withData B off ld rfl rfl (trsmRightTSolData uplo d A B)
      (by rw [trsmRightTSolData_eq, size_mapMat]))

public theorem trsmRightTData_eq (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) :
    trsmRightTData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTAt uplo d α A B i j := by
  unfold trsmRightTData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, scalBetaData_eq, withData, trsmRightTSolData_eq,
      mapMat_mapMat]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmRightTAt, betaMul, hα]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmRightTAt, betaMul, hα, show ((0 : Float) == 0) = true from rfl]

/--
`trsmRightT uplo d α A B` solves `X * Aᵀ = α * B` for the triangle `uplo` of `A`, with a unit
diagonal if `d` is `.unit`, over `B`, by the loops of the reference BLAS for `TRANSA = 'T'`: it
solves `Z * Aᵀ = B` column by column, from `j = n - 1` down to `0` for the upper triangle, where it
subtracts `A[j, k]` times column `k` for `k = n - 1, …, j + 1`, and from `j = 0` up to `n - 1` for
the lower triangle, with `k = 0, …, j - 1`, then divides column `j` by `A[j, j]` unless the
diagonal is unit; last, it scales `Z` by `α`. Each element gets the operations of the reference
loops, in the same order: they scale each column once it is subtracted from the others. It updates
`B` in place when its array is not shared, and leaves the elements of the array outside `B`
unchanged. As in the reference BLAS, it sets `B` to `0` without reading `A` or `B` when `α = 0`,
reads only the triangle `uplo` of `A`, and doesn't check for a zero on the diagonal.
-/
@[expose] public def trsmRightT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) : Mat m n where
  data := trsmRightTData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trsmRightTData_eq, size_mapMat]; exact B.bound

/-- The array of `trsmRightT uplo d α A B` is the array of `B` with its elements solved. -/
public theorem data_trsmRightT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) :
    (trsmRightT uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTAt uplo d α A B i j :=
  trsmRightTData_eq uplo d α A B

@[simp] public theorem off_trsmRightT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) : (trsmRightT uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trsmRightT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) : (trsmRightT uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trsmRightT uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trsmRightT (uplo : Uplo) (d : Diag) (α : Float) (A : Mat n n)
    (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRightT uplo d α A B)[(i, j)] = trsmRightTAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trsmRightT uplo d α A B) rfl rfl i j h

/--
Element `(i, j)` of `trsmRightT .upper d α A B` is `0` when `α = 0`, and otherwise `α * Z[i, j]`
for the solution `Z = trsmRightTUpper d A B` of `Z * Aᵀ = B`, which `trsmRightTUpper_eq` states.
-/
public theorem getElem_trsmRightT_upper (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRightT .upper d α A B)[(i, j)] =
      if α == 0 then 0 else α * trsmRightTUpper d A B i j :=
  getElem_trsmRightT _ _ _ _ _ _ _ h

/--
Element `(i, j)` of `trsmRightT .lower d α A B` is `0` when `α = 0`, and otherwise `α * Z[i, j]`
for the solution `Z = trsmRightTLower d A B` of `Z * Aᵀ = B`, which `trsmRightTLower_eq` states.
-/
public theorem getElem_trsmRightT_lower (d : Diag) (α : Float) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRightT .lower d α A B)[(i, j)] =
      if α == 0 then 0 else α * trsmRightTLower d A B i j :=
  getElem_trsmRightT _ _ _ _ _ _ _ h

end Mat

end BLAS.Float64
