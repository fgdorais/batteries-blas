/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float32.Gemm
public import BatteriesBLAS.Float32.Level2
import all BatteriesBLAS.Internal

/-!
# Transposed `gemm`

The three other forms of the reference BLAS `gemm`, by its loops for each form:

* `Mat.gemmTN α A B β C` is `α * Aᵀ * B + β * C`: for each element, a sum of products of a column
  of `A` and a column of `B`, by the loops of `gemvT`.
* `Mat.gemmNT α A B β C` is `α * A * Bᵀ + β * C`: the loops of `gemm` on `Bᵀ`.
* `Mat.gemmTT α A B β C` is `α * Aᵀ * Bᵀ + β * C`: the loops of `gemmTN` on `Bᵀ`.

`gemmNT` and `gemmTT` first copy `B` into `Mat.transpose B`, which takes `k * n` steps against
the `2 * m * n * k` floating-point operations of the product, then run the kernels of `gemm` and
`gemmTN`. Each element gets the operations of the reference BLAS, in its order, since the loops for
`B` and for `Bᵀ` only differ in where they read the elements of `B`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {m n k : Nat}

/-! ## Transpose -/

/-- The value of the transpose of `A` at `(j, i)`: `A[i, j]`, and `0` outside `A`. -/
@[expose] public def transposeAt (A : Mat m n) (j i : Nat) (_ : Float32) : Float32 :=
  if h : i < m ∧ j < n then A[(i, j)] else 0

/--
The array of `transpose A`, packed: for each row `i` of `A`, it copies the row into column `i` of
the transpose.
-/
public def transposeData (A : Mat m n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ n * m < USize.size ∧ m < USize.size ∧ n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let t := replicate (n * m) 0
    have ht : t.size = n * m := by simp [t]
    inplace t do
      for i in 0...mu do
        let ti := nu * i
        have hti : ti.toNat + nu.toNat ≤ t.size :=
          toNat_mul_add_le (n := m) (by lia) (by rw [hnu, ht]; exact Nat.le_refl _)
        for j in 0...nu do
          t[ti + j] := A.uget ao al rfl rfl hs.1 i j (by lia) (by lia)
  else mapMat (replicate (n * m) 0) 0 n n 0 m (transposeAt A)

public theorem transposeData_eq (A : Mat m n) :
    transposeData A = mapMat (replicate (n * m) 0) 0 n n 0 m (transposeAt A) := by
  unfold transposeData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun i c =>
      c.modifyAt (Stride.mk (0 + n * i) 1).idx 0 n fun j v => transposeAt A j i v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hmu]
      rw [iterRange_cols _ _ _ (Nat.le_refl n)]
    · intro i _ hi next a h
      rw [hmu] at hi
      rw [Tail.run_forInFrom_write (G := fun j => transposeAt A j i.toNat 0)
        (idx := (Stride.mk (0 + n * i.toNat) 1).idx)
        (he := fun j _ hj => by
          rw [toNat_mul_add_eq hnu hi (by lia) hs.2.1]
          simp [Stride.idx])]
      · simp only [USize.toNat_zero, hnu]
        rfl
      · intro j _ hj
        rw [hnu] at hj
        simp [transposeAt, hi, hj]
  · rfl

/-- The transpose of `A`, as a packed copy. -/
public def transpose (A : Mat m n) : Mat n m where
  data := transposeData A
  off := 0
  ld := n
  le_ld := Nat.le_refl _
  bound := by
    rw [transposeData_eq, size_mapMat, size_replicate]
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      rw [Nat.zero_add, ← Nat.mul_succ]
      exact Nat.le_of_eq (by congr 1; lia)

@[simp] public theorem getElem_transpose (A : Mat m n) (i j : Nat) (h : i < n ∧ j < m) :
    A.transpose[(i, j)] = A[(j, i)]'⟨h.2, h.1⟩ := by
  have hq : 0 + n * j + i < (replicate (n * m) 0).size := by
    have := PMat.index_lt h.1 h.2
    simp only [size_replicate]; lia
  simp only [getElem_def, transpose]
  rw [← getElem!_pos, transposeData_eq, getElem!_pos _ _ (by simpa using hq),
    getElem_mapMat_index _ _ _ _ _ _ _ h.1 (Nat.le_refl n) ⟨Nat.zero_le _, h.2⟩ hq]
  simp [transposeAt, h.1, h.2, getElem_def]

/-! ## `gemmNT` -/

/--
The value of `gemmNT α A B β C` at `(i, j)`: `betaMul β C[i, j]` when `α = 0`, and otherwise
`betaMul β C[i, j]`, plus the terms `α * B[j, l] * A[i, l]` for `l = 0, …, k - 1`, added from the
left, in the order of the reference BLAS.
-/
@[expose] public def gemmNTEntry (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) (i j : Nat) (hi : i < m) (hj : j < n) : Float32 :=
  if α == 0 then betaMul β C[(i, j)]
  else Nat.fold k (fun l hl s => s + α * B[(j, l)] * A[(i, l)]) (betaMul β C[(i, j)])

/-- `gemmNTEntry` at every element of a matrix, and the old value elsewhere. -/
@[expose] public def gemmNTAt (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) (i j : Nat) (v : Float32) : Float32 :=
  if h : i < m ∧ j < n then gemmNTEntry α A B β C i j h.1 h.2 else v

theorem gemmAt_transpose (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32) (C : Mat m n) :
    gemmAt α A B.transpose β C = gemmNTAt α A B β C := by
  funext i j v
  simp only [gemmAt, gemmNTAt, gemmEntry, gemmSumEntry, gemmNTEntry, getElem_transpose]

/--
`gemmNT α A B β C` is `α * A * Bᵀ + β * C`, over `C`, by the loops of `gemm` on a transposed copy
of `B`. Each element gets the operations of the loops of the reference BLAS, in the same order. It
updates `C` in place when `C` is packed and its array is not shared. It leaves the elements of
`C`'s array outside `C` unchanged. As in the reference BLAS, it sets `C` to `0` without reading it
when `β = 0`, before adding the products, and only scales `C` when `α = 0`, without reading `A` or
`B`.
-/
@[expose] public def gemmNT (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) : Mat m n :=
  if α == 0 then
    { data := C.scalBetaData β
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalBetaData_eq, size_mapMat]; exact C.bound }
  else gemm α A B.transpose β C

/-- The array of `gemmNT α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemmNT (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32) (C : Mat m n) :
    (gemmNT α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmNTAt α A B β C) := by
  rw [← gemmAt_transpose]
  unfold gemmNT
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, data_gemm]
  · simp only [↓reduceIte, scalBetaData_eq]
    exact mapMat_congr_getElem _ _ _ _ _ _ fun i j hi _ hj _ => by
      simp [gemmAt, gemmEntry, hi, hj, hα, getElem_def]

@[simp] public theorem off_gemmNT (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) : (gemmNT α A B β C).off = C.off := by
  unfold gemmNT; split <;> simp

@[simp] public theorem ld_gemmNT (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) : (gemmNT α A B β C).ld = C.ld := by
  unfold gemmNT; split <;> simp

@[simp] public theorem getElem_gemmNT (α : Float32) (A : Mat m k) (B : Mat n k) (β : Float32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmNT α A B β C)[(i, j)] = gemmNTEntry α A B β C i j h.1 h.2 := by
  rw [getElem_of_data_eq_mapMat _ (data_gemmNT α A B β C) (off_gemmNT α A B β C)
    (ld_gemmNT α A B β C) i j h]
  simp [gemmNTAt, h.1, h.2]

/-! ## `gemmTN` -/

/-- The sum of the products `A[l, i] * B[l, j]` for `l = 0, …, k - 1`, from the left. -/
@[expose] public def gemmTSum (A : Mat k m) (B : Mat k n) (i j : Nat) : Float32 :=
  Nat.fold k (fun l _ s => s + A.data[A.off + A.ld * i + l]! * B.data[B.off + B.ld * j + l]!) 0

/--
The value of the loops of `gemmTN` at an element, from the sum `t` of its products and its old
value `v`: `α * t` when `β = 0`, without reading `v`, and `α * t + β * v` otherwise.
-/
@[inline, expose] public def gemmTVal (α β t v : Float32) : Float32 :=
  if β == 0 then α * t else α * t + β * v

/-- The value of the loops of `gemmTN` at `(i, j)`, from the old value `v`. -/
@[expose] public def gemmTSumAt (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  gemmTVal α β (gemmTSum A B i j) v

/-- Column `j` of `A`, as a vector, with no copy. -/
def colVec (A : Mat k n) (j : Nat) (hj : j < n) : Vec k where
  data := A.data
  off := A.off + A.ld * j
  inc := 1
  inc_pos := Or.inl Nat.one_pos
  bound := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inl h
    · exact Or.inr (by have := A.col_le h hj; lia)

/-- The sums of `A` with `colVec B j` are those of `gemmTN`. -/
private theorem gemvTSum_colVec (A : Mat k m) (B : Mat k n) (j : Nat) (hj : j < n) (i : Nat) :
    gemvTSum A (colVec B j hj) i = gemmTSum A B i j := by
  simp only [gemvTSum, gemmTSum, colVec, Nat.one_mul]

/--
The sums `gemmTSum A B i j` for the rows `i < m` of column `j`: the sums of column `j` of `B` with
the columns of `A`, four at a time, by the loops of `gemvT`.
-/
def gemmTSums (A : Mat k m) (B : Mat k n) (hs : A.data.size < USize.size ∧
    B.data.size < USize.size) (hm : m < USize.size) (hk : k < USize.size) (j : Nat)
    (hj : j < n) : Float32Array :=
  gemvTSums A (colVec B j hj) _ _ _ _ rfl rfl rfl rfl hs hm k.toUSize (by grind) m.toUSize
    (by grind) 0 (by simp) (Float32Array.emptyWithCapacity m)

theorem gemmTSums_spec (A : Mat k m) (B : Mat k n) (hs : A.data.size < USize.size ∧
    B.data.size < USize.size) (hm : m < USize.size) (hk : k < USize.size) (j : Nat)
    (hj : j < n) :
    (gemmTSums A B hs hm hk j hj).size = m ∧
      ∀ i (h : i < (gemmTSums A B hs hm hk j hj).size),
        (gemmTSums A B hs hm hk j hj)[i] = gemmTSum A B i j := by
  have := gemvTSums_spec A (colVec B j hj) _ _ _ _ rfl rfl rfl rfl hs hm k.toUSize (by grind)
    m.toUSize (by grind) 0 (by simp) (Float32Array.emptyWithCapacity m) (by simp) (by simp)
  refine ⟨this.1, fun i h => ?_⟩
  rw [← gemvTSum_colVec A B j hj]
  exact this.2 i h

/-! ### Two columns at a time -/

/-- The sum of the first `q` products of `gemmTSum A B i j`, from the left. -/
def gemmTPart (A : Mat k m) (B : Mat k n) (i j q : Nat) : Float32 :=
  Nat.fold q (fun l _ s => s + A.data[A.off + A.ld * i + l]! * B.data[B.off + B.ld * j + l]!) 0

/-- A product of the sums, on `USize` indices, is the product of `gemmTSum`. -/
private theorem gemmT_step (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (l i j : USize) (hl' : l.toNat < k) (hi : i.toNat < m) (hj : j.toNat < n) :
    A.uget ao al ha hl hs.1 l i hl' hi * B.uget bo bl hb hbl hs.2 l j hl' hj =
      A.data[A.off + A.ld * i.toNat + l.toNat]! * B.data[B.off + B.ld * j.toNat + l.toNat]! := by
  rw [Mat.uget_eq_getElem, Mat.uget_eq_getElem, getElem!_pos A.data _ (A.index_lt hl' hi),
    getElem!_pos B.data _ (B.index_lt hl' hj)]
  rfl

/--
The loop of `gemmTSums2` for the rows `i` to `i + 3` of the columns `j` and `j + 1`, from the term
`l`, up to the bound `ku`, which is `k`: the eight sums so far, `s₀` to `s₃` for column `j` and `t₀`
to `t₃` for column `j + 1`. At the end, it pushes them onto `acc₀` and `acc₁`. The eight sums are
independent, so that their additions overlap, and they share the reads of `A` and `B`.
-/
public def gemmTSums42 (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (hm : m < USize.size) (hn : n < USize.size) (ku : USize) (hku : ku.toNat = k) (i j : USize)
    (hi : i.toNat + 3 < m) (hj : j.toNat + 1 < n) (acc₀ acc₁ : Float32Array) (l : USize)
    (s₀ s₁ s₂ s₃ t₀ t₁ t₂ t₃ : Float32) : Float32Array × Float32Array :=
  if hlk : l < ku then
    have hl' : l.toNat < k := hku ▸ hlk
    have i₁ : (i + 1).toNat < m := by grind
    have i₂ : (i + 2).toNat < m := by grind
    have i₃ : (i + 3).toNat < m := by grind
    have j₁ : (j + 1).toNat < n := by grind
    let y₀ := B.uget bo bl hb hbl hs.2 l j hl' (by lia)
    let y₁ := B.uget bo bl hb hbl hs.2 l (j + 1) hl' j₁
    let x₀ := A.uget ao al ha hl hs.1 l i hl' (by lia)
    let x₁ := A.uget ao al ha hl hs.1 l (i + 1) hl' i₁
    let x₂ := A.uget ao al ha hl hs.1 l (i + 2) hl' i₂
    let x₃ := A.uget ao al ha hl hs.1 l (i + 3) hl' i₃
    gemmTSums42 A B ao al bo bl ha hl hb hbl hs hm hn ku hku i j hi hj acc₀ acc₁ (l + 1)
      (s₀ + x₀ * y₀) (s₁ + x₁ * y₀) (s₂ + x₂ * y₀) (s₃ + x₃ * y₀)
      (t₀ + x₀ * y₁) (t₁ + x₁ * y₁) (t₂ + x₂ * y₁) (t₃ + x₃ * y₁)
  else ((((acc₀.push s₀).push s₁).push s₂).push s₃, (((acc₁.push t₀).push t₁).push t₂).push t₃)
termination_by ku.toNat - l.toNat
decreasing_by grind

private theorem gemmTSums42_eq (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (hm : m < USize.size) (hn : n < USize.size) (ku : USize) (hku : ku.toNat = k) (i j : USize)
    (hi : i.toNat + 3 < m) (hj : j.toNat + 1 < n) (acc₀ acc₁ : Float32Array) (l : USize)
    (q : Nat) (hq : l.toNat = q) (hqk : q ≤ k) :
    gemmTSums42 A B ao al bo bl ha hl hb hbl hs hm hn ku hku i j hi hj acc₀ acc₁ l
      (gemmTPart A B i.toNat j.toNat q) (gemmTPart A B (i.toNat + 1) j.toNat q)
      (gemmTPart A B (i.toNat + 2) j.toNat q) (gemmTPart A B (i.toNat + 3) j.toNat q)
      (gemmTPart A B i.toNat (j.toNat + 1) q) (gemmTPart A B (i.toNat + 1) (j.toNat + 1) q)
      (gemmTPart A B (i.toNat + 2) (j.toNat + 1) q)
      (gemmTPart A B (i.toNat + 3) (j.toNat + 1) q) =
      ((((acc₀.push (gemmTSum A B i.toNat j.toNat)).push (gemmTSum A B (i.toNat + 1) j.toNat)).push
        (gemmTSum A B (i.toNat + 2) j.toNat)).push (gemmTSum A B (i.toNat + 3) j.toNat),
      (((acc₁.push (gemmTSum A B i.toNat (j.toNat + 1))).push
        (gemmTSum A B (i.toNat + 1) (j.toNat + 1))).push
        (gemmTSum A B (i.toNat + 2) (j.toNat + 1))).push
        (gemmTSum A B (i.toNat + 3) (j.toNat + 1))) := by
  have i₁ : (i + 1).toNat = i.toNat + 1 := by grind
  have i₂ : (i + 2).toNat = i.toNat + 2 := by grind
  have i₃ : (i + 3).toNat = i.toNat + 3 := by grind
  have j₁ : (j + 1).toNat = j.toNat + 1 := by grind
  obtain ⟨d, hd⟩ : ∃ d, k - q = d := ⟨_, rfl⟩
  induction d generalizing l q with
  | zero =>
    rw [gemmTSums42, dite_eq_right_of_eq_false (eq_false (by rw [USize.lt_iff_toNat_lt]; lia))]
    obtain rfl : q = k := by lia
    rfl
  | succ d ih =>
    have hlk : l < ku := USize.lt_iff_toNat_lt.mpr (by lia)
    have hl' : l.toNat < k := by lia
    have hsucc : (l + 1).toNat = q + 1 := by clear ih; grind
    rw [gemmTSums42, dite_eq_left_of_eq_true (eq_true hlk)]
    simp only []
    simp only [gemmT_step A B ao al bo bl ha hl hb hbl hs, i₁, i₂, i₃, j₁]
    have := ih (l + 1) (q + 1) hsucc (by lia) (by lia)
    simp only [gemmTPart, Nat.fold_succ] at this
    subst hq
    exact this

/-- The loop of `gemmTSums2` for the row `i` alone: the sums `s` and `t` so far. -/
public def gemmTSums12 (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (hn : n < USize.size) (ku : USize) (hku : ku.toNat = k) (i j : USize)
    (hi : i.toNat < m) (hj : j.toNat + 1 < n) (l : USize) (s t : Float32) : Float32 × Float32 :=
  if hlk : l < ku then
    have hl' : l.toNat < k := hku ▸ hlk
    have j₁ : (j + 1).toNat < n := by grind
    let x := A.uget ao al ha hl hs.1 l i hl' hi
    gemmTSums12 A B ao al bo bl ha hl hb hbl hs hn ku hku i j hi hj (l + 1)
      (s + x * B.uget bo bl hb hbl hs.2 l j hl' (by lia))
      (t + x * B.uget bo bl hb hbl hs.2 l (j + 1) hl' j₁)
  else (s, t)
termination_by ku.toNat - l.toNat
decreasing_by grind

private theorem gemmTSums12_eq (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (hn : n < USize.size) (ku : USize) (hku : ku.toNat = k) (i j : USize)
    (hi : i.toNat < m) (hj : j.toNat + 1 < n) (l : USize) (q : Nat) (hq : l.toNat = q)
    (hqk : q ≤ k) :
    gemmTSums12 A B ao al bo bl ha hl hb hbl hs hn ku hku i j hi hj l
      (gemmTPart A B i.toNat j.toNat q) (gemmTPart A B i.toNat (j.toNat + 1) q) =
      (gemmTSum A B i.toNat j.toNat, gemmTSum A B i.toNat (j.toNat + 1)) := by
  have j₁ : (j + 1).toNat = j.toNat + 1 := by grind
  obtain ⟨d, hd⟩ : ∃ d, k - q = d := ⟨_, rfl⟩
  induction d generalizing l q with
  | zero =>
    rw [gemmTSums12, dite_eq_right_of_eq_false (eq_false (by rw [USize.lt_iff_toNat_lt]; lia))]
    obtain rfl : q = k := by lia
    rfl
  | succ d ih =>
    have hlk : l < ku := USize.lt_iff_toNat_lt.mpr (by lia)
    have hsucc : (l + 1).toNat = q + 1 := by clear ih; grind
    rw [gemmTSums12, dite_eq_left_of_eq_true (eq_true hlk)]
    simp only []
    simp only [gemmT_step A B ao al bo bl ha hl hb hbl hs, j₁]
    have := ih (l + 1) (q + 1) hsucc (by lia) (by lia)
    simp only [gemmTPart, Nat.fold_succ] at this
    subst hq
    exact this

/--
The sums `gemmTSum A B i j` and `gemmTSum A B i (j + 1)` for the rows `i` and up, pushed onto
`acc₀` and `acc₁`: four rows at a time by `gemmTSums42`, then one at a time by `gemmTSums12`.
-/
public def gemmTSums2 (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (hm : m < USize.size) (hn : n < USize.size) (ku : USize) (hku : ku.toNat = k) (mu : USize)
    (hmu : mu.toNat = m) (j : USize) (hj : j.toNat + 1 < n) (i : USize) (hi : i.toNat ≤ m)
    (acc₀ acc₁ : Float32Array) : Float32Array × Float32Array :=
  if h4 : 4 ≤ mu - i then
    have h4' : i.toNat + 3 < m := by grind
    let p := gemmTSums42 A B ao al bo bl ha hl hb hbl hs hm hn ku hku i j h4' hj acc₀ acc₁ 0
      0 0 0 0 0 0 0 0
    gemmTSums2 A B ao al bo bl ha hl hb hbl hs hm hn ku hku mu hmu j hj (i + 4) (by grind) p.1 p.2
  else if h1 : i < mu then
    have h1' : i.toNat < m := by grind
    let p := gemmTSums12 A B ao al bo bl ha hl hb hbl hs hn ku hku i j h1' hj 0 0 0
    gemmTSums2 A B ao al bo bl ha hl hb hbl hs hm hn ku hku mu hmu j hj (i + 1) (by grind)
      (acc₀.push p.1) (acc₁.push p.2)
  else (acc₀, acc₁)
termination_by m - i.toNat
decreasing_by all_goals grind

/-- The array `a` holds the sums `gemmTSum A B r j` of the rows `r < q`. -/
def SumsOf (A : Mat k m) (B : Mat k n) (j : Nat) (a : Float32Array) (q : Nat) : Prop :=
  a.size = q ∧ ∀ r (h : r < a.size), a[r] = gemmTSum A B r j

private theorem SumsOf.push {A : Mat k m} {B : Mat k n} {j : Nat} {a : Float32Array} {q : Nat}
    (h : SumsOf A B j a q) : SumsOf A B j (a.push (gemmTSum A B q j)) (q + 1) := by
  refine ⟨by simp [h.1], fun r hr => ?_⟩
  simp only [getElem_push]
  split
  · exact h.2 r _
  · have : r = q := by simp only [size_push] at hr; have := h.1; lia
    subst this; rfl

private theorem gemmTSums2_spec (A : Mat k m) (B : Mat k n) (ao al bo bl : USize)
    (ha : A.off.toUSize = ao) (hl : A.ld.toUSize = al) (hb : B.off.toUSize = bo)
    (hbl : B.ld.toUSize = bl) (hs : A.data.size < USize.size ∧ B.data.size < USize.size)
    (hm : m < USize.size) (hn : n < USize.size) (ku : USize) (hku : ku.toNat = k) (mu : USize)
    (hmu : mu.toNat = m) (j : USize) (hj : j.toNat + 1 < n) (i : USize) (hi : i.toNat ≤ m)
    (acc₀ acc₁ : Float32Array) (h₀ : SumsOf A B j.toNat acc₀ i.toNat)
    (h₁ : SumsOf A B (j.toNat + 1) acc₁ i.toNat) :
    SumsOf A B j.toNat
        (gemmTSums2 A B ao al bo bl ha hl hb hbl hs hm hn ku hku mu hmu j hj i hi acc₀ acc₁).1 m ∧
      SumsOf A B (j.toNat + 1)
        (gemmTSums2 A B ao al bo bl ha hl hb hbl hs hm hn ku hku mu hmu j hj i hi acc₀ acc₁).2
        m := by
  obtain ⟨d, hd⟩ : ∃ d, m - i.toNat = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing i acc₀ acc₁ with
  | ind d ih =>
    rw [gemmTSums2]
    split
    · rename_i h4
      have h4' : i.toNat + 3 < m := by grind
      have hi4 : (i + 4).toNat = i.toNat + 4 := by grind
      have e := gemmTSums42_eq A B ao al bo bl ha hl hb hbl hs hm hn ku hku i j h4' hj acc₀ acc₁ 0
        0 (by simp) (by lia)
      simp only [gemmTPart, Nat.fold_zero] at e
      refine ih (m - (i + 4).toNat) (by lia) (i + 4) _ _ _ ?_ ?_ rfl
      · rw [e, hi4]; exact h₀.push.push.push.push
      · rw [e, hi4]; exact h₁.push.push.push.push
    · split
      · rename_i h4 h1
        have h1' : i.toNat < m := by grind
        have hi1 : (i + 1).toNat = i.toNat + 1 := by grind
        have e := gemmTSums12_eq A B ao al bo bl ha hl hb hbl hs hn ku hku i j h1' hj 0 0 (by simp)
          (Nat.zero_le _)
        simp only [gemmTPart, Nat.fold_zero] at e
        refine ih (m - (i + 1).toNat) (by lia) (i + 1) _ _ _ ?_ ?_ rfl
        · rw [e, hi1]; exact h₀.push
        · rw [e, hi1]; exact h₁.push
      · rename_i h4 h1
        have : i.toNat = m := by grind
        rw [this] at h₀ h₁
        exact ⟨h₀, h₁⟩

/-- The sums `gemmTSum A B i j` and `gemmTSum A B i (j + 1)` of the rows `i < m`, by `gemmTSums2`. -/
def gemmTNSums2 (A : Mat k m) (B : Mat k n) (hs : A.data.size < USize.size ∧
    B.data.size < USize.size) (hm : m < USize.size) (hn : n < USize.size) (hk : k < USize.size)
    (j : Nat) (hj : j + 1 < n) : Float32Array × Float32Array :=
  gemmTSums2 A B _ _ _ _ rfl rfl rfl rfl hs hm hn k.toUSize (by grind) m.toUSize (by grind)
    j.toUSize (by grind) 0 (by simp) (.emptyWithCapacity m) (.emptyWithCapacity m)

theorem gemmTNSums2_spec (A : Mat k m) (B : Mat k n) (hs : A.data.size < USize.size ∧
    B.data.size < USize.size) (hm : m < USize.size) (hn : n < USize.size) (hk : k < USize.size)
    (j : Nat) (hj : j + 1 < n) :
    SumsOf A B j (gemmTNSums2 A B hs hm hn hk j hj).1 m ∧
      SumsOf A B (j + 1) (gemmTNSums2 A B hs hm hn hk j hj).2 m := by
  have hju : j.toUSize.toNat = j := by grind
  have := gemmTSums2_spec A B _ _ _ _ rfl rfl rfl rfl hs hm hn k.toUSize (by grind) m.toUSize
    (by grind) j.toUSize (by grind) 0 (by simp) (.emptyWithCapacity m) (.emptyWithCapacity m)
    ⟨by simp, fun r h => by simp at h⟩ ⟨by simp, fun r h => by simp at h⟩
  rw [hju] at this
  exact this

/-- Column `j` of `gemmTN`, at the index `o` of the array `b`. -/
@[expose] public def gemmTNCol (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (o j : Nat)
    (b : Float32Array) : Float32Array :=
  b.modifyAt (fun i => o + i) 0 m fun i v => gemmTSumAt α A B β i j v

/-- Steps that each write `G i c[idx i]!` at `idx i` are a `modifyAt`. -/
private theorem iterRange_set!_self (a : Float32Array) (idx : Nat → Nat)
    (G : Nat → Float32 → Float32) {lo hi : Nat} :
    iterRange (fun i c => c.set! (idx i) (G i c[idx i]!)) lo hi a = a.modifyAt idx lo hi G := by
  obtain ⟨d, hd'⟩ : ∃ d, hi - lo = d := ⟨_, rfl⟩
  induction d generalizing lo a with
  | zero => rw [iterRange_of_le _ (by lia), modifyAt_of_le _ _ (by lia)]
  | succ d ih =>
    rw [iterRange_of_lt _ (by lia), modifyAt_of_lt _ _ (by lia), ih _ (by lia)]

/--
The columns `j` and `j + 1` of `gemmTN`, at the indices `o₀` and `o₁` of the array `b`: the sums of
the two columns by `gemmTSums2`, which shares the reads of `A` between them, then a pass over the
two columns. Each element gets the operations of `gemmTNCol`, in the same order.
-/
public def gemmTN2Data (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (j : Nat)
    (hj : j + 1 < n) (o₀ o₁ : Nat) (b : Float32Array) (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ b.size < USize.size ∧
      m < USize.size ∧ n < USize.size ∧ k < USize.size) : Float32Array :=
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  let c₀ := o₀.toUSize
  have e₀ : c₀.toNat = o₀ := by grind
  let c₁ := o₁.toUSize
  have e₁ : c₁.toNat = o₁ := by grind
  let p := gemmTNSums2 A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 j hj
  let s₀ := p.1
  let s₁ := p.2
  inplace b do
    for i in 0...mu do
      have q₀ : (c₀ + i).toNat < b.size := by grind
      have q₁ : (c₁ + i).toNat < b.size := by grind
      let v₀ := b[c₀ + i]
      let v₁ := b[c₁ + i]
      b[c₀ + i] := gemmTVal α β s₀[i.toNat]! v₀
      b[c₁ + i] := gemmTVal α β s₁[i.toNat]! v₁

public theorem gemmTN2Data_eq (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (j : Nat)
    (hj : j + 1 < n) (o₀ o₁ : Nat) (b : Float32Array) (h₁ : o₀ + m ≤ o₁) (h₂ : o₁ + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ b.size < USize.size ∧
      m < USize.size ∧ n < USize.size ∧ k < USize.size) :
    gemmTN2Data α A B β j hj o₀ o₁ b h₁ h₂ hs =
      gemmTNCol α A B β o₁ (j + 1) (gemmTNCol α A B β o₀ j b) := by
  have hmu : m.toUSize.toNat = m := by grind
  have e₀ : o₀.toUSize.toNat = o₀ := by grind
  have e₁ : o₁.toUSize.toNat = o₁ := by grind
  have hsp := gemmTNSums2_spec A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 j hj
  unfold gemmTN2Data
  generalize gemmTNSums2 A B _ _ _ _ j hj = p at hsp
  obtain ⟨⟨hp₀, hv₀⟩, ⟨hp₁, hv₁⟩⟩ := hsp
  let G₀ := fun i v => gemmTSumAt α A B β i j v
  let G₁ := fun i v => gemmTSumAt α A B β i (j + 1) v
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit (F := fun i c => (fun c => c.set! (o₁ + i) (G₁ i c[o₁ + i]!))
      ((fun c => c.set! (o₀ + i) (G₀ i c[o₀ + i]!)) c))
    (hF := fun _ _ => by simp)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
    rw [iterRange_comp_of_local (U := colIdx o₁ m) (V := colIdx o₀ m)
      (F := fun i c => c.set! (o₁ + i) (G₁ i c[o₁ + i]!))
      (G := fun i c => c.set! (o₀ + i) (G₀ i c[o₀ + i]!))
      (fun i hi => local_set! (o₁ + i) (by simp only [colIdx]; lia) (fun c => G₁ i c[o₁ + i]!)
        fun b b' _ hb => by rw [hb _ (by simp only [colIdx]; lia)])
      (fun i hi => local_set! (o₀ + i) (by simp only [colIdx]; lia) (fun c => G₀ i c[o₀ + i]!)
        fun b b' _ hb => by rw [hb _ (by simp only [colIdx]; lia)])
      (fun p h h' => by simp only [colIdx] at h h'; lia),
      iterRange_set!_self, iterRange_set!_self]
    rfl
  · intro i _ hi next a h
    rw [hmu] at hi
    have t₀ : (o₀.toUSize + i).toNat = o₀ + i.toNat := by grind
    have t₁ : (o₁.toUSize + i).toNat = o₁ + i.toNat := by grind
    simp only [Tail.run_readThen, Tail.run_writeThen]
    apply run_congr
    simp only [t₀, t₁, set_eq_set!, getElem_eq_getElem!]
    rw [getElem!_set!_ne _ _ (show o₀ + i.toNat ≠ o₁ + i.toNat by lia),
      getElem!_pos p.1 _ (by rw [hp₀]; exact hi), getElem!_pos p.2 _ (by rw [hp₁]; exact hi),
      hv₀, hv₁]
    rfl

/-- Column `j` of `gemmTN`, at the index `o` of the array `b`, by the sums of `gemmTSums`. -/
public def gemmTN1Data (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (j : Nat)
    (hj : j < n) (o : Nat) (b : Float32Array) (h : o + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ b.size < USize.size ∧
      m < USize.size ∧ n < USize.size ∧ k < USize.size) : Float32Array :=
  let mu := m.toUSize
  have hmu : mu.toNat = m := by grind
  let c := o.toUSize
  have e : c.toNat = o := by grind
  let sums := gemmTSums A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.1 hs.2.2.2.2.2 j hj
  inplace b do
    for i in 0...mu do
      have q : (c + i).toNat < b.size := by grind
      b[c + i] := gemmTVal α β sums[i.toNat]! b[c + i]

public theorem gemmTN1Data_eq (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (j : Nat)
    (hj : j < n) (o : Nat) (b : Float32Array) (h : o + m ≤ b.size)
    (hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ b.size < USize.size ∧
      m < USize.size ∧ n < USize.size ∧ k < USize.size) :
    gemmTN1Data α A B β j hj o b h hs = gemmTNCol α A B β o j b := by
  have hmu : m.toUSize.toNat = m := by grind
  have e : o.toUSize.toNat = o := by grind
  have hsp := gemmTSums_spec A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.1 hs.2.2.2.2.2 j hj
  unfold gemmTN1Data
  generalize gemmTSums A B _ _ _ j hj = sums at hsp
  obtain ⟨hp, hv⟩ := hsp
  simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
  rw [Tail.run_forInFrom_unit
    (F := fun i c => c.set! (o + i) (gemmTSumAt α A B β i j c[o + i]!)) (hF := fun _ _ => by simp)]
  · simp only [Tail.run_done, USize.toNat_zero, hmu]
    rw [iterRange_set!_self]
    rfl
  · intro i _ hi next a h
    rw [hmu] at hi
    have t : (o.toUSize + i).toNat = o + i.toNat := by grind
    simp only [Tail.run_readThen, Tail.run_writeThen]
    apply run_congr
    simp only [t, set_eq_set!, getElem_eq_getElem!]
    rw [getElem!_pos sums _ (by rw [hp]; exact hi), hv]
    rfl

@[simp] private theorem size_gemmTNCol (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32)
    (o j : Nat) (b : Float32Array) : (gemmTNCol α A B β o j b).size = b.size := by
  simp [gemmTNCol]

private theorem toNat_col_base (C : Mat m n) (hs : C.data.size < USize.size) (hm : 0 < m)
    {j : Nat} (hj : j < n) (hju : j < USize.size) :
    (C.off.toUSize + C.ld.toUSize * j.toUSize).toNat = C.off + C.ld * j := by
  have := C.col_le hm hj
  have hj' : j.toUSize.toNat = j := by grind
  have := C.toNat_index hs (i := 0) (j := j.toUSize) hm (by rw [hj']; exact hj)
  grind

private theorem col_add_le' {off ld j : Nat} (hml : m ≤ ld) :
    off + ld * j + m ≤ off + ld * (j + 1) := by
  rw [Nat.mul_succ]; lia

/-- The conditions of the kernels of `gemmTN`. -/
public abbrev GemmTFits (A : Mat k m) (B : Mat k n) (C : Mat m n) : Prop :=
  A.data.size < USize.size ∧ B.data.size < USize.size ∧ C.data.size < USize.size ∧
    m < USize.size ∧ n < USize.size ∧ k < USize.size ∧ 0 < m

/--
The columns `j` and up of `gemmTN`, in the array `c` of `C`: two at a time by `gemmTN2Data`, and the
last one by `gemmTN1Data` when there is one left. It takes the offset and the leading dimension of
`C` as `USize`s rather than reading them from `C`, so that the array isn't shared, and the column
functions update it in place.
-/
public def gemmTNCols (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n)
    (hs : GemmTFits A B C) (co cl : USize) (hco : C.off.toUSize = co)
    (hcl : C.ld.toUSize = cl) (j : Nat) (c : Float32Array) (hc : c.size = C.data.size) :
    Float32Array :=
  if h2 : j + 2 ≤ n then
    let o := fun r => (co + cl * (j + r).toUSize).toNat
    have ho : ∀ r, j + r < n → o r = C.off + C.ld * (j + r) := fun r hr => by
      simp only [o, ← hco, ← hcl,
        toNat_col_base C hs.2.2.1 hs.2.2.2.2.2.2 hr (Nat.lt_trans hr hs.2.2.2.2.1)]
    gemmTNCols α A B β C hs co cl hco hcl (j + 2)
      (gemmTN2Data α A B β j (by lia) (o 0) (o 1) c
        (by rw [ho 0 (by lia), ho 1 (by lia)]; exact col_add_le' C.le_ld)
        (by rw [ho 1 (by lia), hc]; exact C.col_le hs.2.2.2.2.2.2 (by lia))
        ⟨hs.1, hs.2.1, hc ▸ hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)
      (by rw [gemmTN2Data_eq, size_gemmTNCol, size_gemmTNCol, hc])
  else if h1 : j < n then
    let o := (co + cl * j.toUSize).toNat
    have ho : o = C.off + C.ld * j := by
      simp only [o, ← hco, ← hcl,
        toNat_col_base C hs.2.2.1 hs.2.2.2.2.2.2 h1 (Nat.lt_trans h1 hs.2.2.2.2.1)]
    gemmTNCols α A B β C hs co cl hco hcl (j + 1)
      (gemmTN1Data α A B β j h1 o c (by rw [ho, hc]; exact C.col_le hs.2.2.2.2.2.2 h1)
        ⟨hs.1, hs.2.1, hc ▸ hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩)
      (by rw [gemmTN1Data_eq, size_gemmTNCol, hc])
  else c
termination_by n - j

private theorem gemmTNCols_eq (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n)
    (hs : GemmTFits A B C) (co cl : USize) (hco : C.off.toUSize = co)
    (hcl : C.ld.toUSize = cl) (j : Nat) (c : Float32Array) (hc : c.size = C.data.size) :
    gemmTNCols α A B β C hs co cl hco hcl j c hc =
      iterRange (fun j c => gemmTNCol α A B β (C.off + C.ld * j) j c) j n c := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d using Nat.strongRecOn generalizing j c with
  | ind d ih =>
    rw [gemmTNCols]
    split
    · rename_i h2
      have ho : ∀ r, j + r < n → (co + cl * (j + r).toUSize).toNat = C.off + C.ld * (j + r) :=
        fun r hr => by
          rw [← hco, ← hcl,
            toNat_col_base C hs.2.2.1 hs.2.2.2.2.2.2 hr (Nat.lt_trans hr hs.2.2.2.2.1)]
      rw [ih (n - (j + 2)) (by lia) (j + 2) _ _ rfl, iterRange_of_lt _ (show j < n by lia),
        iterRange_of_lt _ (show j + 1 < n by lia), gemmTN2Data_eq]
      dsimp only
      rw [ho 0 (by lia), ho 1 (by lia)]
      rfl
    split
    · rename_i h2 h1
      have ho : (co + cl * j.toUSize).toNat = C.off + C.ld * j := by
        rw [← hco, ← hcl,
          toNat_col_base C hs.2.2.1 hs.2.2.2.2.2.2 h1 (Nat.lt_trans h1 hs.2.2.2.2.1)]
      rw [ih (n - (j + 1)) (by lia) (j + 1) _ _ rfl, iterRange_of_lt _ h1, gemmTN1Data_eq, ho]
    · rename_i h2 h1
      rw [iterRange_of_le _ (by lia)]

/-- Steps that each map column `j` by `H j` map the columns by `mapMat`. -/
private theorem iterRange_col_mapMat (a : Float32Array) (off ld : Nat) (hml : m ≤ ld)
    (H : Nat → Nat → Float32 → Float32) (J : Nat) :
    iterRange (fun j c => c.modifyAt (fun i => off + ld * j + i) 0 m (H j)) 0 J a =
      mapMat a off ld m 0 J fun i j v => H j i v := by
  induction J with
  | zero => rw [iterRange_self, mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)]
  | succ J ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih, ← modifyAt_col_mapMat _ _ _ hml J]
    exact modifyAt_congr _ (fun i _ _ => by simp [Stride.idx]) (fun _ _ _ => rfl)

/-- The array of `gemmTN`, for `α ≠ 0`. -/
public def gemmTNData (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n) :
    Float32Array :=
  if hs : GemmTFits A B C then
    gemmTNCols α A B β C hs C.off.toUSize C.ld.toUSize rfl rfl 0 C.data rfl
  else mapMat C.data C.off C.ld m 0 n (gemmTSumAt α A B β)

public theorem gemmTNData_eq (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n) :
    gemmTNData α A B β C = mapMat C.data C.off C.ld m 0 n (gemmTSumAt α A B β) := by
  unfold gemmTNData
  split
  · rw [gemmTNCols_eq]
    exact iterRange_col_mapMat _ _ _ C.le_ld (fun j i v => gemmTSumAt α A B β i j v) n
  · rfl

/--
The value of `gemmTN` at `(i, j)`, from the old value `v`, with the special cases of the reference
BLAS: `betaMul β v` when `α = 0`, and `v` when `k = 0` and `β = 1`.
-/
@[expose] public def gemmTNAt (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (i j : Nat)
    (v : Float32) : Float32 :=
  if α == 0 then betaMul β v
  else if k == 0 && β == 1 then v
  else gemmTSumAt α A B β i j v

/--
`gemmTN α A B β C` is `α * Aᵀ * B + β * C`, by the loops of the reference BLAS: for each element
`(i, j)`, it sums the products `A[l, i] * B[l, j]` for `l = 0, …, k - 1` from the left, into `t`,
then writes `α * t + β * C[i, j]`, or `α * t` without reading `C[i, j]` when `β = 0`. It computes
the sums of four rows of two columns `j` and `j + 1` together, in one pass over the columns of `A`
and `B`, which gives the same sums, lets their additions overlap and shares their reads. As in the reference BLAS, it only
scales `C` when `α = 0`, without reading `A` or `B`, and returns `C` when `k = 0` and `β = 1`. It
updates `C` in place when its array is not shared, and leaves the elements of the array outside
`C` unchanged.
-/
@[expose] public def gemmTN (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n) :
    Mat m n :=
  if α == 0 then
    { data := C.scalBetaData β
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalBetaData_eq, size_mapMat]; exact C.bound }
  else if k == 0 && β == 1 then C
  else
    { data := gemmTNData α A B β C
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [gemmTNData_eq, size_mapMat]; exact C.bound }

/-- The array of `gemmTN α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemmTN (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n) :
    (gemmTN α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmTNAt α A B β) := by
  unfold gemmTN gemmTNAt
  cases hα : α == 0
  · cases hq : (k == 0 && β == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, gemmTNData_eq]
    · simp only [Bool.false_eq_true, ↓reduceIte, mapMat_id]
  · simp only [↓reduceIte, scalBetaData_eq]

@[simp] public theorem off_gemmTN (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32)
    (C : Mat m n) : (gemmTN α A B β C).off = C.off := by
  unfold gemmTN; split
  · rfl
  · split <;> rfl

@[simp] public theorem ld_gemmTN (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32)
    (C : Mat m n) : (gemmTN α A B β C).ld = C.ld := by
  unfold gemmTN; split
  · rfl
  · split <;> rfl

/--
The value of `gemmTN α A B β C` at `(i, j)`: `betaMul β C[i, j]` when `α = 0`, `C[i, j]` when
`k = 0` and `β = 1`, and otherwise `α * t`, when `β = 0`, or `α * t + β * C[i, j]`, where `t` is
the sum of the products `A[l, i] * B[l, j]` for `l = 0, …, k - 1`, from the left.
-/
@[expose] public def gemmTNEntry (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32)
    (C : Mat m n) (i j : Nat) (hi : i < m) (hj : j < n) : Float32 :=
  if α == 0 then betaMul β C[(i, j)]
  else if k == 0 && β == 1 then C[(i, j)]
  else
    let t := Nat.fold k (fun l hl s => s + A[(l, i)] * B[(l, j)]) 0
    if β == 0 then α * t else α * t + β * C[(i, j)]

@[simp] public theorem getElem_gemmTN (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmTN α A B β C)[(i, j)] = gemmTNEntry α A B β C i j h.1 h.2 := by
  rw [getElem_of_data_eq_mapMat _ (data_gemmTN α A B β C) (off_gemmTN ..) (ld_gemmTN ..) i j h,
    gemmTNAt]
  have e : gemmTSum A B i j = Nat.fold k (fun l hl s => s + A[(l, i)] * B[(l, j)]) 0 := by
    unfold gemmTSum
    congr
    funext l hl s
    rw [getElem!_pos A.data _ (A.index_lt hl h.1), getElem!_pos B.data _ (B.index_lt hl h.2)]
    rfl
  cases hα : α == 0 <;> cases hq : (k == 0 && β == 1) <;>
    simp [gemmTNEntry, gemmTSumAt, gemmTVal, hα, hq, e]

/-! ## `gemmTT` -/

/--
The value of `gemmTT α A B β C` at `(i, j)`: `betaMul β C[i, j]` when `α = 0`, `C[i, j]` when
`k = 0` and `β = 1`, and otherwise `α * t`, when `β = 0`, or `α * t + β * C[i, j]`, where `t` is
the sum of the products `A[l, i] * B[j, l]` for `l = 0, …, k - 1`, from the left.
-/
@[expose] public def gemmTTEntry (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32)
    (C : Mat m n) (i j : Nat) (hi : i < m) (hj : j < n) : Float32 :=
  if α == 0 then betaMul β C[(i, j)]
  else if k == 0 && β == 1 then C[(i, j)]
  else
    let t := Nat.fold k (fun l hl s => s + A[(l, i)] * B[(j, l)]) 0
    if β == 0 then α * t else α * t + β * C[(i, j)]

/-- `gemmTTEntry` at every element of a matrix, and the old value elsewhere. -/
@[expose] public def gemmTTAt (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32)
    (C : Mat m n) (i j : Nat) (v : Float32) : Float32 :=
  if h : i < m ∧ j < n then gemmTTEntry α A B β C i j h.1 h.2 else v

/--
`gemmTT α A B β C` is `α * Aᵀ * Bᵀ + β * C`, by the loops of `gemmTN` on a transposed copy of `B`.
Each element gets the operations of the loops of the reference BLAS, in the same order: the sum `t`
of the products `A[l, i] * B[j, l]` for `l = 0, …, k - 1`, from the left, then
`α * t + β * C[i, j]`, or `α * t` without reading `C[i, j]` when `β = 0`. As in the reference BLAS,
it only scales `C` when `α = 0`, without reading `A` or `B`, and returns `C` when `k = 0` and
`β = 1`. It updates `C` in place when its array is not shared, and leaves the elements of the array
outside `C` unchanged.
-/
@[expose] public def gemmTT (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32) (C : Mat m n) :
    Mat m n :=
  if α == 0 then
    { data := C.scalBetaData β
      off := C.off
      ld := C.ld
      le_ld := C.le_ld
      bound := by rw [scalBetaData_eq, size_mapMat]; exact C.bound }
  else gemmTN α A B.transpose β C

@[simp] public theorem off_gemmTT (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32)
    (C : Mat m n) : (gemmTT α A B β C).off = C.off := by
  unfold gemmTT; split <;> simp

@[simp] public theorem ld_gemmTT (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32)
    (C : Mat m n) : (gemmTT α A B β C).ld = C.ld := by
  unfold gemmTT; split <;> simp

/-- The array of `gemmTT α A B β C` is the array of `C` with its elements updated. -/
public theorem data_gemmTT (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32) (C : Mat m n) :
    (gemmTT α A B β C).data = mapMat C.data C.off C.ld m 0 n (gemmTTAt α A B β C) := by
  unfold gemmTT
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, data_gemmTN]
    exact mapMat_congr_getElem _ _ _ _ _ _ fun i j hi _ hj _ => by
      have e : gemmTSum A B.transpose i j =
          Nat.fold k (fun l hl s => s + A[(l, i)] * B[(j, l)]) 0 := by
        unfold gemmTSum
        congr
        funext l hl s
        have := getElem_transpose B l j ⟨hl, hj⟩
        rw [getElem_def, getElem_def] at this
        rw [getElem!_pos A.data _ (A.index_lt hl hi),
          getElem!_pos B.transpose.data _ (B.transpose.index_lt hl hj), this]
        rfl
      cases hq : (k == 0 && β == 1) <;>
        simp [gemmTNAt, gemmTTAt, gemmTTEntry, gemmTSumAt, gemmTVal, hi, hj, hα, hq, e,
          getElem_def]
  · simp only [↓reduceIte, scalBetaData_eq]
    exact mapMat_congr_getElem _ _ _ _ _ _ fun i j hi _ hj _ => by
      simp [gemmTTAt, gemmTTEntry, hi, hj, hα, getElem_def]

@[simp] public theorem getElem_gemmTT (α : Float32) (A : Mat k m) (B : Mat n k) (β : Float32)
    (C : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (gemmTT α A B β C)[(i, j)] = gemmTTEntry α A B β C i j h.1 h.2 := by
  rw [getElem_of_data_eq_mapMat _ (data_gemmTT α A B β C) (off_gemmTT α A B β C)
    (ld_gemmTT α A B β C) i j h]
  simp [gemmTTAt, h.1, h.2]

end Mat

end BLAS.Float32
