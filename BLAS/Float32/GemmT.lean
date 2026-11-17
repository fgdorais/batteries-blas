/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Gemm
public import BLAS.Float32.Level2
import all BLAS.Internal

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
    (inplace t do
      for i in 0...mu do
        let ti := nu * i
        have hti : ti.toNat + nu.toNat ≤ t.size :=
          toNat_mul_add_le (n := m) (by lia) (by rw [hnu, ht]; exact Nat.le_refl _)
        for j in 0...nu do
          t[ti + j] := A.uget ao al rfl rfl hs.1 i j (by lia) (by lia)).2
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

/-- The array of `gemmTN`, for `α ≠ 0`. -/
public def gemmTNData (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n) :
    Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ C.data.size < USize.size ∧
      m < USize.size ∧ n < USize.size ∧ k < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let c := C.data
    let co := C.off.toUSize
    let cl := C.ld.toUSize
    (inplace c do
      for j in 0...nu do
        let cj := co + cl * j
        let sums := gemmTSums A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.1 hs.2.2.2.2.2 j.toNat (by lia)
        for i in 0...mu do
          have hk : (cj + 1 * i).toNat < c.size := C.toNat_col_index_lt hs.2.2.1 (by lia) (by lia)
          c[cj + 1 * i] := gemmTVal α β sums[i.toNat]! c[cj + 1 * i]).2
  else mapMat C.data C.off C.ld m 0 n (gemmTSumAt α A B β)

public theorem gemmTNData_eq (α : Float32) (A : Mat k m) (B : Mat k n) (β : Float32) (C : Mat m n) :
    gemmTNData α A B β C = mapMat C.data C.off C.ld m 0 n (gemmTSumAt α A B β) := by
  unfold gemmTNData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (C.off + C.ld * j) 1).idx 0 m fun i v => gemmTSumAt α A B β i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ C.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      rw [Tail.run_forInFrom_modify (G := fun i v => gemmTSumAt α A B β i j.toNat v)
        (idx := (Stride.mk (C.off + C.ld * j.toNat) 1).idx)
        (he := fun i _ hi => C.toNat_col_index hs.2.2.1 (by lia) hj)]
      · simp only [USize.toNat_zero, hmu]
      · intro i _ hi v
        rw [hmu] at hi
        have hsp := gemmTSums_spec A B ⟨hs.1, hs.2.1⟩ hs.2.2.2.1 hs.2.2.2.2.2 _ hj
        rw [getElem!_pos _ _ (by rw [hsp.1]; exact hi), hsp.2]
        rfl
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
the sums of four elements of a column in each pass over column `j` of `B`, by the loops of `gemvT`,
which gives the same sums and lets their additions overlap. As in the reference BLAS, it only
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
