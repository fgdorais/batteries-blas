/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Herm3

/-!
# Complex triangular product, Level 3

`trmm` (`B := α * A * B`), `trmmT` (`B := α * Aᵀ * B`) and `trmmC` (`B := α * Aᴴ * B`), and
`trmmRight` (`B := α * B * A`), `trmmRightT` (`B := α * B * Aᵀ`) and `trmmRightC`
(`B := α * B * Aᴴ`), for the upper or the lower triangle of `A`, with a unit diagonal or not, as
`ctrmm` in the reference BLAS (`master`, without the zero skips of LAPACK 3.12), with the same
operations in the same order.

Each read of `B` in the loops of `ctrmm` sees an element that the loops haven't written yet, so
each routine here reads the elements of `B` as they are given and writes them into a copy of `B`,
updated in place: the steps of the reference loops are then pointwise on the elements of the copy.
As in the reference BLAS, all of them set `B` to `0` without reading `A` or `B` when `α = 0`.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.ComplexFloat32

namespace Mat

variable {m n : Nat}

/-! ## Updates of a column by its elements -/

/-- `C` with each element `c` of row `i` of column `j` replaced by `f i c`, one row at a time. -/
@[specialize] public def mapColIdx (f : (i : Nat) → i < m → ComplexFloat32 → ComplexFloat32)
    (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  Nat.fold m (fun i hi C => C.setAt i j ⟨hi, hj⟩ (f i hi C[(i, j)])) C

public theorem getElem_mapColIdx (f : (i : Nat) → i < m → ComplexFloat32 → ComplexFloat32)
    (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (mapColIdx f C j hj)[(i, j')] = if j' = j then f i h.1 C[(i, j')] else C[(i, j')] := by
  unfold mapColIdx
  rw [getElem_fold_of_pointwise (fun i hi C => C.setAt i j ⟨hi, hj⟩ (f i hi C[(i, j)]))
    (fun i' hi' i j' h v => if j' = j ∧ i = i' then f i' hi' v else v)
    (fun i' hi' B i j' h => by
      rw [getElem_setAt]
      by_cases e2 : i = i' ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := e2; simp
      · have : ¬ (j' = j ∧ i = i') := fun ⟨a, b⟩ => e2 ⟨b, a⟩
        simp only [e2, this, ↓reduceIte])
    C i j' h m (Nat.le_refl _)]
  have key : ∀ K (hK : K ≤ m) (v : ComplexFloat32), Nat.fold K (fun i' hi' w =>
      if j' = j ∧ i = i' then f i' (by lia) w else w) v =
      if j' = j ∧ i < K then f i h.1 v else v := by
    intro K hK v
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.fold_succ, ih (by lia)]
      by_cases e : j' = j ∧ i = K
      · obtain ⟨rfl, rfl⟩ := e
        simp
      · by_cases e' : j' = j
        · have : i ≠ K := fun h => e ⟨e', h⟩
          have h2 : (i < K + 1) = (i < K) := by apply propext; lia
          simp [e', this, h2]
        · simp [e']
  rw [key m (Nat.le_refl _)]
  simp [h.1]

/-! ## `trmm` -/

/--
The step of `trmm` for row `k` of column `j`: with `t = mul α B[k, j]`, it adds `mul t A[i, k]` to
the elements `i` of the column in the triangle of column `k` of `A`, other than the diagonal, and
sets element `k` to `diagMul d t A[k, k]`, as `ctrmm` with `SIDE = 'L'` and `TRANSA = 'N'`. It
reads `B` and writes `C`.
-/
public def trmmStep (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32) (A : Mat m m)
    (B : Mat m n) (j : Nat) (hj : j < n) (k : Nat) (hk : k < m) (C : Mat m n) : Mat m n :=
  let t := mul α B[(k, j)]
  let C :=
    if uplo = .upper then axpyColSlice t A k hk C j hj 0 k (by lia)
    else axpyColSlice t A k hk C j hj (k + 1) (m - (k + 1)) (by lia)
  C.setAt k j ⟨hk, hj⟩ (diagMul d t A[(k, k)])

/-- The step `trmmStep` at element `i` of column `j`, from its old value `v`. -/
@[expose] public def trmmStepAt (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) (j : Nat) (hj : j < n) (k : Nat) (hk : k < m) (i : Nat)
    (hi : i < m) (v : ComplexFloat32) : ComplexFloat32 :=
  if i = k then diagMul d (mul α B[(k, j)]) A[(k, k)]
  else if InTri uplo i k then v + mul (mul α B[(k, j)]) A[(i, k)]
  else v

private theorem getElem_trmmStep (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) (j : Nat) (hj : j < n) (k : Nat) (hk : k < m) (C : Mat m n)
    (i j' : Nat) (h : i < m ∧ j' < n) :
    (trmmStep uplo d α A B j hj k hk C)[(i, j')] =
      if j' = j then trmmStepAt uplo d α A B j hj k hk i h.1 C[(i, j')] else C[(i, j')] := by
  unfold trmmStep trmmStepAt
  rw [getElem_setAt]
  cases uplo
  rotate_left
  · simp only [reduceCtorEq, ↓reduceIte, InTri, false_and, true_and, false_or]
    rw [getElem_axpyColSlice]
    by_cases e : j' = j
    · subst e
      by_cases e' : i = k
      · subst e'; simp
      · have h1 : (k + 1 ≤ i ∧ i < k + 1 + (m - (k + 1))) = (k < i) := by apply propext; lia
        simp [e', h1]
    · simp [e]
  · simp only [↓reduceIte, InTri, true_and]
    rw [getElem_axpyColSlice]
    by_cases e : j' = j
    · subst e
      by_cases e' : i = k
      · subst e'; simp
      · simp [e']
    · simp [e]

/-- Column `j` of `trmm`: the steps `trmmStep` for each row, in the order of `hemmRow`. -/
public def trmmCol (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32) (A : Mat m m)
    (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  Nat.fold m (fun s hs C => trmmStep uplo d α A B j hj (hemmRow uplo m s) (hemmRow_lt uplo hs) C) C

private theorem getElem_trmmCol (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat)
    (h : i < m ∧ j' < n) :
    (trmmCol uplo d α A B C j hj)[(i, j')] =
      if j' = j then
        Nat.fold m (fun s hs v => trmmStepAt uplo d α A B j hj (hemmRow uplo m s)
          (hemmRow_lt uplo hs) i h.1 v) C[(i, j')]
      else C[(i, j')] := by
  unfold trmmCol
  rw [getElem_fold_of_pointwise
    (fun s hs C => trmmStep uplo d α A B j hj (hemmRow uplo m s) (hemmRow_lt uplo hs) C)
    (fun s hs i j' h v => if j' = j then trmmStepAt uplo d α A B j hj (hemmRow uplo m s)
      (hemmRow_lt uplo hs) i h.1 v else v)
    (fun _ _ _ _ _ _ => getElem_trmmStep ..) C i j' h m (Nat.le_refl _)]
  by_cases e : j' = j
  · simp [e]
  · simp only [e, ↓reduceIte, fold_id]

/-- `C` with column `j` set to `0`. -/
public def zeroCol (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  mapColSlice (fun _ => zero) C j hj 0 m (by lia)

public theorem getElem_zeroCol (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat)
    (h : i < m ∧ j' < n) :
    (zeroCol C j hj)[(i, j')] = if j' = j then zero else C[(i, j')] := by
  simp [zeroCol, getElem_mapColSlice, h.1]

/--
`trmm uplo d α A B` is `α * A * B` for the triangle `uplo` of `A`, with a unit diagonal if `d` is
`.unit`, as `ctrmm` with `SIDE = 'L'` and `TRANSA = 'N'`: it sets `B` to `0` when `α = 0`, and
otherwise runs `trmmCol` for each column, from the first row for the upper triangle and from the
last row for the lower one.
-/
@[expose] public def trmm (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) : Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else Nat.fold n (fun j hj C => trmmCol uplo d α A B C j hj) B

/--
Element `(i, j)` of `trmm uplo d α A B`: `0` when `α = 0`, and otherwise the fold of the steps
`trmmStepAt` over the rows in the order of `hemmRow`, from `B[i, j]`.
-/
public theorem getElem_trmm (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trmm uplo d α A B)[(i, j)] =
      if isZero α then zero
      else Nat.fold m (fun s hs v => trmmStepAt uplo d α A B j h.2 (hemmRow uplo m s)
        (hemmRow_lt uplo hs) i h.1 v) B[(i, j)] := by
  unfold trmm
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => trmmCol uplo d α A B C j hj)
      (fun i j hij c => Nat.fold m (fun s hs v => trmmStepAt uplo d α A B j hij.2
        (hemmRow uplo m s) (hemmRow_lt uplo hs) i hij.1 v) c)
      (fun _ _ _ _ _ _ => getElem_trmmCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]

/-! ## `trmmT` and `trmmC` -/

/--
The sum of element `(i, j)` of `trmmTWith p`: `B[i, j]` times `p A[i, i]` (unless the diagonal is
unit), plus `mul (p A[k, i]) B[k, j]` for the other rows `k` of column `i` in the triangle, in
increasing order.
-/
@[expose, specialize] public def trmmTDot (p : ComplexFloat32 → ComplexFloat32)
    (uplo : Float32.Uplo) (d : Float32.Diag) (A : Mat m m) (B : Mat m n) (i j : Nat) (hi : i < m)
    (hj : j < n) : ComplexFloat32 :=
  if uplo = .upper then
    Vec.accWith p id (· + ·) (diagMul d B[(i, j)] (p A[(i, i)])) ((A.col i hi).slice 0 i (by lia))
      ((B.col j hj).slice 0 i (by lia))
  else
    Vec.accWith p id (· + ·) (diagMul d B[(i, j)] (p A[(i, i)]))
      ((A.col i hi).slice (i + 1) (m - (i + 1)) (by lia))
      ((B.col j hj).slice (i + 1) (m - (i + 1)) (by lia))

/--
`trmmTWith p uplo d α A B` is `α` times the product of the transpose of the triangle `uplo` of `A`,
with its elements mapped by `p`, by `B`, as `ctrmm` with `SIDE = 'L'` and `TRANSA = 'T'` (`p = id`)
or `'C'` (`p = conj`): it sets `B` to `0` when `α = 0`, and otherwise sets each element `(i, j)` to
`mul α (trmmTDot p uplo d A B i j)`.
-/
@[expose, specialize] public def trmmTWith (p : ComplexFloat32 → ComplexFloat32)
    (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32) (A : Mat m m) (B : Mat m n) :
    Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else Nat.fold n (fun j hj C =>
    mapColIdx (fun i hi _ => mul α (trmmTDot p uplo d A B i j hi hj)) C j hj) B

/-- Element `(i, j)` of `trmmTWith p uplo d α A B`: `0` when `α = 0`, and otherwise
`mul α (trmmTDot p uplo d A B i j)`. -/
public theorem getElem_trmmTWith (p : ComplexFloat32 → ComplexFloat32) (uplo : Float32.Uplo)
    (d : Float32.Diag) (α : ComplexFloat32) (A : Mat m m) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trmmTWith p uplo d α A B)[(i, j)] =
      if isZero α then zero else mul α (trmmTDot p uplo d A B i j h.1 h.2) := by
  unfold trmmTWith
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C =>
        mapColIdx (fun i hi _ => mul α (trmmTDot p uplo d A B i j hi hj)) C j hj)
      (fun i j hij _ => mul α (trmmTDot p uplo d A B i j hij.1 hij.2))
      (fun _ _ _ _ _ _ => getElem_mapColIdx ..) B i j h n (Nat.le_refl _)]
    simp [h.2]

/-- `trmmT uplo d α A B` is `α * Aᵀ * B`, as `trmmTWith id`. -/
@[expose] public def trmmT (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) : Mat m n :=
  trmmTWith id uplo d α A B

/-- `trmmC uplo d α A B` is `α * Aᴴ * B`, as `trmmTWith conj`. -/
@[expose] public def trmmC (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat m m) (B : Mat m n) : Mat m n :=
  trmmTWith ComplexFloat32.conj uplo d α A B

/-! ## `trmmRight` -/

/--
Column `j` of `trmmRight`: each element becomes `mul (diagMul d α A[j, j]) B[i, j]`, and then gets
`mul (mul α A[l, j]) B[i, l]` for each column `l` of `A` in the triangle of column `j`, other than
the diagonal, in increasing order, as `ctrmm` with `SIDE = 'R'` and `TRANSA = 'N'`. It reads `B`
and writes `C`.
-/
public def trmmRightCol (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32) (A : Mat n n)
    (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) : Mat m n :=
  let t := diagMul d α A[(j, j)]
  let C := zipCol (fun _ b => mul t b) B j hj C j hj
  Nat.fold n (fun l hl C => if InTri uplo l j then
    axpyColSlice (mul α A[(l, j)]) B l hl C j hj 0 m (by lia) else C) C

private theorem getElem_trmmRightCol (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat n n) (B : Mat m n) (C : Mat m n) (j : Nat) (hj : j < n) (i j' : Nat)
    (h : i < m ∧ j' < n) :
    (trmmRightCol uplo d α A B C j hj)[(i, j')] =
      if j' = j then
        Nat.fold n (fun l hl v => if InTri uplo l j then
          v + mul (mul α A[(l, j)]) B[(i, l)] else v) (mul (diagMul d α A[(j, j)]) B[(i, j)])
      else C[(i, j')] := by
  unfold trmmRightCol
  rw [getElem_fold_of_pointwise
    (fun l hl C => if InTri uplo l j then
      axpyColSlice (mul α A[(l, j)]) B l hl C j hj 0 m (by lia) else C)
    (fun l hl i j' h v => if j' = j then (if InTri uplo l j then
      v + mul (mul α A[(l, j)]) B[(i, l)] else v) else v)
    (fun l hl C i j' h => by
      by_cases e : InTri uplo l j
      · simp only [e, ↓reduceIte, getElem_axpyColSlice, Nat.zero_le, Nat.zero_add, h.1,
          and_true]
      · simp [e])
    _ i j' h n (Nat.le_refl _)]
  rw [getElem_zipCol]
  by_cases e : j' = j
  · subst e; simp
  · simp [e, fold_id]

/--
`trmmRight uplo d α A B` is `α * B * A` for the triangle `uplo` of `A`, with a unit diagonal if
`d` is `.unit`, as `ctrmm` with `SIDE = 'R'` and `TRANSA = 'N'`: it sets `B` to `0` when `α = 0`,
and otherwise runs `trmmRightCol` for each column.
-/
@[expose] public def trmmRight (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat n n) (B : Mat m n) : Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else Nat.fold n (fun j hj C => trmmRightCol uplo d α A B C j hj) B

/--
Element `(i, j)` of `trmmRight uplo d α A B`: `0` when `α = 0`, and otherwise
`mul (diagMul d α A[j, j]) B[i, j]` plus `mul (mul α A[l, j]) B[i, l]` for each `l` in the
triangle of column `j`, other than `j`, in increasing order, from the left.
-/
public theorem getElem_trmmRight (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat n n) (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trmmRight uplo d α A B)[(i, j)] =
      if isZero α then zero
      else Nat.fold n (fun l hl v => if InTri uplo l j then
          v + mul (mul α (A[(l, j)]'⟨hl, h.2⟩)) B[(i, l)] else v)
        (mul (diagMul d α A[(j, j)]) B[(i, j)]) := by
  unfold trmmRight
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => trmmRightCol uplo d α A B C j hj)
      (fun i j hij _ => Nat.fold n (fun l hl v => if InTri uplo l j then
          v + mul (mul α (A[(l, j)]'⟨hl, hij.2⟩)) B[(i, l)] else v)
        (mul (diagMul d α A[(j, j)]) B[(i, j)]))
      (fun _ _ _ _ _ _ => getElem_trmmRightCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]

/-! ## `trmmRightT` and `trmmRightC` -/

/--
Column `j` of `trmmRightTWith p`: with `t = diagMul d α (p A[j, j])`, each element `c` becomes
`mul t B[i, j]` unless `t = 1`, and then gets `mul (mul α (p A[j, l])) B[i, l]` for each column `l`
in the triangle of row `j` of `A`, other than the diagonal, in the order of `hemmRow` (increasing
for the upper triangle, decreasing for the lower one), as `ctrmm` with `SIDE = 'R'` and
`TRANSA = 'T'` or `'C'`. It reads `B` and writes `C`.
-/
@[specialize] public def trmmRightTCol (p : ComplexFloat32 → ComplexFloat32) (uplo : Float32.Uplo)
    (d : Float32.Diag) (α : ComplexFloat32) (A : Mat n n) (B : Mat m n) (C : Mat m n) (j : Nat)
    (hj : j < n) : Mat m n :=
  let t := diagMul d α (p A[(j, j)])
  let C := if isOne t then C else zipCol (fun _ b => mul t b) B j hj C j hj
  Nat.fold n (fun s hs C =>
    let l := hemmRow uplo n s
    have hl : l < n := hemmRow_lt uplo hs
    if InTri uplo j l then axpyColSlice (mul α (p A[(j, l)])) B l hl C j hj 0 m (by lia)
    else C) C

/-- The first value of element `(i, j)` of `trmmRightTWith p`, from `b = B[i, j]`. -/
@[expose] public def trmmRightTInit (t b : ComplexFloat32) : ComplexFloat32 :=
  if isOne t then b else mul t b

private theorem getElem_trmmRightTCol (p : ComplexFloat32 → ComplexFloat32) (uplo : Float32.Uplo)
    (d : Float32.Diag) (α : ComplexFloat32) (A : Mat n n) (B : Mat m n) (C : Mat m n) (j : Nat)
    (hj : j < n) (i j' : Nat) (h : i < m ∧ j' < n) :
    (trmmRightTCol p uplo d α A B C j hj)[(i, j')] =
      if j' = j then
        Nat.fold n (fun s hs v => if InTri uplo j (hemmRow uplo n s) then
            v + mul (mul α (p (A[(j, hemmRow uplo n s)]'⟨hj, hemmRow_lt uplo hs⟩)))
              (B[(i, hemmRow uplo n s)]'⟨h.1, hemmRow_lt uplo hs⟩)
          else v)
          (if isOne (diagMul d α (p A[(j, j)])) then C[(i, j')]
            else mul (diagMul d α (p A[(j, j)])) B[(i, j)])
      else C[(i, j')] := by
  unfold trmmRightTCol
  rw [getElem_fold_of_pointwise
    (fun s hs C =>
      if InTri uplo j (hemmRow uplo n s) then
        axpyColSlice (mul α (p (A[(j, hemmRow uplo n s)]'⟨hj, hemmRow_lt uplo hs⟩))) B
          (hemmRow uplo n s) (hemmRow_lt uplo hs) C j hj 0 m (by lia)
      else C)
    (fun s hs i j' h v => if j' = j then (if InTri uplo j (hemmRow uplo n s) then
        v + mul (mul α (p (A[(j, hemmRow uplo n s)]'⟨hj, hemmRow_lt uplo hs⟩)))
          (B[(i, hemmRow uplo n s)]'⟨h.1, hemmRow_lt uplo hs⟩)
      else v) else v)
    (fun s hs C i j' h => by
      by_cases e : InTri uplo j (hemmRow uplo n s)
      · simp only [e, ↓reduceIte, getElem_axpyColSlice, Nat.zero_le, Nat.zero_add, h.1,
          and_true]
      · simp [e])
    _ i j' h n (Nat.le_refl _)]
  by_cases e : j' = j
  · subst e
    by_cases ht : isOne (diagMul d α (p A[(j', j')]))
    · simp [ht]
    · simp [ht, getElem_zipCol]
  · by_cases ht : isOne (diagMul d α (p A[(j, j)]))
    · simp [e, ht, fold_id]
    · simp [e, ht, fold_id, getElem_zipCol]

/--
`trmmRightTWith p uplo d α A B` is `α` times the product of `B` by the transpose of the triangle
`uplo` of `A`, with its elements mapped by `p`, as `ctrmm` with `SIDE = 'R'` and `TRANSA = 'T'`
(`p = id`) or `'C'` (`p = conj`): it sets `B` to `0` when `α = 0`, and otherwise runs
`trmmRightTCol p` for each column.
-/
@[expose, specialize] public def trmmRightTWith (p : ComplexFloat32 → ComplexFloat32)
    (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32) (A : Mat n n) (B : Mat m n) :
    Mat m n :=
  if isZero α then Nat.fold n (fun j hj C => zeroCol C j hj) B
  else Nat.fold n (fun j hj C => trmmRightTCol p uplo d α A B C j hj) B

/--
Element `(i, j)` of `trmmRightTWith p uplo d α A B`: `0` when `α = 0`, and otherwise
`trmmRightTInit (diagMul d α (p A[j, j])) B[i, j]` plus `mul (mul α (p A[j, l])) B[i, l]` for each
`l` in the triangle of row `j` of `A`, other than `j`, in the order of `hemmRow`, from the left.
-/
public theorem getElem_trmmRightTWith (p : ComplexFloat32 → ComplexFloat32) (uplo : Float32.Uplo)
    (d : Float32.Diag) (α : ComplexFloat32) (A : Mat n n) (B : Mat m n) (i j : Nat)
    (h : i < m ∧ j < n) :
    (trmmRightTWith p uplo d α A B)[(i, j)] =
      if isZero α then zero
      else Nat.fold n (fun s hs v => if InTri uplo j (hemmRow uplo n s) then
            v + mul (mul α (p (A[(j, hemmRow uplo n s)]'⟨h.2, hemmRow_lt uplo hs⟩)))
              (B[(i, hemmRow uplo n s)]'⟨h.1, hemmRow_lt uplo hs⟩)
          else v)
        (trmmRightTInit (diagMul d α (p A[(j, j)])) B[(i, j)]) := by
  unfold trmmRightTWith trmmRightTInit
  by_cases ha : isZero α
  · simp only [ha, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => zeroCol C j hj) (fun _ _ _ _ => zero)
      (fun _ _ _ _ _ _ => getElem_zeroCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [getElem_fold_col (fun j hj C => trmmRightTCol p uplo d α A B C j hj)
      (fun i j hij c => Nat.fold n (fun s hs v => if InTri uplo j (hemmRow uplo n s) then
            v + mul (mul α (p (A[(j, hemmRow uplo n s)]'⟨hij.2, hemmRow_lt uplo hs⟩)))
              (B[(i, hemmRow uplo n s)]'⟨hij.1, hemmRow_lt uplo hs⟩)
          else v)
          (if isOne (diagMul d α (p A[(j, j)])) then c
            else mul (diagMul d α (p A[(j, j)])) B[(i, j)]))
      (fun _ _ _ _ _ _ => getElem_trmmRightTCol ..) B i j h n (Nat.le_refl _)]
    simp [h.2]

/-- `trmmRightT uplo d α A B` is `α * B * Aᵀ`, as `trmmRightTWith id`. -/
@[expose] public def trmmRightT (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat n n) (B : Mat m n) : Mat m n :=
  trmmRightTWith id uplo d α A B

/-- `trmmRightC uplo d α A B` is `α * B * Aᴴ`, as `trmmRightTWith conj`. -/
@[expose] public def trmmRightC (uplo : Float32.Uplo) (d : Float32.Diag) (α : ComplexFloat32)
    (A : Mat n n) (B : Mat m n) : Mat m n :=
  trmmRightTWith ComplexFloat32.conj uplo d α A B

end Mat

end BLAS.ComplexFloat32
