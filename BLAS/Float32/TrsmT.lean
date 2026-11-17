/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Trsm
public import BLAS.Float32.TrsvT
import all BLAS.Internal

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

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

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
@[expose] public def trsmTAt (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n)
    (i j : Nat) : Float32 :=
  if α == 0 then 0 else trsvTAscSol uplo d A (scaledCol α B j) i

private theorem size_scalData_colOf (α : Float32) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float32Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) : (Vec.scalData α (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [Vec.scalData_eq, size_modifyAt]; exact hb

private theorem size_trsvTAscData_colOf (uplo : Uplo) (d : Diag) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (b : Float32Array) (hb : b.size = sz)
    (j : Nat) (hj : j < n) : (trsvTAscData uplo d A (colOf off ld sz hsz b hb j hj)).size = sz := by
  rw [trsvTAscData_eq, size_modifyAt]; exact hb

/--
The loop of `trsmT` over the columns from `j`, on the array `b` of an `m × n` matrix: it scales
column `j` by `α`, then solves it by `trsvTAscData`. It takes the offset and the leading dimension
of the matrix rather than the matrix, which would keep a second reference to its array.
-/
public def trsmTLoop (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (off ld sz : Nat)
    (hsz : m = 0 ∨ n = 0 ∨ off + ld * (n - 1) + m ≤ sz) (j : Nat) (b : Float32Array)
    (hb : b.size = sz) : Float32Array :=
  if hj : j < n then
    trsmTLoop uplo d α A off ld sz hsz (j + 1)
      (trsvTAscData uplo d A (colOf off ld sz hsz (Vec.scalData α (colOf off ld sz hsz b hb j hj))
        (size_scalData_colOf ..) j hj))
      (size_trsvTAscData_colOf ..)
  else b
termination_by n - j

/-- The value at `(i, j)` of `trsmT` for `α ≠ 0`, from the column `j` of the array `a`. -/
private def trsmTColAt (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n)
    (a : Float32Array) (i j : Nat) (_ : Float32) : Float32 :=
  trsvTAscSol uplo d A (Vec.ofFn fun l : Fin m => α * a[B.off + B.ld * j + l.val]!) i

/-- A step of `trsmTLoop` maps column `j` to its solution. -/
private theorem trsmTLoop_step (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j < n) (b : Float32Array) (hb : b.size = B.data.size)
    (a : Float32Array) (hcol : ∀ l, l < m → b[B.off + B.ld * j + l]! = a[B.off + B.ld * j + l]!) :
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
private theorem getElem!_mapMat_col_of_not (a : Float32Array) (off ld lo hi : Nat)
    (g : Nat → Nat → Float32 → Float32) (hml : m ≤ ld) {j : Nat} (hj : ¬(lo ≤ j ∧ j < hi)) {l : Nat}
    (hl : l < m) : (mapMat a off ld m lo hi g)[off + ld * j + l]! = a[off + ld * j + l]! := by
  by_cases hq : off + ld * j + l < a.size
  · rw [getElem!_pos _ _ (by rw [size_mapMat]; exact hq), getElem!_pos a _ hq,
      getElem_mapMat_of_ne _ _ _ _ _ _ _ (fun i' j' hi' h₁ h₂ e' => by
        by_cases hjj : j = j'
        · subst hjj; exact hj ⟨h₁, h₂⟩
        · exact col_index_ne hl hi' hml hjj e') hq]
  · rw [getElem!_neg _ _ (by rw [size_mapMat]; exact hq), getElem!_neg a _ hq]

/-- `trsmTLoop` from column `j`, after the columns before `j` are solved, solves all of them. -/
private theorem trsmTLoop_eq (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n)
    (j : Nat) (hj : j ≤ n) (b : Float32Array) (hb : b.size = B.data.size)
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

/-- The array of `trsmT`. -/
public def trsmTData (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) :
    Float32Array :=
  if α == 0 then B.scalBetaData 0
  else trsmTLoop uplo d α A B.off B.ld B.data.size B.bound 0 B.data rfl

public theorem trsmTData_eq (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) :
    trsmTData uplo d α A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmTAt uplo d α A B i j := by
  unfold trsmTData
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [trsmTLoop_eq uplo d α A B 0 (Nat.zero_le _) _ rfl
      (mapMat_of_le _ _ _ _ _ _ _ (Nat.le_refl _)).symm]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmTColAt, trsmTAt, scaledCol, hα]
  · simp only [↓reduceIte, scalBetaData_eq]
    apply mapMat_congr
    intro i j v _ _ _
    simp [trsmTAt, betaMul, hα, show ((0 : Float32) == 0) = true from rfl]

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
@[expose] public def trsmT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) :
    Mat m n where
  data := trsmTData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trsmTData_eq, size_mapMat]; exact B.bound

/-- The array of `trsmT uplo d α A B` is the array of `B` with its elements solved. -/
public theorem data_trsmT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) :
    (trsmT uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmTAt uplo d α A B i j :=
  trsmTData_eq uplo d α A B

@[simp] public theorem off_trsmT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m)
    (B : Mat m n) : (trsmT uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trsmT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m)
    (B : Mat m n) : (trsmT uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trsmT uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trsmT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) : (trsmT uplo d α A B)[(i, j)] = trsmTAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trsmT uplo d α A B) rfl rfl i j h

/--
Element `(i, j)` of `X = trsmT .upper d α A B` is `0` when `α = 0`, and otherwise `α * B[i, j]`,
minus the terms `A[l, i] * X[l, j]` for `l = 0, …, i - 1`, divided by `A[i, i]` unless the diagonal
is unit: forward substitution with `Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsmT_upper (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) (i j : Nat)
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
public theorem getElem_trsmT_lower (d : Diag) (α : Float32) (A : Mat m m) (B : Mat m n) (i j : Nat)
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
public def trsmRightTUpper (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) : Float32 :=
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
public def trsmRightTLower (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) : Float32 :=
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
private theorem modifyAt_rows (b : Float32Array) (idx : Nat → Nat) (d : Diag) {mu : USize}
    (hmu : mu.toNat = m) (t : Float32) :
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
private theorem iterRange_subCols (c : Float32Array) (oj : Nat) (ok : Nat → Nat) (w : Nat → Float32)
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

/-- The array of the solve of `Z * Aᵀ = B` for the upper triangle of `A`. -/
public def trsmRightTUpperData (d : Diag) (A : Mat n n) (B : Mat m n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    (inplace b do
      for t in 0...nu do
        let j := nu - 1 - t
        have hj : j.toNat = n - 1 - t.toNat := by grind
        have hjn : j.toNat < n := by lia
        have hr : (nu - 1 - j).toNat = n - 1 - j.toNat := by grind
        let cj := bo + bl * j
        for t' in 0...(nu - 1 - j) do
          let k := nu - 1 - t'
          have hk : k.toNat = n - 1 - t'.toNat := by grind
          have hkn : k.toNat < n := by lia
          let w := A.uget ao al rfl rfl hs.1 j k hjn hkn
          let ck := bo + bl * k
          for i in 0...mu do
            have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hjn
            have hq' : (ck + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) hkn
            b[cj + 1 * i] := b[cj + 1 * i] - w * b[ck + 1 * i]
        let ajj := A.uget ao al rfl rfl hs.1 j j hjn hjn
        for i in 0...d.rows mu do
          have hq : (cj + 1 * i).toNat < b.size :=
            B.toNat_col_index_lt hs.2.1 (Nat.lt_of_lt_of_le (by assumption)
              (hmu ▸ d.toNat_rows_le)) hjn
          b[cj + 1 * i] := b[cj + 1 * i] / ajj).2
  else mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTUpper d A B i j

/--
The value of column `j` of the upper solve from its old value `v`, with the columns after it.
-/
private def trsmRightTUpperG (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) (v : Float32) :
    Float32 :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * (n - 1 - t) + j]! * trsmRightTUpper d A B i (n - 1 - t)) v)
    A.data[A.off + A.ld * j + j]!

private theorem trsmRightTUpper_eq_G (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) :
    trsmRightTUpper d A B i j = trsmRightTUpperG d A B i j B.data[B.off + B.ld * j + i]! := by
  rw [trsmRightTUpper]; rfl

/-- The step `t` of the upper solve, for column `j = n - 1 - t`, on the array `c`. -/
private def trsmRightTUpperCol (d : Diag) (A : Mat n n) (B : Mat m n) (t : Nat)
    (c : Float32Array) : Float32Array :=
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

public theorem trsmRightTUpperData_eq (d : Diag) (A : Mat n n) (B : Mat m n) :
    trsmRightTUpperData d A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTUpper d A B i j := by
  unfold trsmRightTUpperData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsmRightTUpperCol d A B)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_trsmRightTUpperCol d A B (Nat.le_refl _), Nat.sub_self]
      apply mapMat_congr_getElem
      intro i j hi _ hj hq
      rw [trsmRightTUpper_eq_G, getElem!_pos B.data _ hq]
    · intro t _ ht next a h
      rw [hnu] at ht
      have hj : (n.toUSize - 1 - t).toNat = n - 1 - t.toNat := by grind
      have hjn : n - 1 - t.toNat < n := by lia
      have hr : (n.toUSize - 1 - (n.toUSize - 1 - t)).toNat = n - 1 - (n - 1 - t.toNat) := by
        grind
      have hcol : ∀ k, k ≠ n - 1 - t.toNat → ∀ i, i < m → ∀ i', i' < m →
          B.off + B.ld * (n - 1 - t.toNat) + i ≠ B.off + B.ld * k + i' :=
        fun k hk i hi i' hi' => col_index_ne hi hi' B.le_ld (Ne.symm hk)
      rw [Tail.run_forInFrom_unit (F := fun t' c =>
          c.modifyAt (Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx 0 m fun i v =>
            v - A.data[A.off + A.ld * (n - 1 - t') + (n - 1 - t.toNat)]! *
              c[B.off + B.ld * (n - 1 - t') + i]!)
          (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
      · rw [Tail.run_forInFrom_modify
          (G := fun _ v => v / A.data[A.off + A.ld * (n - 1 - t.toNat) + (n - 1 - t.toNat)]!)
          (idx := (Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx)
          (e := fun i => B.off.toUSize + B.ld.toUSize * (n.toUSize - 1 - t) + 1 * i)
          (he := fun i _ hi => by
            rw [B.toNat_col_index hs.2.1 (by have := d.toNat_rows_le (mu := m.toUSize); lia)
              (by rw [hj]; exact hjn), hj]
            rfl)]
        · apply run_congr
          have hsub := iterRange_subCols (m := m) a
            (B.off + B.ld * (n - 1 - t.toNat)) (fun t' => B.off + B.ld * (n - 1 - t'))
            (fun t' => A.data[A.off + A.ld * (n - 1 - t') + (n - 1 - t.toNat)]!) 0
            (n - 1 - (n - 1 - t.toNat))
            (fun t' _ ht' i hi i' hi' => hcol _ (by lia) i hi i' hi')
          simp only [Nat.zero_add] at hsub
          rw [hr, USize.toNat_zero, hsub, modifyAt_rows _ _ d hmu,
            modifyAt_modifyAt _ _ (col_injOn _ _ _), trsmRightTUpperCol]
        · intro _ _ _ _
          rw [Mat.uget_eq_getElem, getElem_def]
          simp only [hj]
          rw [getElem!_pos A.data _ (A.index_lt hjn hjn)]
      · intro t' _ ht' next' a' h'
        rw [hr] at ht'
        have hk : (n.toUSize - 1 - t').toNat = n - 1 - t'.toNat := by grind
        have hkn : n - 1 - t'.toNat < n := by lia
        rw [Tail.run_forInFrom_unit (F := fun i c =>
            c.set! ((Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx i)
              (c[(Stride.mk (B.off + B.ld * (n - 1 - t.toNat)) 1).idx i]! -
                A.data[A.off + A.ld * (n - 1 - t'.toNat) + (n - 1 - t.toNat)]! *
                c[(Stride.mk (B.off + B.ld * (n - 1 - t'.toNat)) 1).idx i]!))
            (hF := by simp)]
        · apply run_congr
          rw [USize.toNat_zero, hmu,
            iterRange_set!_read _ _ _
              (fun i v w => v - A.data[A.off + A.ld * (n - 1 - t'.toNat) + (n - 1 - t.toNat)]! * w)
              (fun i _ hi i' _ hi' e => by
                simp only [Stride.idx, Nat.one_mul] at e
                exact hcol (n - 1 - t'.toNat) (by lia) i hi i' hi' e)]
          apply modifyAt_congr_fun
          intro i v _ _
          simp only [Stride.idx, Nat.one_mul]
        · intro i _ hi next'' a'' h''
          rw [hmu] at hi
          simp only [Tail.run_readThen, Tail.run_writeThen]
          apply run_set_eq_set!
          · rw [B.toNat_col_index hs.2.1 hi (by rw [hj]; exact hjn), hj]
            rfl
          · have h1 :=
              B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - t) (by rw [hj]; exact hjn)
            have h2 :=
              B.toNat_col_index hs.2.1 hi (j := n.toUSize - 1 - t') (by rw [hk]; exact hkn)
            simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, hj, hk, Stride.idx, Nat.one_mul]
            rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hjn),
              getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hkn),
              getElem!_pos A.data _ (A.index_lt hjn hkn)]
  · rfl

/-! ### The lower triangle -/

/-- The array of the solve of `Z * Aᵀ = B` for the lower triangle of `A`. -/
public def trsmRightTLowerData (d : Diag) (A : Mat n n) (B : Mat m n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ B.data.size < USize.size ∧ m < USize.size ∧
      n < USize.size then
    let mu := m.toUSize
    have hmu : mu.toNat = m := by grind
    let nu := n.toUSize
    have hnu : nu.toNat = n := by grind
    let b := B.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let bo := B.off.toUSize
    let bl := B.ld.toUSize
    (inplace b do
      for j in 0...nu do
        let cj := bo + bl * j
        for k in 0...j do
          let w := A.uget ao al rfl rfl hs.1 j k (by lia) (by lia)
          let ck := bo + bl * k
          for i in 0...mu do
            have hq : (cj + 1 * i).toNat < b.size := B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            have hq' : (ck + 1 * i).toNat < b.size :=
              B.toNat_col_index_lt hs.2.1 (by lia) (by lia)
            b[cj + 1 * i] := b[cj + 1 * i] - w * b[ck + 1 * i]
        let ajj := A.uget ao al rfl rfl hs.1 j j (by lia) (by lia)
        for i in 0...d.rows mu do
          have hq : (cj + 1 * i).toNat < b.size :=
            B.toNat_col_index_lt hs.2.1 (Nat.lt_of_lt_of_le (by assumption)
              (hmu ▸ d.toNat_rows_le)) (by lia)
          b[cj + 1 * i] := b[cj + 1 * i] / ajj).2
  else mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTLower d A B i j

/--
The value of column `j` of the lower solve from its old value `v`, with the columns before it.
-/
private def trsmRightTLowerG (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) (v : Float32) :
    Float32 :=
  d.apply (Nat.fold j (fun k _ s => s - A.data[A.off + A.ld * k + j]! * trsmRightTLower d A B i k)
    v) A.data[A.off + A.ld * j + j]!

private theorem trsmRightTLower_eq_G (d : Diag) (A : Mat n n) (B : Mat m n) (i j : Nat) :
    trsmRightTLower d A B i j = trsmRightTLowerG d A B i j B.data[B.off + B.ld * j + i]! := by
  rw [trsmRightTLower]; rfl

/-- The step of the lower solve for column `j`, on the array `c`. -/
private def trsmRightTLowerCol (d : Diag) (A : Mat n n) (B : Mat m n) (j : Nat)
    (c : Float32Array) : Float32Array :=
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

public theorem trsmRightTLowerData_eq (d : Diag) (A : Mat n n) (B : Mat m n) :
    trsmRightTLowerData d A B =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTLower d A B i j := by
  unfold trsmRightTLowerData
  split
  · rename_i hs
    have hmu : m.toUSize.toNat = m := by grind
    have hnu : n.toUSize.toNat = n := by grind
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsmRightTLowerCol d A B)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_trsmRightTLowerCol d A B (Nat.le_refl _)]
      apply mapMat_congr_getElem
      intro i j hi _ hj hq
      rw [trsmRightTLower_eq_G, getElem!_pos B.data _ hq]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hcol : ∀ k, k ≠ j.toNat → ∀ i, i < m → ∀ i', i' < m →
          B.off + B.ld * j.toNat + i ≠ B.off + B.ld * k + i' :=
        fun k hk i hi i' hi' => col_index_ne hi hi' B.le_ld (Ne.symm hk)
      rw [Tail.run_forInFrom_unit (F := fun k c =>
          c.modifyAt (Stride.mk (B.off + B.ld * j.toNat) 1).idx 0 m fun i v =>
            v - A.data[A.off + A.ld * k + j.toNat]! * c[B.off + B.ld * k + i]!)
          (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
      · rw [Tail.run_forInFrom_modify
          (G := fun _ v => v / A.data[A.off + A.ld * j.toNat + j.toNat]!)
          (idx := (Stride.mk (B.off + B.ld * j.toNat) 1).idx)
          (he := fun i _ hi => B.toNat_col_index hs.2.1
            (by have := d.toNat_rows_le (mu := m.toUSize); lia) hj)]
        · apply run_congr
          have hsub := iterRange_subCols (m := m) a
            (B.off + B.ld * j.toNat) (fun k => B.off + B.ld * k)
            (fun k => A.data[A.off + A.ld * k + j.toNat]!) 0 j.toNat
            (fun k _ hk i hi i' hi' => hcol k (by lia) i hi i' hi')
          simp only [Nat.zero_add] at hsub
          rw [USize.toNat_zero, hsub, modifyAt_rows _ _ d hmu,
            modifyAt_modifyAt _ _ (col_injOn _ _ _), trsmRightTLowerCol]
        · intro _ _ _ _
          rw [Mat.uget_eq_getElem, getElem_def,
            getElem!_pos A.data _ (A.index_lt hj hj)]
      · intro k _ hk next' a' h'
        have hkj : k.toNat < j.toNat := hk
        rw [Tail.run_forInFrom_unit (F := fun i c =>
            c.set! ((Stride.mk (B.off + B.ld * j.toNat) 1).idx i)
              (c[(Stride.mk (B.off + B.ld * j.toNat) 1).idx i]! -
                A.data[A.off + A.ld * k.toNat + j.toNat]! *
                c[(Stride.mk (B.off + B.ld * k.toNat) 1).idx i]!))
            (hF := by simp)]
        · apply run_congr
          rw [USize.toNat_zero, hmu,
            iterRange_set!_read _ _ _
              (fun i v w => v - A.data[A.off + A.ld * k.toNat + j.toNat]! * w)
              (fun i _ hi i' _ hi' e => by
                simp only [Stride.idx, Nat.one_mul] at e
                exact hcol k.toNat (by lia) i hi i' hi' e)]
          apply modifyAt_congr_fun
          intro i v _ _
          simp only [Stride.idx, Nat.one_mul]
        · intro i _ hi next'' a'' h''
          rw [hmu] at hi
          simp only [Tail.run_readThen, Tail.run_writeThen]
          apply run_set_eq_set!
          · exact B.toNat_col_index hs.2.1 hi hj
          · have h1 := B.toNat_col_index hs.2.1 hi hj
            have h2 := B.toNat_col_index hs.2.1 hi (Nat.lt_trans hkj hj)
            simp only [Mat.uget_eq_getElem, getElem_def, h1, h2, Stride.idx, Nat.one_mul]
            rw [getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi hj),
              getElem!_pos a'' _ (by rw [h'']; exact B.index_lt hi (Nat.lt_trans hkj hj)),
              getElem!_pos A.data _ (A.index_lt hj (Nat.lt_trans hkj hj))]
  · rfl

/-! ### `trsmRightT` -/

/-- The solution `Z` of `Z * Aᵀ = B` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trsmRightTSol (uplo : Uplo) (d : Diag) (A : Mat n n) (B : Mat m n) :
    Nat → Nat → Float32 :=
  match uplo with
  | .upper => trsmRightTUpper d A B
  | .lower => trsmRightTLower d A B

/--
The value of `trsmRightT` at `(i, j)`: `0` when `α = 0`, and `α` times the solution of
`Z * Aᵀ = B` otherwise.
-/
@[expose] public def trsmRightTAt (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) (i j : Nat) : Float32 :=
  if α == 0 then 0 else α * trsmRightTSol uplo d A B i j

/-- The array of the solve of `Z * Aᵀ = B`, before the scaling by `α`. -/
public def trsmRightTSolData (uplo : Uplo) (d : Diag) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
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
    (a : Float32Array) (h : a.size = B.data.size) : Mat m n where
  data := a
  off := off
  ld := ld
  le_ld := hl ▸ B.le_ld
  bound := by rw [h, ho, hl]; exact B.bound

/--
The array of `trsmRightT`. It takes the offset and the leading dimension of `B` before the solve,
so that `B` is not used after it, and the solve updates its array in place when it is not shared.
-/
public def trsmRightTData (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n) :
    Float32Array :=
  if α == 0 then B.scalBetaData 0
  else
    let off := B.off
    let ld := B.ld
    Mat.scalBetaData α (withData B off ld rfl rfl (trsmRightTSolData uplo d A B)
      (by rw [trsmRightTSolData_eq, size_mapMat]))

public theorem trsmRightTData_eq (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
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
    simp [trsmRightTAt, betaMul, hα, show ((0 : Float32) == 0) = true from rfl]

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
@[expose] public def trsmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : Mat m n where
  data := trsmRightTData uplo d α A B
  off := B.off
  ld := B.ld
  le_ld := B.le_ld
  bound := by rw [trsmRightTData_eq, size_mapMat]; exact B.bound

/-- The array of `trsmRightT uplo d α A B` is the array of `B` with its elements solved. -/
public theorem data_trsmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) :
    (trsmRightT uplo d α A B).data =
      mapMat B.data B.off B.ld m 0 n fun i j _ => trsmRightTAt uplo d α A B i j :=
  trsmRightTData_eq uplo d α A B

@[simp] public theorem off_trsmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : (trsmRightT uplo d α A B).off = B.off := rfl

@[simp] public theorem ld_trsmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) : (trsmRightT uplo d α A B).ld = B.ld := rfl

/-- Element `(i, j)` of `trsmRightT uplo d α A B` is element `(i, j)` of the model. -/
public theorem getElem_trsmRightT (uplo : Uplo) (d : Diag) (α : Float32) (A : Mat n n)
    (B : Mat m n) (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRightT uplo d α A B)[(i, j)] = trsmRightTAt uplo d α A B i j :=
  getElem_of_data_eq_mapMat _ (data_trsmRightT uplo d α A B) rfl rfl i j h

/--
Element `(i, j)` of `trsmRightT .upper d α A B` is `0` when `α = 0`, and otherwise `α * Z[i, j]`
for the solution `Z = trsmRightTUpper d A B` of `Z * Aᵀ = B`, which `trsmRightTUpper_eq` states.
-/
public theorem getElem_trsmRightT_upper (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRightT .upper d α A B)[(i, j)] =
      if α == 0 then 0 else α * trsmRightTUpper d A B i j :=
  getElem_trsmRightT _ _ _ _ _ _ _ h

/--
Element `(i, j)` of `trsmRightT .lower d α A B` is `0` when `α = 0`, and otherwise `α * Z[i, j]`
for the solution `Z = trsmRightTLower d A B` of `Z * Aᵀ = B`, which `trsmRightTLower_eq` states.
-/
public theorem getElem_trsmRightT_lower (d : Diag) (α : Float32) (A : Mat n n) (B : Mat m n)
    (i j : Nat) (h : i < m ∧ j < n) :
    (trsmRightT .lower d α A B)[(i, j)] =
      if α == 0 then 0 else α * trsmRightTLower d A B i j :=
  getElem_trsmRightT _ _ _ _ _ _ _ h

end Mat

end BLAS.Float32
