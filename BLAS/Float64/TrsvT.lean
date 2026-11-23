/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float64.Trsv
import all BLAS.Internal

/-!
# Transposed triangular solve

`Mat.trsvT uplo diag A x` solves `Aᵀ * y = x` for a triangular matrix `A`, over `x`, by the loops
of the reference BLAS for `TRANS = 'T'`. These loops are dot products: element `j` is `x[j]`, minus
the terms `A[i, j] * y[i]` of the elements of column `j` that are already solved, divided by
`A[j, j]` unless the diagonal is unit. Its specification is the recursive model `trsvTUpper` or
`trsvTLower`, which subtracts the terms in the order the loops do.
-/

open ScalarArray Float64Array InPlace

namespace BLAS.Float64

namespace Mat

variable {n : Nat}

/-! ## The models -/

/--
Element `j` of the solution of `Aᵀ * y = x` for the upper triangle of `A`, on the arrays: `x[j]`,
minus the terms `A[i, j] * y[i]` for `i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal
is unit.
-/
public def trsvTUpper (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float :=
  d.apply (Nat.fold j (fun i _hi s => s - A.data[A.off + A.ld * j + i]! * trsvTUpper d A x i)
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
termination_by j
decreasing_by exact _hi

/--
Element `j` of the solution of `Aᵀ * y = x` for the lower triangle of `A`, on the arrays: `x[j]`,
minus the terms `A[i, j] * y[i]` for `i = n - 1, …, j + 1`, divided by `A[j, j]` unless the
diagonal is unit.
-/
public def trsvTLower (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (n - 1 - t)]! * trsvTLower d A x (n - 1 - t))
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/--
Element `j < n` of the solution of `Aᵀ * y = x` for the upper triangle of `A` is `x[j]`, minus the
terms `A[i, j] * y[i]` for `i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal is unit.
-/
public theorem trsvTUpper_eq (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (h : j < n) :
    trsvTUpper d A x j =
      d.apply (Nat.fold j (fun i hi s => s - A[(i, j)]'⟨by lia, h⟩ * trsvTUpper d A x i) x[j])
        A[(j, j)] := by
  rw [trsvTUpper, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext i hi s
  rw [getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
Element `j < n` of the solution of `Aᵀ * y = x` for the lower triangle of `A` is `x[j]`, minus the
terms `A[i, j] * y[i]` for `i = n - 1, …, j + 1`, divided by `A[j, j]` unless the diagonal is
unit.
-/
public theorem trsvTLower_eq (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (h : j < n) :
    trsvTLower d A x j =
      d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
          s - A[(n - 1 - t, j)]'⟨by lia, h⟩ * trsvTLower d A x (n - 1 - t)) x[j])
        A[(j, j)] := by
  rw [trsvTLower, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/-! ## The loops -/

/--
A loop whose step `i` only maps its variable, by `g i` with the array `a`, leaves `a` unchanged and
maps the variable by a fold.
-/
theorem iterRange_fst (g : Nat → Float64Array → Float → Float) (k : Nat) (t : Float)
    (a : Float64Array) :
    iterRange (fun i p => (g i p.2 p.1, p.2)) 0 k (t, a) =
      (Nat.fold k (fun i _ s => g i a s) t, a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterRange_succ _ (Nat.zero_le _), ih, Nat.fold_succ]

/-- The step `j` of the upper solve: solve for element `j` from the elements above it. -/
@[expose] public def trsvTUpperStep (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat)
    (b : Float64Array) : Float64Array :=
  let t := d.apply (Nat.fold j (fun i _ s =>
      s - A.data[A.off + A.ld * j + i]! * b[x.off + x.inc * i]!) b[x.off + x.inc * j]!)
    A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-!
### Four elements per pass

The steps of both solves have one shape: step `k` solves element `π k` from the elements `π t`,
`t < k`, solved before it, where `π k = k` for the upper triangle and `π k = n - 1 - k` for the
lower one. Four consecutive steps share the terms of the elements solved before the first of them,
so they can compute those four dot products together, then finish each element in order.
-/

/-- The value of the step `k` of a solve in the order `π`, on the array `b`. -/
private def solveVal (d : Diag) (A : Mat n n) (x : Vec n) (π : Nat → Nat) (k : Nat)
    (b : Float64Array) : Float :=
  d.apply (Nat.fold k (fun t _ s =>
      s - A.data[A.off + A.ld * π k + π t]! * b[x.off + x.inc * π t]!) b[x.off + x.inc * π k]!)
    A.data[A.off + A.ld * π k + π k]!

/-- The dot product of the step `k + r` over the steps before `k`, on the array `b`. -/
private def solvePre (A : Mat n n) (x : Vec n) (π : Nat → Nat) (k r : Nat) (b : Float64Array) :
    Float :=
  Nat.fold k (fun t _ s => s - A.data[A.off + A.ld * π (k + r) + π t]! * b[x.off + x.inc * π t]!)
    b[x.off + x.inc * π (k + r)]!

/--
Four steps of a solve in the order `π` from `k`: the four dot products over the elements of the
steps before `k`, then the solve of each element with the terms of the elements of the four solved
before it.
-/
private theorem iterRange_solve_four (d : Diag) (A : Mat n n) (x : Vec n) (π : Nat → Nat)
    (hπ : ∀ k, k < n → π k < n) (hinj : ∀ k k', k < n → k' < n → k ≠ k' → π k ≠ π k')
    {k : Nat} (hk : k + 3 < n) (b : Float64Array) (hb : b.size = x.data.size) :
    iterRange (fun k b => b.set! (x.off + x.inc * π k) (solveVal d A x π k b)) k (k + 4) b =
      let w := fun k t => A.data[A.off + A.ld * π k + π t]!
      let D := fun k v => d.apply v A.data[A.off + A.ld * π k + π k]!
      let y₀ := D k (solvePre A x π k 0 b)
      let y₁ := D (k + 1) (solvePre A x π k 1 b - w (k + 1) k * y₀)
      let y₂ := D (k + 2) ((solvePre A x π k 2 b - w (k + 2) k * y₀) - w (k + 2) (k + 1) * y₁)
      let y₃ := D (k + 3) (((solvePre A x π k 3 b - w (k + 3) k * y₀) -
        w (k + 3) (k + 1) * y₁) - w (k + 3) (k + 2) * y₂)
      (((b.set! (x.off + x.inc * π k) y₀).set! (x.off + x.inc * π (k + 1)) y₁).set!
        (x.off + x.inc * π (k + 2)) y₂).set! (x.off + x.inc * π (k + 3)) y₃ := by
  rw [iterRange_of_lt _ (by lia), iterRange_of_lt _ (by lia), iterRange_of_lt _ (by lia),
    iterRange_of_lt _ (by lia), iterRange_of_le _ (by lia)]
  have rd : ∀ (c : Float64Array) (q t : Nat) (v : Float), t < n → q < n → t ≠ q →
      (c.set! (x.off + x.inc * π q) v)[x.off + x.inc * π t]! = c[x.off + x.inc * π t]! :=
    fun c q t v ht hq h =>
      getElem!_set!_ne c v (idx_ne_of_ne x.inc_pos (hπ q hq) (hπ t ht) (hinj q t hq ht (Ne.symm h)))
  have rs : ∀ (c : Float64Array) (q : Nat) (v : Float), q < n → c.size = x.data.size →
      (c.set! (x.off + x.inc * π q) v)[x.off + x.inc * π q]! = v :=
    fun c q v hq h => by
      rw [getElem!_set!_of_lt _ _ _ (by simpa [h] using x.index_lt (hπ q hq)), ite_eq_left rfl]
  have pre : ∀ (r : Nat) (c : Float64Array),
      (∀ t, t < k → c[x.off + x.inc * π t]! = b[x.off + x.inc * π t]!) →
      c[x.off + x.inc * π (k + r)]! = b[x.off + x.inc * π (k + r)]! →
      Nat.fold k (fun t _ s =>
          s - A.data[A.off + A.ld * π (k + r) + π t]! * c[x.off + x.inc * π t]!)
        c[x.off + x.inc * π (k + r)]! = solvePre A x π k r b := by
    intro r c hc hr
    rw [solvePre, hr]
    congr 1
    funext t ht s
    rw [hc t ht]
  have v₀ : solveVal d A x π k b = d.apply (solvePre A x π k 0 b)
      A.data[A.off + A.ld * π k + π k]! := rfl
  simp only [v₀]
  generalize d.apply (solvePre A x π k 0 b) A.data[A.off + A.ld * π k + π k]! = y₀
  have v₁ : solveVal d A x π (k + 1) (b.set! (x.off + x.inc * π k) y₀) =
      d.apply (solvePre A x π k 1 b - A.data[A.off + A.ld * π (k + 1) + π k]! * y₀)
        A.data[A.off + A.ld * π (k + 1) + π (k + 1)]! := by
    rw [solveVal, Nat.fold_succ, pre 1 _ (fun t ht => by simp (disch := lia) only [rd])
      (by simp (disch := lia) only [rd])]
    simp (disch := first | lia | simp [hb]) only [rs]
  rw [v₁]
  generalize d.apply (solvePre A x π k 1 b - A.data[A.off + A.ld * π (k + 1) + π k]! * y₀)
      A.data[A.off + A.ld * π (k + 1) + π (k + 1)]! = y₁
  have v₂ : solveVal d A x π (k + 2)
        ((b.set! (x.off + x.inc * π k) y₀).set! (x.off + x.inc * π (k + 1)) y₁) =
      d.apply ((solvePre A x π k 2 b - A.data[A.off + A.ld * π (k + 2) + π k]! * y₀) -
          A.data[A.off + A.ld * π (k + 2) + π (k + 1)]! * y₁)
        A.data[A.off + A.ld * π (k + 2) + π (k + 2)]! := by
    rw [solveVal, show k + 2 = k + 1 + 1 by lia, Nat.fold_succ, Nat.fold_succ,
      show k + 1 + 1 = k + 2 by lia]
    rw [pre 2 _ (fun t ht => by simp (disch := lia) only [rd])
      (by simp (disch := lia) only [rd])]
    simp (disch := first | lia | simp [hb]) only [rd, rs]
  rw [v₂]
  generalize d.apply ((solvePre A x π k 2 b - A.data[A.off + A.ld * π (k + 2) + π k]! * y₀) -
      A.data[A.off + A.ld * π (k + 2) + π (k + 1)]! * y₁)
    A.data[A.off + A.ld * π (k + 2) + π (k + 2)]! = y₂
  have v₃ : solveVal d A x π (k + 3)
        (((b.set! (x.off + x.inc * π k) y₀).set! (x.off + x.inc * π (k + 1)) y₁).set!
          (x.off + x.inc * π (k + 2)) y₂) =
      d.apply (((solvePre A x π k 3 b - A.data[A.off + A.ld * π (k + 3) + π k]! * y₀) -
          A.data[A.off + A.ld * π (k + 3) + π (k + 1)]! * y₁) -
          A.data[A.off + A.ld * π (k + 3) + π (k + 2)]! * y₂)
        A.data[A.off + A.ld * π (k + 3) + π (k + 3)]! := by
    rw [solveVal, show k + 3 = k + 2 + 1 by lia, Nat.fold_succ, show k + 2 = k + 1 + 1 by lia,
      Nat.fold_succ, Nat.fold_succ, show k + 1 + 1 = k + 2 by lia,
      show k + 2 + 1 = k + 3 by lia]
    rw [pre 3 _ (fun t ht => by simp (disch := lia) only [rd])
      (by simp (disch := lia) only [rd])]
    simp (disch := first | lia | simp [hb]) only [rd, rs]
  rw [v₃]

private theorem trsvTUpperStep_eq_solve (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTUpperStep d A x =
      fun k b => b.set! (x.off + x.inc * k) (solveVal d A x (fun k => k) k b) := by
  funext k b
  rw [trsvTUpperStep, modifyAt_of_lt _ _ (Nat.lt_succ_self k), modifyAt_self, Vec.idx_stride]
  rfl

/-- The array of the upper solve: four elements per pass, then the rest one at a time. -/
public def trsvTUpperData (d : Diag) (A : Mat n n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let q4 := nu / 4
    have hq4 : q4.toNat = n / 4 := by simp only [q4, USize.toNat_div, hnu]; simp
    inplace a do
      for g in 0...q4 do
        have e₀ : (4 * g).toNat = 4 * g.toNat := by grind
        have e₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
        have e₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
        have e₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
        have k₀ : (o + c * (4 * g)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₁ : (o + c * (4 * g + 1)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₂ : (o + c * (4 * g + 2)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₃ : (o + c * (4 * g + 3)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        let v₀ := a[o + c * (4 * g)]
        let v₁ := a[o + c * (4 * g + 1)]
        let v₂ := a[o + c * (4 * g + 2)]
        let v₃ := a[o + c * (4 * g + 3)]
        for i in 0...4 * g with (s₀ := v₀) (s₁ := v₁) (s₂ := v₂) (s₃ := v₃) do
          have hi : (o + c * i).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
          let y := a[o + c * i]
          s₀ := s₀ - A.uget ao al rfl rfl hs.1 i (4 * g) (by lia) (by lia) * y
          s₁ := s₁ - A.uget ao al rfl rfl hs.1 i (4 * g + 1) (by lia) (by lia) * y
          s₂ := s₂ - A.uget ao al rfl rfl hs.1 i (4 * g + 2) (by lia) (by lia) * y
          s₃ := s₃ - A.uget ao al rfl rfl hs.1 i (4 * g + 3) (by lia) (by lia) * y
        let y₀ := d.apply s₀ (A.uget ao al rfl rfl hs.1 (4 * g) (4 * g) (by lia) (by lia))
        a[o + c * (4 * g)] := y₀
        let y₁ := d.apply
          (s₁ - A.uget ao al rfl rfl hs.1 (4 * g) (4 * g + 1) (by lia) (by lia) * y₀)
          (A.uget ao al rfl rfl hs.1 (4 * g + 1) (4 * g + 1) (by lia) (by lia))
        a[o + c * (4 * g + 1)] := y₁
        let y₂ := d.apply ((s₂ -
            A.uget ao al rfl rfl hs.1 (4 * g) (4 * g + 2) (by lia) (by lia) * y₀) -
            A.uget ao al rfl rfl hs.1 (4 * g + 1) (4 * g + 2) (by lia) (by lia) * y₁)
          (A.uget ao al rfl rfl hs.1 (4 * g + 2) (4 * g + 2) (by lia) (by lia))
        a[o + c * (4 * g + 2)] := y₂
        let y₃ := d.apply (((s₃ -
            A.uget ao al rfl rfl hs.1 (4 * g) (4 * g + 3) (by lia) (by lia) * y₀) -
            A.uget ao al rfl rfl hs.1 (4 * g + 1) (4 * g + 3) (by lia) (by lia) * y₁) -
            A.uget ao al rfl rfl hs.1 (4 * g + 2) (4 * g + 3) (by lia) (by lia) * y₂)
          (A.uget ao al rfl rfl hs.1 (4 * g + 3) (4 * g + 3) (by lia) (by lia))
        a[o + c * (4 * g + 3)] := y₃
      for j in 4 * q4...nu do
        have hk : (o + c * j).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        let v := a[o + c * j]
        for i in 0...j with (t := v) do
          have hi : (o + c * i).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
          t := t - A.uget ao al rfl rfl hs.1 i j (by lia) (by lia) * a[o + c * i]
        a[o + c * j] := d.apply t (A.uget ao al rfl rfl hs.1 j j (by lia) (by lia))
  else iterRange (trsvTUpperStep d A x) 0 n x.data

public theorem trsvTUpperData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTUpperData d A x = iterRange (trsvTUpperStep d A x) 0 n x.data := by
  unfold trsvTUpperData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hq4 : (n.toUSize / 4).toNat = n / 4 := by simp only [USize.toNat_div, hnu]; simp
    have h4q : (4 * (n.toUSize / 4)).toNat = 4 * (n / 4) := by grind
    have hF : ∀ j (b : Float64Array), (trsvTUpperStep d A x j b).size = b.size :=
      fun _ _ => size_modifyAt _ _ _ _ _
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit
      (F := fun g b => iterRange (trsvTUpperStep d A x) (4 * g) (4 * g + 4) b)
      (hF := fun _ _ => size_iterRange _ hF _ _ _)]
    · rw [Tail.run_forInFrom_unit (F := trsvTUpperStep d A x) (hF := hF)]
      · simp only [Tail.run_done, hq4, h4q, hnu, USize.toNat_zero]
        rw [iterRange_four, ← iterRange_split _ (Nat.zero_le _) (by lia)]
      · intro j hl hj next a h
        rw [hnu] at hj
        rw [h4q] at hl
        simp only [Tail.run_readThen]
        rw [Tail.run_forInFrom (f := fun i p =>
            (p.1 - A.data[A.off + A.ld * j.toNat + i]! * p.2[x.off + x.inc * i]!, p.2))
          (hf := fun _ _ => rfl)]
        · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun i a s =>
            s - A.data[A.off + A.ld * j.toNat + i]! * a[x.off + x.inc * i]!)]
          congr 1
          have hp := x.toNat_index hs.2 hj
          rw [trsvTUpperStep,
            ← set_eq_modifyAt _ _ _ _ (by rw [Vec.idx_stride, h]; exact x.index_lt hj)]
          simp only [hp, Vec.idx_stride, uget_eq_getElem, getElem_def,
            getElem!_pos a (x.off + x.inc * j.toNat)
              (show _ < a.size by rw [h]; exact x.index_lt hj),
            getElem!_pos A.data (A.off + A.ld * j.toNat + j.toNat) (A.index_lt hj hj)]
        · intro i _ hi next' b a' h'
          simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
          have hp := x.toNat_index hs.2 (Nat.lt_trans hi hj)
          simp only [hp, getElem!_pos a' (x.off + x.inc * i.toNat)
              (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
            getElem!_pos A.data (A.off + A.ld * j.toNat + i.toNat) (A.index_lt (by lia) hj)]
    · intro g _ hg next a h
      rw [hq4] at hg
      have e₀ : (4 * g).toNat = 4 * g.toNat := by grind
      have e₁ : (4 * g + 1).toNat = 4 * g.toNat + 1 := by grind
      have e₂ : (4 * g + 2).toNat = 4 * g.toNat + 2 := by grind
      have e₃ : (4 * g + 3).toNat = 4 * g.toNat + 3 := by grind
      have t₀ := x.toNat_index hs.2 (i := 4 * g) (by lia)
      have t₁ := x.toNat_index hs.2 (i := 4 * g + 1) (by lia)
      have t₂ := x.toNat_index hs.2 (i := 4 * g + 2) (by lia)
      have t₃ := x.toNat_index hs.2 (i := 4 * g + 3) (by lia)
      rw [e₀] at t₀
      rw [e₁] at t₁
      rw [e₂] at t₂
      rw [e₃] at t₃
      have hb : a.size = x.data.size := h
      simp only [Tail.run_readThen, Tail.forIn4_eq]
      rw [run_forIn4From_read
        (f₀ := fun i s => s - A.data[A.off + A.ld * (4 * g.toNat) + i]! * a[x.off + x.inc * i]!)
        (f₁ := fun i s => s - A.data[A.off + A.ld * (4 * g.toNat + 1) + i]! *
          a[x.off + x.inc * i]!)
        (f₂ := fun i s => s - A.data[A.off + A.ld * (4 * g.toNat + 2) + i]! *
          a[x.off + x.inc * i]!)
        (f₃ := fun i s => s - A.data[A.off + A.ld * (4 * g.toNat + 3) + i]! *
          a[x.off + x.inc * i]!)]
      · simp only [Tail.run_writeThen, USize.toNat_zero, e₀, iterRange_eq_fold]
        apply run_congr
        rw [trsvTUpperStep_eq_solve, iterRange_solve_four d A x (fun k => k) (fun _ h => h)
          (fun _ _ _ _ h => h) (by lia) a hb]
        simp only [solvePre, t₀, t₁, t₂, t₃, set_eq_set!, getElem_eq_getElem!,
          uget_eq_getElem, getElem_def, e₀, e₁, e₂, e₃, Nat.add_zero]
      · intro i _ hi next' s₀ s₁ s₂ s₃
        have hp := x.toNat_index hs.2 (i := i) (by lia)
        simp only [Tail.run_readThen, hp, getElem_eq_getElem!, uget_eq_getElem, getElem_def, e₀,
          e₁, e₂, e₃]
  · rfl

/-- After the steps `i < j`, the elements `i < j` are solved, and the others are unchanged. -/
theorem iterRange_trsvTUpperStep (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (hj : j ≤ n) :
    iterRange (trsvTUpperStep d A x) 0 j x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v => if i < j then trsvTUpper d A x i else v := by
  induction j with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ _
    simp
  | succ j ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, i ≤ j → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if i < j then trsvTUpper d A x i else v)[x.off + x.inc * i]! =
        if i < j then trsvTUpper d A x i else x.data[x.off + x.inc * i]! := by
      intro i hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt (by lia : i < n)),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) (by lia),
        getElem!_pos x.data _ (x.index_lt (by lia))]
    have ht : d.apply (Nat.fold j (fun i _ s => s - A.data[A.off + A.ld * j + i]! *
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if i < j then trsvTUpper d A x i else v)[x.off + x.inc * i]!)
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if i < j then trsvTUpper d A x i else v)[x.off + x.inc * j]!)
          A.data[A.off + A.ld * j + j]! = trsvTUpper d A x j := by
      rw [hr j (Nat.le_refl _), ite_eq_right (Nat.lt_irrefl j), trsvTUpper]
      congr 2
      funext i hi s
      rw [hr i (by lia), ite_eq_left hi]
    simp only [trsvTUpperStep, ht]
    rw [modifyAt_widen (lo := j) (hi := j + 1) (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _)
      (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : i < j
    · simp [h₁, show i < j + 1 by lia, show ¬j ≤ i by lia]
    · by_cases h₂ : i = j
      · subst h₂; simp
      · simp [h₁, show ¬i < j + 1 by lia]

/-- The array of the upper solve is the array of `x` with its elements solved. -/
public theorem trsvTUpperData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTUpperData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTUpper d A x i := by
  rw [trsvTUpperData_eq_iterRange, iterRange_trsvTUpperStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp [hi]

/-! ## The lower triangle -/

/--
The step `k` of the lower solve: solve for element `j = n - 1 - k` from the elements below it.
-/
@[expose] public def trsvTLowerStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float64Array) : Float64Array :=
  let j := n - 1 - k
  let t := d.apply (Nat.fold k (fun t _ s =>
      s - A.data[A.off + A.ld * j + (n - 1 - t)]! * b[x.off + x.inc * (n - 1 - t)]!)
      b[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

private theorem trsvTLowerStep_eq_solve (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerStep d A x =
      fun k b =>
        b.set! (x.off + x.inc * (n - 1 - k)) (solveVal d A x (fun k => n - 1 - k) k b) := by
  funext k b
  rw [trsvTLowerStep, modifyAt_of_lt _ _ (Nat.lt_succ_self _), modifyAt_self, Vec.idx_stride]
  rfl

/-- The array of the lower solve: four elements per pass, then the rest one at a time. -/
public def trsvTLowerData (d : Diag) (A : Mat n n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let q4 := nu / 4
    have hq4 : q4.toNat = n / 4 := by simp only [q4, USize.toNat_div, hnu]; simp
    inplace a do
      for g in 0...q4 do
        have j₀ : (nu - 1 - 4 * g).toNat = n - 1 - 4 * g.toNat := by grind
        have j₁ : (nu - 1 - (4 * g + 1)).toNat = n - 1 - (4 * g.toNat + 1) := by grind
        have j₂ : (nu - 1 - (4 * g + 2)).toNat = n - 1 - (4 * g.toNat + 2) := by grind
        have j₃ : (nu - 1 - (4 * g + 3)).toNat = n - 1 - (4 * g.toNat + 3) := by grind
        have k₀ : (o + c * (nu - 1 - 4 * g)).toNat < a.size := x.toNat_index_lt hs.2 (by lia)
        have k₁ : (o + c * (nu - 1 - (4 * g + 1))).toNat < a.size :=
          x.toNat_index_lt hs.2 (by lia)
        have k₂ : (o + c * (nu - 1 - (4 * g + 2))).toNat < a.size :=
          x.toNat_index_lt hs.2 (by lia)
        have k₃ : (o + c * (nu - 1 - (4 * g + 3))).toNat < a.size :=
          x.toNat_index_lt hs.2 (by lia)
        let v₀ := a[o + c * (nu - 1 - 4 * g)]
        let v₁ := a[o + c * (nu - 1 - (4 * g + 1))]
        let v₂ := a[o + c * (nu - 1 - (4 * g + 2))]
        let v₃ := a[o + c * (nu - 1 - (4 * g + 3))]
        for t in 0...4 * g with (s₀ := v₀) (s₁ := v₁) (s₂ := v₂) (s₃ := v₃) do
          have ht : (nu - 1 - t).toNat < n := by grind
          have hi : (o + c * (nu - 1 - t)).toNat < a.size := x.toNat_index_lt hs.2 ht
          let y := a[o + c * (nu - 1 - t)]
          s₀ := s₀ - A.uget ao al rfl rfl hs.1 (nu - 1 - t) (nu - 1 - 4 * g) ht (by lia) * y
          s₁ := s₁ - A.uget ao al rfl rfl hs.1 (nu - 1 - t) (nu - 1 - (4 * g + 1)) ht (by lia) * y
          s₂ := s₂ - A.uget ao al rfl rfl hs.1 (nu - 1 - t) (nu - 1 - (4 * g + 2)) ht (by lia) * y
          s₃ := s₃ - A.uget ao al rfl rfl hs.1 (nu - 1 - t) (nu - 1 - (4 * g + 3)) ht (by lia) * y
        let y₀ := d.apply s₀
          (A.uget ao al rfl rfl hs.1 (nu - 1 - 4 * g) (nu - 1 - 4 * g) (by lia) (by lia))
        a[o + c * (nu - 1 - 4 * g)] := y₀
        let y₁ := d.apply (s₁ - A.uget ao al rfl rfl hs.1 (nu - 1 - 4 * g) (nu - 1 - (4 * g + 1))
            (by lia) (by lia) * y₀)
          (A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 1)) (nu - 1 - (4 * g + 1)) (by lia)
            (by lia))
        a[o + c * (nu - 1 - (4 * g + 1))] := y₁
        let y₂ := d.apply ((s₂ -
            A.uget ao al rfl rfl hs.1 (nu - 1 - 4 * g) (nu - 1 - (4 * g + 2)) (by lia) (by lia) *
              y₀) -
            A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 1)) (nu - 1 - (4 * g + 2)) (by lia)
              (by lia) * y₁)
          (A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 2)) (nu - 1 - (4 * g + 2)) (by lia)
            (by lia))
        a[o + c * (nu - 1 - (4 * g + 2))] := y₂
        let y₃ := d.apply (((s₃ -
            A.uget ao al rfl rfl hs.1 (nu - 1 - 4 * g) (nu - 1 - (4 * g + 3)) (by lia) (by lia) *
              y₀) -
            A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 1)) (nu - 1 - (4 * g + 3)) (by lia)
              (by lia) * y₁) -
            A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 2)) (nu - 1 - (4 * g + 3)) (by lia)
              (by lia) * y₂)
          (A.uget ao al rfl rfl hs.1 (nu - 1 - (4 * g + 3)) (nu - 1 - (4 * g + 3)) (by lia)
            (by lia))
        a[o + c * (nu - 1 - (4 * g + 3))] := y₃
      for k in 4 * q4...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        for t in 0...k with (s := v) do
          have hi : (nu - 1 - t).toNat < n := by grind
          have hk' : (o + c * (nu - 1 - t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s - A.uget ao al rfl rfl hs.1 (nu - 1 - t) (nu - 1 - k) hi hjn *
            a[o + c * (nu - 1 - t)]
        a[o + c * (nu - 1 - k)] :=
          d.apply s (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)
  else iterRange (trsvTLowerStep d A x) 0 n x.data

public theorem trsvTLowerData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerData d A x = iterRange (trsvTLowerStep d A x) 0 n x.data := by
  unfold trsvTLowerData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    have hq4 : (n.toUSize / 4).toNat = n / 4 := by simp only [USize.toNat_div, hnu]; simp
    have h4q : (4 * (n.toUSize / 4)).toNat = 4 * (n / 4) := by grind
    have hF : ∀ j (b : Float64Array), (trsvTLowerStep d A x j b).size = b.size :=
      fun _ _ => size_modifyAt _ _ _ _ _
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit
      (F := fun g b => iterRange (trsvTLowerStep d A x) (4 * g) (4 * g + 4) b)
      (hF := fun _ _ => size_iterRange _ hF _ _ _)]
    · rw [Tail.run_forInFrom_unit (F := trsvTLowerStep d A x) (hF := hF)]
      · simp only [Tail.run_done, hq4, h4q, hnu, USize.toNat_zero]
        rw [iterRange_four, ← iterRange_split _ (Nat.zero_le _) (by lia)]
      · intro k hl hk next a h
        rw [hnu] at hk
        have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
        simp only [Tail.run_readThen]
        rw [Tail.run_forInFrom (f := fun t p =>
            (p.1 - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - t)]! *
              p.2[x.off + x.inc * (n - 1 - t)]!, p.2))
          (hf := fun _ _ => rfl)]
        · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun t a s =>
            s - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - t)]! *
              a[x.off + x.inc * (n - 1 - t)]!)]
          congr 1
          have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
              x.off + x.inc * (n - 1 - k.toNat) := by
            rw [x.toNat_index hs.2 (by lia), hj]
          rw [trsvTLowerStep, ← set_eq_modifyAt _ _ _ _
            (by rw [Vec.idx_stride, h]; exact x.index_lt (by lia))]
          simp only [hp, hj, Vec.idx_stride, uget_eq_getElem, getElem_def,
            getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
              (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
            getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
              (A.index_lt (by lia) (by lia))]
        · intro t _ ht next' b a' h'
          simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
          have hi : (n.toUSize - 1 - t).toNat = n - 1 - t.toNat := by grind
          have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - t)).toNat =
              x.off + x.inc * (n - 1 - t.toNat) := by
            rw [x.toNat_index hs.2 (by lia), hi]
          simp only [hp, hi, hj, getElem!_pos a' (x.off + x.inc * (n - 1 - t.toNat))
              (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
            getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - t.toNat))
              (A.index_lt (by lia) (by lia))]
    · intro g _ hg next a h
      rw [hq4] at hg
      have e₀ : (4 * g).toNat = 4 * g.toNat := by grind
      have hg4 : 4 * g.toNat + 3 < n := by lia
      have hn : n < USize.size := Nat.lt_of_le_of_lt x.le_size hs.2
      have j₀ : (n.toUSize - 1 - 4 * g).toNat = n - 1 - 4 * g.toNat := by grind
      have j₁ : (n.toUSize - 1 - (4 * g + 1)).toNat = n - 1 - (4 * g.toNat + 1) := by grind
      have j₂ : (n.toUSize - 1 - (4 * g + 2)).toNat = n - 1 - (4 * g.toNat + 2) := by grind
      have j₃ : (n.toUSize - 1 - (4 * g + 3)).toNat = n - 1 - (4 * g.toNat + 3) := by grind
      have t₀ := x.toNat_index hs.2 (i := n.toUSize - 1 - 4 * g) (by lia)
      have t₁ := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 1)) (by lia)
      have t₂ := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 2)) (by lia)
      have t₃ := x.toNat_index hs.2 (i := n.toUSize - 1 - (4 * g + 3)) (by lia)
      rw [j₀] at t₀
      rw [j₁] at t₁
      rw [j₂] at t₂
      rw [j₃] at t₃
      have hb : a.size = x.data.size := h
      simp only [Tail.run_readThen, Tail.forIn4_eq]
      rw [run_forIn4From_read
        (f₀ := fun t s => s - A.data[A.off + A.ld * (n - 1 - 4 * g.toNat) + (n - 1 - t)]! *
          a[x.off + x.inc * (n - 1 - t)]!)
        (f₁ := fun t s => s - A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 1)) + (n - 1 - t)]! *
          a[x.off + x.inc * (n - 1 - t)]!)
        (f₂ := fun t s => s - A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 2)) + (n - 1 - t)]! *
          a[x.off + x.inc * (n - 1 - t)]!)
        (f₃ := fun t s => s - A.data[A.off + A.ld * (n - 1 - (4 * g.toNat + 3)) + (n - 1 - t)]! *
          a[x.off + x.inc * (n - 1 - t)]!)]
      · simp only [Tail.run_writeThen, USize.toNat_zero, e₀, iterRange_eq_fold]
        apply run_congr
        rw [trsvTLowerStep_eq_solve, iterRange_solve_four d A x (fun k => n - 1 - k)
          (fun _ _ => by lia) (fun _ _ _ _ h => by lia) (by lia) a hb]
        simp only [solvePre, t₀, t₁, t₂, t₃, set_eq_set!, getElem_eq_getElem!,
          uget_eq_getElem, getElem_def, j₀, j₁, j₂, j₃, Nat.add_zero]
      · intro t _ ht next' s₀ s₁ s₂ s₃
        have hi : (n.toUSize - 1 - t).toNat = n - 1 - t.toNat := by grind
        have hp := x.toNat_index hs.2 (i := n.toUSize - 1 - t) (by lia)
        rw [hi] at hp
        simp only [Tail.run_readThen, hp, hi, getElem_eq_getElem!, uget_eq_getElem, getElem_def,
          j₀, j₁, j₂, j₃]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are solved, and the others are unchanged.
-/
theorem iterRange_trsvTLowerStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat} (hk : k ≤ n) :
    iterRange (trsvTLowerStep d A x) 0 k x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v =>
        if n - k ≤ i then trsvTLower d A x i else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, n - 1 - k ≤ i → i < n → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trsvTLower d A x i else v)[x.off + x.inc * i]! =
        if n - k ≤ i then trsvTLower d A x i else x.data[x.off + x.inc * i]! := by
      intro i _ hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt hi),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) hi,
        getElem!_pos x.data _ (x.index_lt hi)]
    have ht : d.apply (Nat.fold k (fun t _ s =>
          s - A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - t)]! *
            (x.data.modifyAt x.stride.idx 0 n fun i v =>
              if n - k ≤ i then trsvTLower d A x i else v)[x.off + x.inc * (n - 1 - t)]!)
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if n - k ≤ i then trsvTLower d A x i else v)[x.off + x.inc * (n - 1 - k)]!)
          A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]! = trsvTLower d A x (n - 1 - k) := by
      rw [hr (n - 1 - k) (Nat.le_refl _) (by lia), ite_eq_right (by lia),
        trsvTLower.eq_1 d A x (n - 1 - k), Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
      congr 2
      funext t ht s
      rw [hr (n - 1 - t) (by lia) (by lia), ite_eq_left (by lia)]
    simp only [trsvTLowerStep, ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _
      (Nat.zero_le _) (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/-- The array of the lower solve is the array of `x` with its elements solved. -/
public theorem trsvTLowerData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerData d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTLower d A x i := by
  rw [trsvTLowerData_eq_iterRange, iterRange_trsvTLowerStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-! ## The lower triangle, with the terms in increasing order -/

/-!
The reference `trsm` solves `Aᵀ * X = α * B` for a lower triangle with the loops of `trsv`, except
that it subtracts the terms of element `j` in increasing order, `i = j + 1, …, n - 1`, where `trsv`
subtracts them from `i = n - 1` down. `trsvTLowerAsc` is that solve, for the columns of `trsmT`.
-/

/--
Element `j` of the solution of `Aᵀ * y = x` for the lower triangle of `A`, on the arrays: `x[j]`,
minus the terms `A[i, j] * y[i]` for `i = j + 1, …, n - 1`, divided by `A[j, j]` unless the
diagonal is unit.
-/
public def trsvTLowerAsc (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) : Float :=
  d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * trsvTLowerAsc d A x (j + 1 + t))
    x.data[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
termination_by n - j
decreasing_by lia

/--
Element `j < n` of `trsvTLowerAsc d A x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = j + 1, …, n - 1`, divided by `A[j, j]` unless the diagonal is unit.
-/
public theorem trsvTLowerAsc_eq (d : Diag) (A : Mat n n) (x : Vec n) {j : Nat} (h : j < n) :
    trsvTLowerAsc d A x j =
      d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
          s - A[(j + 1 + t, j)]'⟨by lia, h⟩ * trsvTLowerAsc d A x (j + 1 + t)) x[j])
        A[(j, j)] := by
  rw [trsvTLowerAsc, getElem!_pos x.data _ (x.index_lt h), getElem!_pos A.data _ (A.index_lt h h)]
  congr
  funext t ht s
  rw [getElem!_pos A.data _ (A.index_lt (by lia) h)]
  rfl

/--
The step `k` of the lower solve in increasing order: solve for element `j = n - 1 - k` from the
elements below it.
-/
@[expose] public def trsvTLowerAscStep (d : Diag) (A : Mat n n) (x : Vec n) (k : Nat)
    (b : Float64Array) : Float64Array :=
  let j := n - 1 - k
  let t := d.apply (Nat.fold k (fun t _ s =>
      s - A.data[A.off + A.ld * j + (j + 1 + t)]! * b[x.off + x.inc * (j + 1 + t)]!)
      b[x.off + x.inc * j]!) A.data[A.off + A.ld * j + j]!
  b.modifyAt x.stride.idx j (j + 1) fun _ _ => t

/-- The array of the lower solve in increasing order. -/
public def trsvTLowerAscData (d : Diag) (A : Mat n n) (x : Vec n) : Float64Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := x.data
    let o := x.off.toUSize
    let c := x.inc.toUSize
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    inplace a do
      for k in 0...nu do
        have hj : (nu - 1 - k).toNat = n - 1 - k.toNat := by grind
        have hjn : (nu - 1 - k).toNat < n := by lia
        have hk : (o + c * (nu - 1 - k)).toNat < a.size := x.toNat_index_lt hs.2 hjn
        let v := a[o + c * (nu - 1 - k)]
        for t in 0...k with (s := v) do
          have hi : (nu - 1 - k + 1 + t).toNat < n := by grind
          have hk' : (o + c * (nu - 1 - k + 1 + t)).toNat < a.size := x.toNat_index_lt hs.2 hi
          s := s - A.uget ao al rfl rfl hs.1 (nu - 1 - k + 1 + t) (nu - 1 - k) hi hjn *
            a[o + c * (nu - 1 - k + 1 + t)]
        a[o + c * (nu - 1 - k)] :=
          d.apply s (A.uget ao al rfl rfl hs.1 (nu - 1 - k) (nu - 1 - k) hjn hjn)
  else iterRange (trsvTLowerAscStep d A x) 0 n x.data

public theorem trsvTLowerAscData_eq_iterRange (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerAscData d A x = iterRange (trsvTLowerAscStep d A x) 0 n x.data := by
  unfold trsvTLowerAscData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := trsvTLowerAscStep d A x)
      (hF := fun _ _ => size_modifyAt _ _ _ _ _)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
    · intro k _ hk next a h
      rw [hnu] at hk
      have hj : (n.toUSize - 1 - k).toNat = n - 1 - k.toNat := by grind
      simp only [Tail.run_readThen]
      rw [Tail.run_forInFrom (f := fun t p =>
          (p.1 - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + t)]! *
            p.2[x.off + x.inc * (n - 1 - k.toNat + 1 + t)]!, p.2))
        (hf := fun _ _ => rfl)]
      · simp only [USize.toNat_zero, Tail.run_writeThen, iterRange_fst (fun t a s =>
          s - A.data[A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + t)]! *
            a[x.off + x.inc * (n - 1 - k.toNat + 1 + t)]!)]
        congr 1
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k)).toNat =
            x.off + x.inc * (n - 1 - k.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hj]
        rw [trsvTLowerAscStep, ← set_eq_modifyAt _ _ _ _
          (by rw [Vec.idx_stride, h]; exact x.index_lt (by lia))]
        simp only [hp, hj, Vec.idx_stride, uget_eq_getElem, getElem_def,
          getElem!_pos a (x.off + x.inc * (n - 1 - k.toNat))
            (show _ < a.size by rw [h]; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat))
            (A.index_lt (by lia) (by lia))]
      · intro t _ ht next' b a' h'
        simp only [Tail.run_readThen, uget_eq_getElem, getElem_def]
        have hi : (n.toUSize - 1 - k + 1 + t).toNat = n - 1 - k.toNat + 1 + t.toNat := by grind
        have hp : (x.off.toUSize + x.inc.toUSize * (n.toUSize - 1 - k + 1 + t)).toNat =
            x.off + x.inc * (n - 1 - k.toNat + 1 + t.toNat) := by
          rw [x.toNat_index hs.2 (by lia), hi]
        simp only [hp, hi, hj, getElem!_pos a' (x.off + x.inc * (n - 1 - k.toNat + 1 + t.toNat))
            (show _ < a'.size by rw [h']; exact x.index_lt (by lia)),
          getElem!_pos A.data (A.off + A.ld * (n - 1 - k.toNat) + (n - 1 - k.toNat + 1 + t.toNat))
            (A.index_lt (by lia) (by lia))]
  · rfl

/--
After the steps `t < k`, the elements `i ≥ n - k` are solved, and the others are unchanged.
-/
theorem iterRange_trsvTLowerAscStep (d : Diag) (A : Mat n n) (x : Vec n) {k : Nat}
    (hk : k ≤ n) :
    iterRange (trsvTLowerAscStep d A x) 0 k x.data =
      x.data.modifyAt x.stride.idx 0 n fun i v =>
        if n - k ≤ i then trsvTLowerAsc d A x i else v := by
  induction k with
  | zero =>
    rw [iterRange_self, modifyAt_congr_fun (g' := fun _ v => v), modifyAt_id]
    intro i v _ hi
    simp [show ¬n ≤ i by lia]
  | succ k ih =>
    rw [iterRange_succ _ (Nat.zero_le _), ih (by lia)]
    have hr : ∀ i, n - 1 - k ≤ i → i < n → (x.data.modifyAt x.stride.idx 0 n fun i v =>
          if n - k ≤ i then trsvTLowerAsc d A x i else v)[x.off + x.inc * i]! =
        if n - k ≤ i then trsvTLowerAsc d A x i else x.data[x.off + x.inc * i]! := by
      intro i _ hi
      rw [getElem!_pos _ _ (by simpa using x.index_lt hi),
        Vec.getElem_modifyAt_stride x rfl (Nat.le_refl _) _ (Nat.zero_le _) hi,
        getElem!_pos x.data _ (x.index_lt hi)]
    have ht : d.apply (Nat.fold k (fun t _ s =>
          s - A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k + 1 + t)]! *
            (x.data.modifyAt x.stride.idx 0 n fun i v =>
              if n - k ≤ i then trsvTLowerAsc d A x i else v)[x.off + x.inc * (n - 1 - k + 1 + t)]!)
          (x.data.modifyAt x.stride.idx 0 n fun i v =>
            if n - k ≤ i then trsvTLowerAsc d A x i else v)[x.off + x.inc * (n - 1 - k)]!)
          A.data[A.off + A.ld * (n - 1 - k) + (n - 1 - k)]! =
        trsvTLowerAsc d A x (n - 1 - k) := by
      rw [hr (n - 1 - k) (Nat.le_refl _) (by lia), ite_eq_right (by lia),
        trsvTLowerAsc.eq_1 d A x (n - 1 - k),
        Nat.fold_congr (show n - 1 - (n - 1 - k) = k by lia)]
      congr 2
      funext t ht s
      rw [hr (n - 1 - k + 1 + t) (by lia) (by lia), ite_eq_left (by lia)]
    simp only [trsvTLowerAscStep, ht]
    rw [modifyAt_widen (lo := n - 1 - k) (hi := n - 1 - k + 1) (lo' := 0) (hi' := n) _ _ _
      (Nat.zero_le _) (by lia) (by lia), modifyAt_modifyAt _ _ (x.fits.injOn (Nat.le_refl _))]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases h₁ : n - k ≤ i
    · simp [h₁, show n - (k + 1) ≤ i by lia, show ¬i < n - 1 - k + 1 by lia]
    · by_cases h₂ : i = n - 1 - k
      · subst h₂; simp [show n - (k + 1) ≤ n - 1 - k by lia]
      · simp [h₁, show ¬n - (k + 1) ≤ i by lia, show ¬n - 1 - k ≤ i by lia]

/--
The array of the lower solve in increasing order is the array of `x` with its elements solved.
-/
public theorem trsvTLowerAscData_eq (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTLowerAscData d A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTLowerAsc d A x i := by
  rw [trsvTLowerAscData_eq_iterRange, iterRange_trsvTLowerAscStep d A x (Nat.le_refl _)]
  apply modifyAt_congr_fun
  intro i v _ hi
  simp

/-- The column solve of `trsmT`: `trsvTUpper`, or `trsvTLowerAsc` for the lower triangle. -/
@[expose] public def trsvTAscSol (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => trsvTUpper d A x
  | .lower => trsvTLowerAsc d A x

/-- The array of the column solve of `trsmT`. -/
@[expose] public def trsvTAscData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => trsvTUpperData d A x
  | .lower => trsvTLowerAscData d A x

public theorem trsvTAscData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTAscData uplo d A x =
      x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTAscSol uplo d A x i := by
  cases uplo
  · exact trsvTUpperData_eq d A x
  · exact trsvTLowerAscData_eq d A x

/-! ## `trsvT` -/

/-- The solution of `Aᵀ * y = x` for the triangle `uplo` of `A`, element by element. -/
@[expose] public def trsvTSol (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Nat → Float :=
  match uplo with
  | .upper => trsvTUpper d A x
  | .lower => trsvTLower d A x

/-- The array of `trsvT`. -/
@[expose] public def trsvTData (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    Float64Array :=
  match uplo with
  | .upper => trsvTUpperData d A x
  | .lower => trsvTLowerData d A x

public theorem trsvTData_eq (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    trsvTData uplo d A x = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTSol uplo d A x i := by
  cases uplo
  · exact trsvTUpperData_eq d A x
  · exact trsvTLowerData_eq d A x

/--
`trsvT uplo d A x` solves `Aᵀ * y = x` for the triangle `uplo` of `A`, with a unit diagonal if `d`
is `.unit`, by the loops of the reference BLAS for `TRANS = 'T'`. For the upper triangle, it sets
`y[j]` to `x[j]` minus the dot product of the elements `0, …, j - 1` of column `j` of `A` and of
`y`, divided by `A[j, j]`, for `j = 0, …, n - 1`; for the lower triangle, it does the same from
`j = n - 1` down to `0`, with the elements below the diagonal, from the last one up. It updates `x`
in place when its array is not shared, and leaves the elements of the array outside `x` unchanged.
It reads only the triangle `uplo` of `A`, and not its diagonal when `d` is `.unit`. Like the
reference BLAS, it doesn't check for a zero on the diagonal.
-/
@[expose] public def trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) : Vec n where
  data := trsvTData uplo d A x
  off := x.off
  inc := x.inc
  inc_pos := x.inc_pos
  bound := by rw [trsvTData_eq, size_modifyAt]; exact x.bound

/-- The array of `trsvT uplo d A x` is the array of `x` with its elements solved. -/
public theorem data_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsvT uplo d A x).data = x.data.modifyAt x.stride.idx 0 n fun i _ => trsvTSol uplo d A x i :=
  trsvTData_eq uplo d A x

@[simp] public theorem off_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsvT uplo d A x).off = x.off := rfl

@[simp] public theorem inc_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) :
    (trsvT uplo d A x).inc = x.inc := rfl

/-- Element `i` of `trsvT uplo d A x` is element `i` of the model. -/
public theorem getElem_trsvT (uplo : Uplo) (d : Diag) (A : Mat n n) (x : Vec n) (i : Nat)
    (h : i < n) : (trsvT uplo d A x)[i] = trsvTSol uplo d A x i :=
  Vec.getElem_of_data_eq_modifyAt _ (data_trsvT uplo d A x) rfl rfl i h

/--
Element `j` of `y = trsvT .upper d A x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = 0, …, j - 1`, divided by `A[j, j]` unless the diagonal is unit: forward substitution with
`Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsvT_upper (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (h : j < n) :
    (trsvT .upper d A x)[j] = d.apply (Nat.fold j (fun i hi s =>
      s - A[(i, j)]'⟨by lia, h⟩ * (trsvT .upper d A x)[i]'(by lia)) x[j]) A[(j, j)] := by
  rw [getElem_trsvT _ _ _ _ _ h, trsvTSol, trsvTUpper_eq d A x h]
  congr
  funext i hi s
  rw [getElem_trsvT _ _ _ _ _ (by lia), trsvTSol]

/--
Element `j` of `y = trsvT .lower d A x` is `x[j]`, minus the terms `A[i, j] * y[i]` for
`i = n - 1, …, j + 1`, divided by `A[j, j]` unless the diagonal is unit: back substitution with
`Aᵀ`, in the order of the loops.
-/
public theorem getElem_trsvT_lower (d : Diag) (A : Mat n n) (x : Vec n) (j : Nat) (h : j < n) :
    (trsvT .lower d A x)[j] = d.apply (Nat.fold (n - 1 - j) (fun t _ s =>
      s - A[(n - 1 - t, j)]'⟨by lia, h⟩ * (trsvT .lower d A x)[n - 1 - t]'(by lia)) x[j])
        A[(j, j)] := by
  rw [getElem_trsvT _ _ _ _ _ h, trsvTSol, trsvTLower_eq d A x h]
  congr
  funext t ht s
  rw [getElem_trsvT _ _ _ _ _ (by lia), trsvTSol]

end Mat

end BLAS.Float64
