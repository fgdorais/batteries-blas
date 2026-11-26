/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float32.Syrk
import all BatteriesBLAS.Internal

/-!
# Symmetric rank-one and rank-two updates

`Mat.syr uplo α x A` computes `α * x * xᵀ + A` and `Mat.syr2 uplo α x y A` computes
`α * x * yᵀ + α * y * xᵀ + A`, on the triangle `uplo` of `A`, by the loops of the reference BLAS.
As there, they return `A` when `α = 0`, and skip the columns `j` with `x[j] = 0` (with
`x[j] = y[j] = 0` for `syr2`), so that an infinity or a `NaN` elsewhere in `x` or `y` doesn't
reach them. They update `A` in place when its array is not shared, and leave the other triangle
and the elements of the array outside `A` unchanged.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.Float32

namespace Mat

variable {n : Nat}

/-- The bound that a loop from `u.loU j` to `u.hiU nu j` gives its index. -/
private theorem lt_of_hiU' {u : Uplo} {nu j i : USize} (hnu : nu.toNat = n) (hj : j.toNat < n)
    (hi : i.toNat < (u.hiU nu j).toNat) : i.toNat < n := by
  rw [u.toNat_hiU hnu hj] at hi
  exact Nat.lt_of_lt_of_le hi (u.hi_le hj)

/--
The column `j` of a triangle `uplo`, mapped by `G` from `lo` to `hi`, or not at all when `skip`, is
mapped by `G` on the triangle, unless `skip`.
-/
private theorem modifyAt_tri (a : Float32Array) (uplo : Uplo) (off ld j : Nat) (hj : j < n)
    (skip : Bool) (G : Nat → Float32 → Float32) :
    a.modifyAt (Stride.mk (off + ld * j) 1).idx (uplo.lo j)
        (if skip then uplo.lo j else uplo.hi n j) G =
      a.modifyAt (Stride.mk (off + ld * j) 1).idx 0 n fun i v =>
        if uplo.contains i j && !skip then G i v else v := by
  split
  · next h =>
    rw [modifyAt_of_le _ _ (Nat.le_refl _),
      modifyAt_congr_fun _ _ (g' := fun _ v => v) (fun i v _ _ => by simp [h]), modifyAt_id]
  · next h =>
    rw [modifyAt_widen (lo' := 0) (hi' := n) _ _ _ (Nat.zero_le _) (uplo.lo_le_hi hj)
      (uplo.hi_le hj)]
    apply modifyAt_congr_fun
    intro i v _ hi
    by_cases hc : uplo.contains i j = true
    · rw [ite_eq_left ((uplo.contains_iff hi).1 hc)]; simp [hc, h]
    · rw [ite_eq_right (fun h' => hc ((uplo.contains_iff hi).2 h'))]; simp [hc]

/-! ## `syr` -/

/--
The value of the loops of `syr` at `(i, j)`, from its old value `v`, on the arrays: `v` outside the
triangle and when `x[j] = 0`, and `v + x[i] * (α * x[j])` otherwise.
-/
@[expose] public def syrAt (uplo : Uplo) (α : Float32) (x : Vec n) (i j : Nat) (v : Float32) :
    Float32 :=
  if uplo.contains i j && !(x.data[x.off + x.inc * j]! == 0) then
    v + x.data[x.off + x.inc * i]! * (α * x.data[x.off + x.inc * j]!)
  else v

/-- The array of `syr`. -/
public def syrData (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2
    let a := A.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    inplace a do
      for j in 0...nu do
        let xj := x.uget xo xc rfl rfl hs.2 j (by lia)
        let t := α * xj
        let cj := ao + al * j
        let lo := uplo.loU j
        -- A skipped column runs an empty loop: an `if` would allocate a closure per column.
        let hi := syrkRows lo (uplo.hiU nu j) (xj == 0)
        have hh : hi.toNat ≤ (uplo.hiU nu j).toNat :=
          syrkRows_le (uplo.loU_le_hiU hnu (by lia)) _
        for i in lo...hi do
          have hi' : i.toNat < n :=
            lt_of_hiU' (u := uplo) (j := j) hnu (by lia) (Nat.lt_of_lt_of_le (by assumption) hh)
          have hk : (cj + 1 * i).toNat < a.size := A.toNat_col_index_lt hs.1 hi' (by lia)
          a[cj + 1 * i] := a[cj + 1 * i] + x.uget xo xc rfl rfl hs.2 i hi' * t
  else mapMat A.data A.off A.ld n 0 n (syrAt uplo α x)

public theorem syrData_eq (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) :
    syrData uplo α x A = mapMat A.data A.off A.ld n 0 n (syrAt uplo α x) := by
  unfold syrData
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (A.off + A.ld * j) 1).idx 0 n fun i v => syrAt uplo α x i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ A.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hy := getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)
      rw [Tail.run_forInFrom_modify
        (G := fun i v => v + x.data[x.off + x.inc * i]! * (α * x.data[x.off + x.inc * j.toNat]!))
        (idx := (Stride.mk (A.off + A.ld * j.toNat) 1).idx)
        (he := fun i _ hi => A.toNat_col_index hs.1 (lt_of_hiU' hnu hj
          (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj) _))) hj)]
      · apply run_congr
        have hr : ∀ b : Bool, (syrkRows (uplo.loU j) (uplo.hiU n.toUSize j) b).toNat =
            if b then uplo.lo j.toNat else uplo.hi n j.toNat := by
          intro b; unfold syrkRows; split <;> simp [uplo.toNat_loU, uplo.toNat_hiU hnu hj]
        rw [hr, uplo.toNat_loU, modifyAt_tri _ _ _ _ _ hj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [syrAt, Vec.uget_eq_getElem, Vec.getElem_def, ← hy]
      · intro i _ hi v
        have hi' : i.toNat < n := lt_of_hiU' hnu hj
          (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj) _))
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, ← hy,
          getElem!_pos x.data (x.off + x.inc * i.toNat) (x.index_lt hi')]
  · rfl

/--
`syr uplo α x A` is `α * x * xᵀ + A` on the triangle `uplo` of `A`, by the loops of the reference
BLAS: for each column `j`, it adds `x` times `α * x[j]` to the part of the column in the triangle.
As in the reference BLAS, it returns `A` when `α = 0`, and skips the columns with `x[j] = 0`. It
updates `A` in place when its array is not shared, and leaves the other triangle and the elements
of the array outside `A` unchanged.
-/
@[expose] public def syr (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) : Mat n n :=
  if α == 0 then A
  else
    { data := syrData uplo α x A
      off := A.off
      ld := A.ld
      le_ld := A.le_ld
      bound := by rw [syrData_eq, size_mapMat]; exact A.bound }

public theorem data_syr (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) :
    (syr uplo α x A).data =
      mapMat A.data A.off A.ld n 0 n fun i j v => if α == 0 then v else syrAt uplo α x i j v := by
  unfold syr
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, syrData_eq]
  · simp only [↓reduceIte, mapMat_id]

@[simp] public theorem off_syr (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) :
    (syr uplo α x A).off = A.off := by
  unfold syr; split <;> rfl

@[simp] public theorem ld_syr (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) :
    (syr uplo α x A).ld = A.ld := by
  unfold syr; split <;> rfl

/--
Element `(i, j)` of `syr uplo α x A` is `A[i, j]` when `α = 0`, outside the triangle `uplo`, or
when `x[j] = 0`, and `A[i, j] + x[i] * (α * x[j])` otherwise.
-/
public theorem getElem_syr (uplo : Uplo) (α : Float32) (x : Vec n) (A : Mat n n) (i j : Nat)
    (h : i < n ∧ j < n) :
    (syr uplo α x A)[(i, j)] =
      if α == 0 || !uplo.contains i j || x[j] == 0 then A[(i, j)]
      else A[(i, j)] + x[i] * (α * x[j]) := by
  rw [getElem_of_data_eq_mapMat _ (data_syr uplo α x A) (off_syr uplo α x A) (ld_syr uplo α x A)
    i j h, syrAt,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h.1),
    getElem!_pos x.data (x.off + x.inc * j) (x.index_lt h.2)]
  cases α == 0 <;> cases uplo.contains i j <;> cases x[j] == 0 <;> rfl

/-! ## `syr2` -/

/--
The value of the loops of `syr2` at `(i, j)`, from its old value `v`, on the arrays: `v` outside
the triangle and when `x[j] = y[j] = 0`, and `v + x[i] * (α * y[j]) + y[i] * (α * x[j])`
otherwise.
-/
@[expose] public def syr2At (uplo : Uplo) (α : Float32) (x y : Vec n) (i j : Nat) (v : Float32) :
    Float32 :=
  if uplo.contains i j &&
      !(x.data[x.off + x.inc * j]! == 0 && y.data[y.off + y.inc * j]! == 0) then
    v + x.data[x.off + x.inc * i]! * (α * y.data[y.off + y.inc * j]!) +
      y.data[y.off + y.inc * i]! * (α * x.data[x.off + x.inc * j]!)
  else v

/-- The array of `syr2`. -/
public def syr2Data (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) : Float32Array :=
  if hs : A.data.size < USize.size ∧ x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := x.toNat_toUSize hs.2.1
    let a := A.data
    let ao := A.off.toUSize
    let al := A.ld.toUSize
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let yo := y.off.toUSize
    let yc := y.inc.toUSize
    inplace a do
      for j in 0...nu do
        let xj := x.uget xo xc rfl rfl hs.2.1 j (by lia)
        let yj := y.uget yo yc rfl rfl hs.2.2 j (by lia)
        let t1 := α * yj
        let t2 := α * xj
        let cj := ao + al * j
        let lo := uplo.loU j
        let hi := syrkRows lo (uplo.hiU nu j) (xj == 0 && yj == 0)
        have hh : hi.toNat ≤ (uplo.hiU nu j).toNat :=
          syrkRows_le (uplo.loU_le_hiU hnu (by lia)) _
        for i in lo...hi do
          have hi' : i.toNat < n :=
            lt_of_hiU' (u := uplo) (j := j) hnu (by lia) (Nat.lt_of_lt_of_le (by assumption) hh)
          have hk : (cj + 1 * i).toNat < a.size := A.toNat_col_index_lt hs.1 hi' (by lia)
          a[cj + 1 * i] := a[cj + 1 * i] + x.uget xo xc rfl rfl hs.2.1 i hi' * t1 +
            y.uget yo yc rfl rfl hs.2.2 i hi' * t2
  else mapMat A.data A.off A.ld n 0 n (syr2At uplo α x y)

public theorem syr2Data_eq (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) :
    syr2Data uplo α x y A = mapMat A.data A.off A.ld n 0 n (syr2At uplo α x y) := by
  unfold syr2Data
  split
  · rename_i hs
    have hnu := x.toNat_toUSize hs.2.1
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_unit (F := fun j c =>
      c.modifyAt (Stride.mk (A.off + A.ld * j) 1).idx 0 n fun i v => syr2At uplo α x y i j v)
      (hF := by simp)]
    · simp only [Tail.run_done, USize.toNat_zero, hnu]
      rw [iterRange_cols _ _ _ A.le_ld]
    · intro j _ hj next a h
      rw [hnu] at hj
      have hx := getElem!_pos x.data (x.off + x.inc * j.toNat) (x.index_lt hj)
      have hy := getElem!_pos y.data (y.off + y.inc * j.toNat) (y.index_lt hj)
      rw [Tail.run_forInFrom_modify
        (G := fun i v => v + x.data[x.off + x.inc * i]! * (α * y.data[y.off + y.inc * j.toNat]!) +
          y.data[y.off + y.inc * i]! * (α * x.data[x.off + x.inc * j.toNat]!))
        (idx := (Stride.mk (A.off + A.ld * j.toNat) 1).idx)
        (he := fun i _ hi => A.toNat_col_index hs.1 (lt_of_hiU' hnu hj
          (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj) _))) hj)]
      · apply run_congr
        have hr : ∀ b : Bool, (syrkRows (uplo.loU j) (uplo.hiU n.toUSize j) b).toNat =
            if b then uplo.lo j.toNat else uplo.hi n j.toNat := by
          intro b; unfold syrkRows; split <;> simp [uplo.toNat_loU, uplo.toNat_hiU hnu hj]
        rw [hr, uplo.toNat_loU, modifyAt_tri _ _ _ _ _ hj]
        apply modifyAt_congr_fun
        intro i v _ _
        simp only [syr2At, Vec.uget_eq_getElem, Vec.getElem_def, ← hx, ← hy]
      · intro i _ hi v
        have hi' : i.toNat < n := lt_of_hiU' hnu hj
          (Nat.lt_of_lt_of_le hi (syrkRows_le (uplo.loU_le_hiU hnu hj) _))
        simp only [Vec.uget_eq_getElem, Vec.getElem_def, ← hx, ← hy,
          getElem!_pos x.data (x.off + x.inc * i.toNat) (x.index_lt hi'),
          getElem!_pos y.data (y.off + y.inc * i.toNat) (y.index_lt hi')]
  · rfl

/--
`syr2 uplo α x y A` is `α * x * yᵀ + α * y * xᵀ + A` on the triangle `uplo` of `A`, by the loops of
the reference BLAS: for each column `j`, it adds `x` times `α * y[j]` and `y` times `α * x[j]` to
each element of the part of the column in the triangle, in that order. As in the reference BLAS,
it returns `A` when `α = 0`, and skips the columns with `x[j] = y[j] = 0`. It updates `A` in place
when its array is not shared, and leaves the other triangle and the elements of the array outside
`A` unchanged.
-/
@[expose] public def syr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) : Mat n n :=
  if α == 0 then A
  else
    { data := syr2Data uplo α x y A
      off := A.off
      ld := A.ld
      le_ld := A.le_ld
      bound := by rw [syr2Data_eq, size_mapMat]; exact A.bound }

public theorem data_syr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) :
    (syr2 uplo α x y A).data =
      mapMat A.data A.off A.ld n 0 n fun i j v =>
        if α == 0 then v else syr2At uplo α x y i j v := by
  unfold syr2
  cases hα : α == 0
  · simp only [Bool.false_eq_true, ↓reduceIte, syr2Data_eq]
  · simp only [↓reduceIte, mapMat_id]

@[simp] public theorem off_syr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) :
    (syr2 uplo α x y A).off = A.off := by
  unfold syr2; split <;> rfl

@[simp] public theorem ld_syr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) :
    (syr2 uplo α x y A).ld = A.ld := by
  unfold syr2; split <;> rfl

/--
Element `(i, j)` of `syr2 uplo α x y A` is `A[i, j]` when `α = 0`, outside the triangle `uplo`, or
when `x[j] = y[j] = 0`, and `A[i, j] + x[i] * (α * y[j]) + y[i] * (α * x[j])` otherwise.
-/
public theorem getElem_syr2 (uplo : Uplo) (α : Float32) (x y : Vec n) (A : Mat n n) (i j : Nat)
    (h : i < n ∧ j < n) :
    (syr2 uplo α x y A)[(i, j)] =
      if α == 0 || !uplo.contains i j || (x[j] == 0 && y[j] == 0) then A[(i, j)]
      else A[(i, j)] + x[i] * (α * y[j]) + y[i] * (α * x[j]) := by
  rw [getElem_of_data_eq_mapMat _ (data_syr2 uplo α x y A) (off_syr2 uplo α x y A)
    (ld_syr2 uplo α x y A) i j h, syr2At,
    getElem!_pos x.data (x.off + x.inc * i) (x.index_lt h.1),
    getElem!_pos x.data (x.off + x.inc * j) (x.index_lt h.2),
    getElem!_pos y.data (y.off + y.inc * i) (y.index_lt h.1),
    getElem!_pos y.data (y.off + y.inc * j) (y.index_lt h.2)]
  cases α == 0 <;> cases uplo.contains i j <;> cases x[j] == 0 <;> cases y[j] == 0 <;> rfl

end Mat

end BLAS.Float32
