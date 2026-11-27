/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Vec
public import BatteriesBLAS.Float32.Level1
public import ScalarArray.Notation

/-!
# Complex Level 1

Vector operations on complex vectors: the updates `axpy`, `scal`, `rscal`, `copy` and `swap`, and
the reductions `dotu`, `dotc`, `asum`, `nrm2` and `iamax`.

As for the real routines, each routine runs a loop over the `USize` indices of its vectors when
their arrays' sizes fit in a `USize`, as they do for every array in memory, and its model
otherwise, so that its specification needs no hypothesis on the size. An update reads and writes
both parts of an element in the same step, and its model is a scalar-arrays `modifyAt2` at the
indices of the real and the imaginary parts.
-/

open ScalarArray Float32Array InPlace

namespace BLAS.ComplexFloat32

namespace Vec

variable {n : Nat}

/--
A vector `v` whose array is the array of `w` with both parts of element `i` mapped together by
`F i` and `G i`, at the same indices, has the elements
`⟨F i w[i].re w[i].im, G i w[i].re w[i].im⟩`.
-/
public theorem getElem_of_data_eq_modifyAt2 {v w : Vec n}
    (F G : Nat → Float32 → Float32 → Float32)
    (hd : v.data = w.data.modifyAt2 w.reStride.idx w.imStride.idx 0 n F G) (ho : v.off = w.off)
    (hc : v.inc = w.inc) (i : Nat) (h : i < n) :
    v[i] = ⟨F i w[i].re w[i].im, G i w[i].re w[i].im⟩ := by
  have hd' := fun i j (_ : i < n) (_ : j < n) => w.re_ne_im i j
  simp only [getElem_def]
  congr 1
  · have e : v.data[2 * v.off + 2 * v.inc * i]'(v.re_lt h) =
        (w.data.modifyAt2 w.reStride.idx w.imStride.idx 0 n F G)[w.reStride.idx i]'(by
          rw [size_modifyAt2]; exact w.re_lt h) := by
      simp only [hd, ho, hc, idx_reStride]
    rw [e, getElem_modifyAt2_stride_left _ w.fits_re w.fits_im (fun i hi j hj => hd' i j hi hj)
      (Nat.le_refl _) _ _ (Nat.zero_le _) h]
    rfl
  · have e : v.data[2 * v.off + 1 + 2 * v.inc * i]'(v.im_lt h) =
        (w.data.modifyAt2 w.reStride.idx w.imStride.idx 0 n F G)[w.imStride.idx i]'(by
          rw [size_modifyAt2]; exact w.im_lt h) := by
      simp only [hd, ho, hc, idx_imStride]
    rw [e, getElem_modifyAt2_stride_right _ w.fits_re w.fits_im (fun i hi j hj => hd' i j hi hj)
      (Nat.le_refl _) _ _ (Nat.zero_le _) h]
    rfl

/-- The number of elements `n` as a `USize`, in a vector whose array has a `USize` size. -/
public theorem toNat_toUSize (x : Vec n) (hs : x.data.size < USize.size) :
    n.toUSize.toNat = n := by
  have := x.two_mul_le_size
  grind

/-! ## `scal` and `rscal` -/

/--
`scal α x` is `α * x`, with the product `mul`, as in the reference BLAS. As there, it returns
`x` when `α = 1`, so that an infinity in `x` doesn't turn into a `NaN`. It updates `x` in place
when its array is not shared, and leaves the entries of the array outside `x` unchanged.
-/
@[expose] public def scal (α : ComplexFloat32) (x : Vec n) : Vec n :=
  if α.re == 1 && α.im == 0 then x
  else
    { data := x.data.modifyStride2 x.reStride x.imStride n (fun u v => mulRe α ⟨u, v⟩)
        (fun u v => mulIm α ⟨u, v⟩) x.fits_re x.fits_im
      off := x.off
      inc := x.inc
      inc_pos := x.inc_pos
      bound := by rw [size_modifyStride2]; exact x.bound }

@[simp] public theorem off_scal (α : ComplexFloat32) (x : Vec n) : (scal α x).off = x.off := by
  unfold scal; split <;> rfl

@[simp] public theorem inc_scal (α : ComplexFloat32) (x : Vec n) : (scal α x).inc = x.inc := by
  unfold scal; split <;> rfl

/-- Element `i` of `scal α x` is `x[i]` when `α = 1`, and `mul α x[i]` otherwise. -/
@[simp] public theorem getElem_scal (α : ComplexFloat32) (x : Vec n) (i : Nat) (h : i < n) :
    (scal α x)[i] = if α.re == 1 && α.im == 0 then x[i] else mul α x[i] := by
  unfold scal
  split
  · rfl
  · refine (getElem_of_data_eq_modifyAt2 (v := ⟨_, x.off, x.inc, x.inc_pos, _⟩) (w := x) _ _
      (modifyStride2_eq ..) rfl rfl i h).trans ?_
    simp only [mulRe_eq, mulIm_eq]

/--
`rscal α x` is `α * x` for a real `α`, as `csscal` in the reference BLAS: it multiplies both
parts of each element by `α`. As there, it returns `x` when `α = 1`.
-/
@[expose] public def rscal (α : Float32) (x : Vec n) : Vec n :=
  if α == 1 then x
  else
    { data := x.data.modifyStride2 x.reStride x.imStride n (fun u _ => α * u) (fun _ v => α * v)
        x.fits_re x.fits_im
      off := x.off
      inc := x.inc
      inc_pos := x.inc_pos
      bound := by rw [size_modifyStride2]; exact x.bound }

@[simp] public theorem off_rscal (α : Float32) (x : Vec n) : (rscal α x).off = x.off := by
  unfold rscal; split <;> rfl

@[simp] public theorem inc_rscal (α : Float32) (x : Vec n) : (rscal α x).inc = x.inc := by
  unfold rscal; split <;> rfl

/-- Element `i` of `rscal α x` is `x[i]` when `α = 1`, and `rmul α x[i]` otherwise. -/
@[simp] public theorem getElem_rscal (α : Float32) (x : Vec n) (i : Nat) (h : i < n) :
    (rscal α x)[i] = if α == 1 then x[i] else rmul α x[i] := by
  unfold rscal
  split
  · rfl
  · exact getElem_of_data_eq_modifyAt2 (v := ⟨_, x.off, x.inc, x.inc_pos, _⟩) (w := x) _ _
      (modifyStride2_eq ..) rfl rfl i h

/-! ## `axpy` -/

/-- The `USize` indices of the real parts in the loop of a vector update don't wrap. -/
public theorem loop_re (x : Vec n) (hs : x.data.size < USize.size) :
    ∀ j : USize, (0 : USize).toNat ≤ j.toNat → j.toNat < n.toUSize.toNat →
      ((2 * x.off).toUSize + (2 * x.inc).toUSize * j).toNat = x.reStride.idx j.toNat := by
  rw [x.toNat_toUSize hs]
  exact fun j _ hj => x.toNat_re hs hj

/-- The `USize` indices of the imaginary parts in the loop of a vector update don't wrap. -/
public theorem loop_im (x : Vec n) (hs : x.data.size < USize.size) :
    ∀ j : USize, (0 : USize).toNat ≤ j.toNat → j.toNat < n.toUSize.toNat →
      ((2 * x.off + 1).toUSize + (2 * x.inc).toUSize * j).toNat = x.imStride.idx j.toNat := by
  rw [x.toNat_toUSize hs]
  exact fun j _ hj => x.toNat_im hs hj

/-- Element `i` of `x`, or `0` out of bounds, for the models. -/
@[expose] public def get0 (x : Vec n) (i : Nat) : ComplexFloat32 :=
  if h : i < n then x[i] else zero

/--
The array of `y` with each element `v` replaced by `⟨fr v x[k], fi v x[k]⟩`, in one loop that
reads `x` and updates `y` in place when its array is not shared. The parts `fr` and `fi` are
separate functions, so that the loop keeps them in floats rather than in a `ComplexFloat32`.
-/
@[inline] public def zipWithData (fr fi : ComplexFloat32 → ComplexFloat32 → Float32) (x y : Vec n) :
    Float32Array :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2
    let a := y.data
    let o := (2 * y.off).toUSize
    let o1 := (2 * y.off + 1).toUSize
    let c := (2 * y.inc).toUSize
    let xo := (2 * x.off).toUSize
    let xo1 := (2 * x.off + 1).toUSize
    let xc := (2 * x.inc).toUSize
    inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_re_lt hs.2 (by lia)
        have hk1 : (o1 + c * k).toNat < a.size := y.toNat_im_lt hs.2 (by lia)
        let u := a[o + c * k]
        let v := a[o1 + c * k]
        a[o + c * k] := fr ⟨u, v⟩ (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia))
        a[o1 + c * k] := fi ⟨u, v⟩ (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia))
  else y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
    (fun i u v => fr ⟨u, v⟩ (x.get0 i)) (fun i u v => fi ⟨u, v⟩ (x.get0 i))

public theorem zipWithData_eq (fr fi : ComplexFloat32 → ComplexFloat32 → Float32) (x y : Vec n) :
    zipWithData fr fi x y = y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
      (fun i u v => fr ⟨u, v⟩ (x.get0 i)) (fun i u v => fi ⟨u, v⟩ (x.get0 i)) := by
  unfold zipWithData
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify2 (ia := y.reStride.idx) (ib := y.imStride.idx)
      (F := fun i u v => fr ⟨u, v⟩ (x.get0 i)) (G := fun i u v => fi ⟨u, v⟩ (x.get0 i))
      (hea := y.loop_re hs.2) (heb := y.loop_im hs.2)]
    · simp only [Tail.run_done, y.toNat_toUSize hs.2, USize.toNat_zero]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
  · rfl

public theorem size_zipWithData (fr fi : ComplexFloat32 → ComplexFloat32 → Float32) (x y : Vec n) :
    (zipWithData fr fi x y).size = y.data.size := by
  rw [zipWithData_eq, size_modifyAt2]

/-- Element `i` of a vector whose array is `zipWithData fr fi x y`, with the place of `y`. -/
public theorem getElem_of_data_eq_zipWithData {v : Vec n}
    (fr fi : ComplexFloat32 → ComplexFloat32 → Float32) (x y : Vec n)
    (hd : v.data = zipWithData fr fi x y) (ho : v.off = y.off) (hc : v.inc = y.inc) (i : Nat)
    (h : i < n) : v[i] = ⟨fr y[i] x[i], fi y[i] x[i]⟩ := by
  rw [getElem_of_data_eq_modifyAt2 _ _ (hd.trans (zipWithData_eq ..)) ho hc i h]
  simp only [get0, h, ↓reduceDIte]

/-- The array of `axpy`. -/
public def axpyData (α : ComplexFloat32) (x y : Vec n) : Float32Array :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2
    let a := y.data
    let o := (2 * y.off).toUSize
    let o1 := (2 * y.off + 1).toUSize
    let c := (2 * y.inc).toUSize
    let xo := (2 * x.off).toUSize
    let xo1 := (2 * x.off + 1).toUSize
    let xc := (2 * x.inc).toUSize
    let ar := α.re
    let ai := α.im
    inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_re_lt hs.2 (by lia)
        have hk1 : (o1 + c * k).toNat < a.size := y.toNat_im_lt hs.2 (by lia)
        let u := a[o + c * k]
        let v := a[o1 + c * k]
        a[o + c * k] := u + mulRe ⟨ar, ai⟩ (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia))
        a[o1 + c * k] := v + mulIm ⟨ar, ai⟩ (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia))
  else y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
    (fun i u _ => u + (mul α (x.get0 i)).re) (fun i _ v => v + (mul α (x.get0 i)).im)

public theorem axpyData_eq (α : ComplexFloat32) (x y : Vec n) :
    axpyData α x y = y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
      (fun i u _ => u + (mul α (x.get0 i)).re) (fun i _ v => v + (mul α (x.get0 i)).im) := by
  unfold axpyData
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify2 (ia := y.reStride.idx) (ib := y.imStride.idx)
      (F := fun i u _ => u + (mul α (x.get0 i)).re) (G := fun i _ v => v + (mul α (x.get0 i)).im)
      (hea := y.loop_re hs.2) (heb := y.loop_im hs.2)]
    · simp only [Tail.run_done, y.toNat_toUSize hs.2, USize.toNat_zero]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
  · rfl

/--
`axpy α x y` is `α * x + y`, with the product `mul`. As in the reference BLAS, it returns `y`
when `|α.re| + |α.im| = 0`, without reading `x`. It updates `y` in place when its array is not
shared, and leaves the entries of the array outside `y` unchanged.
-/
@[expose] public def axpy (α : ComplexFloat32) (x y : Vec n) : Vec n :=
  if abs1 α == 0 then y
  else
    { data := axpyData α x y
      off := y.off
      inc := y.inc
      inc_pos := y.inc_pos
      bound := by rw [axpyData_eq, size_modifyAt2]; exact y.bound }

@[simp] public theorem off_axpy (α : ComplexFloat32) (x y : Vec n) :
    (axpy α x y).off = y.off := by
  unfold axpy; split <;> rfl

@[simp] public theorem inc_axpy (α : ComplexFloat32) (x y : Vec n) :
    (axpy α x y).inc = y.inc := by
  unfold axpy; split <;> rfl

/--
Element `i` of `axpy α x y` is `y[i]` when `|α.re| + |α.im| = 0`, and `y[i] + mul α x[i]`
otherwise.
-/
@[simp] public theorem getElem_axpy (α : ComplexFloat32) (x y : Vec n) (i : Nat) (h : i < n) :
    (axpy α x y)[i] = if abs1 α == 0 then y[i] else y[i] + mul α x[i] := by
  unfold axpy
  split
  · rfl
  · refine (getElem_of_data_eq_modifyAt2 (v := ⟨_, y.off, y.inc, y.inc_pos, _⟩) (w := y) _ _
      (axpyData_eq α x y) rfl rfl i h).trans ?_
    simp [get0, h]
    rfl

/-! ## `copy` and `swap` -/

/-- The array of `copy`. -/
public def copyData (x y : Vec n) : Float32Array :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let nu := n.toUSize
    have hnu : nu.toNat = n := y.toNat_toUSize hs.2
    let a := y.data
    let o := (2 * y.off).toUSize
    let o1 := (2 * y.off + 1).toUSize
    let c := (2 * y.inc).toUSize
    let xo := (2 * x.off).toUSize
    let xo1 := (2 * x.off + 1).toUSize
    let xc := (2 * x.inc).toUSize
    inplace a do
      for k in 0...nu do
        have hk : (o + c * k).toNat < a.size := y.toNat_re_lt hs.2 (by lia)
        have hk1 : (o1 + c * k).toNat < a.size := y.toNat_im_lt hs.2 (by lia)
        let _u := a[o + c * k]
        let _v := a[o1 + c * k]
        a[o + c * k] := (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia)).re
        a[o1 + c * k] := (x.uget xo xo1 xc rfl rfl rfl hs.1 k (by lia)).im
  else y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
    (fun i _ _ => (x.get0 i).re) (fun i _ _ => (x.get0 i).im)

public theorem copyData_eq (x y : Vec n) :
    copyData x y = y.data.modifyAt2 y.reStride.idx y.imStride.idx 0 n
      (fun i _ _ => (x.get0 i).re) (fun i _ _ => (x.get0 i).im) := by
  unfold copyData
  split
  · rename_i hs
    simp only [runInPlaceThenOf_eq, Tail.forIn_eq]
    rw [Tail.run_forInFrom_modify2 (ia := y.reStride.idx) (ib := y.imStride.idx)
      (F := fun i _ _ => (x.get0 i).re) (G := fun i _ _ => (x.get0 i).im)
      (hea := y.loop_re hs.2) (heb := y.loop_im hs.2)]
    · simp only [Tail.run_done, y.toNat_toUSize hs.2, USize.toNat_zero]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
    · intro j _ hj u v
      rw [y.toNat_toUSize hs.2] at hj
      simp [get0, hj]
  · rfl

/--
`copy x y` is `x`, written over `y`, in place when the array of `y` is not shared. It leaves the
entries of the array outside `y` unchanged.
-/
@[expose] public def copy (x y : Vec n) : Vec n where
  data := copyData x y
  off := y.off
  inc := y.inc
  inc_pos := y.inc_pos
  bound := by rw [copyData_eq, size_modifyAt2]; exact y.bound

@[simp] public theorem off_copy (x y : Vec n) : (copy x y).off = y.off := rfl

@[simp] public theorem inc_copy (x y : Vec n) : (copy x y).inc = y.inc := rfl

@[simp] public theorem getElem_copy (x y : Vec n) (i : Nat) (h : i < n) :
    (copy x y)[i] = x[i] := by
  refine (getElem_of_data_eq_modifyAt2 (v := copy x y) (w := y) _ _ (copyData_eq x y) rfl rfl i
    h).trans ?_
  simp [get0, h]
  rfl

/-- `swap x y` is `(y, x)`. Nothing is copied. -/
public def swap (x y : Vec n) : Vec n × Vec n := (y, x)

@[simp] public theorem swap_fst (x y : Vec n) : (swap x y).1 = y := by simp [swap]

@[simp] public theorem swap_snd (x y : Vec n) : (swap x y).2 = x := by simp [swap]

/-! ## `dotu` and `dotc` -/

/--
The loop of `dotu` and `dotc` from the index `i`, up to the bound `m`, which is `n`, with the parts
`sr` and `si` of the sum so far: it adds `mul (p x[i]) y[i]`. It keeps the parts in two loop
variables rather than a `ComplexFloat32`, which would be allocated at every step, and tests once per
step whether the product needs the recovery of `mul`.
-/
@[specialize] public def dotLoop (p : ComplexFloat32 → ComplexFloat32)
    (x y : Vec n) (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float32) : ComplexFloat32 :=
  if hi : i < m then
    let u := p (x.uget xo xo1 xc hxo hxo1 hxc hs.1 i (hm ▸ hi))
    let v := y.uget yo yo1 yc hyo hyo1 hyc hs.2 i (hm ▸ hi)
    let tr := u.re * v.re - u.im * v.im
    let ti := u.re * v.im + u.im * v.re
    let ok := tr == tr || ti == ti
    dotLoop p x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm (i + 1)
      (sr + if ok then tr else mulRecoverRe u.re u.im v.re v.im)
      (si + if ok then ti else mulRecoverIm u.re u.im v.re v.im)
  else ⟨sr, si⟩
termination_by m.toNat - i.toNat
decreasing_by
  grind

private theorem dotLoop_eq (p : ComplexFloat32 → ComplexFloat32) (x y : Vec n)
    (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float32) (j : Nat) (hj : i.toNat = j)
    (hjn : j ≤ n) (hacc : Nat.fold j (fun l hl s => s + mul (p x[l]) y[l]) zero = ⟨sr, si⟩) :
    dotLoop p x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm i sr si =
      Nat.fold n (fun l hl s => s + mul (p x[l]) y[l]) zero := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i sr si j with
  | zero =>
    rw [dotLoop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    rw [dotLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem]
    subst hj
    refine ih (i + 1) _ _ (i.toNat + 1) hsucc (by lia) ?_ (by lia)
    rw [Nat.fold_succ, hacc]
    simp only [mul, mulRecoverRe, mulRecoverIm]
    split <;> rfl

/--
The loop of `dotLoop` with the textbook products only, and the flag `ok`, which stays `true` while
no product needed the recovery of `mul`. When it ends `true`, the sum is that of `dotLoop`, and
the loop is faster without a branch per step.
-/
@[specialize] public def dotFast (p : ComplexFloat32 → ComplexFloat32)
    (x y : Vec n) (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float32) (ok : Bool) :
    ComplexFloat32 × Bool :=
  if hi : i < m then
    let u := p (x.uget xo xo1 xc hxo hxo1 hxc hs.1 i (hm ▸ hi))
    let v := y.uget yo yo1 yc hyo hyo1 hyc hs.2 i (hm ▸ hi)
    let tr := u.re * v.re - u.im * v.im
    let ti := u.re * v.im + u.im * v.re
    dotFast p x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm (i + 1)
      (sr + tr) (si + ti) (ok && (tr == tr || ti == ti))
  else (⟨sr, si⟩, ok)
termination_by m.toNat - i.toNat
decreasing_by
  grind

private theorem dotFast_ok (p : ComplexFloat32 → ComplexFloat32) (x y : Vec n)
    (xo xo1 xc yo yo1 yc : USize) (hxo : (2 * x.off).toUSize = xo)
    (hxo1 : (2 * x.off + 1).toUSize = xo1) (hxc : (2 * x.inc).toUSize = xc)
    (hyo : (2 * y.off).toUSize = yo) (hyo1 : (2 * y.off + 1).toUSize = yo1)
    (hyc : (2 * y.inc).toUSize = yc) (hs : x.data.size < USize.size ∧ y.data.size < USize.size)
    (m : USize) (hm : m.toNat = n) (i : USize) (sr si : Float32) (ok : Bool)
    (h : (dotFast p x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm i sr si ok).2) :
    ok ∧ (dotFast p x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm i sr si ok).1 =
      dotLoop p x y xo xo1 xc yo yo1 yc hxo hxo1 hxc hyo hyo1 hyc hs m hm i sr si := by
  obtain ⟨d, hd⟩ : ∃ d, m.toNat - i.toNat = d := ⟨_, rfl⟩
  induction d generalizing i sr si ok with
  | zero =>
    have hi : ¬ i < m := by grind
    rw [dotFast, dite_eq_right_of_eq_false (eq_false hi)] at h ⊢
    rw [dotLoop, dite_eq_right_of_eq_false (eq_false hi)]
    exact ⟨h, rfl⟩
  | succ d ih =>
    have hi : i < m := by grind
    rw [dotFast, dite_eq_left_of_eq_true (eq_true hi)] at h ⊢
    rw [dotLoop, dite_eq_left_of_eq_true (eq_true hi)]
    obtain ⟨h₁, h₂⟩ := ih (i + 1) _ _ _ h (by grind)
    simp only [Bool.and_eq_true] at h₁
    refine ⟨h₁.1, h₂.trans ?_⟩
    simp only [h₁.2, ite_true]

/--
`Nat.fold n (fun i _ s => s + mul (p x[i]) y[i]) 0`, by `dotFast`, or by `dotLoop` when a product
needed the recovery of `mul`.
-/
@[inline] public def dotWith (p : ComplexFloat32 → ComplexFloat32) (x y : Vec n) : ComplexFloat32 :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let r := dotFast p x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hs n.toUSize
      (x.toNat_toUSize hs.1) 0 0 0 true
    if r.2 then r.1
    else
      dotLoop p x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hs n.toUSize (x.toNat_toUSize hs.1)
        0 0 0
  else Nat.fold n (fun i _ s => s + mul (p x[i]) y[i]) zero

public theorem dotWith_eq (p : ComplexFloat32 → ComplexFloat32) (x y : Vec n) :
    dotWith p x y = Nat.fold n (fun i _ s => s + mul (p x[i]) y[i]) zero := by
  unfold dotWith
  split
  · rw [← dotLoop_eq p x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl _ _ _ 0 0 0 0
      (by simp) (by lia) (by simp [zero])]
    dsimp only
    split
    · exact (dotFast_ok p x y _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl _ _ _ _ _ _ _
      (by assumption)).2
    · rfl
  · rfl

/--
The unconjugated dot product `x[0] * y[0] + … + x[n - 1] * y[n - 1]`, with the product `mul`,
summed from the left from `0`, as `cdotu` in the reference BLAS.
-/
public def dotu (x y : Vec n) : ComplexFloat32 := dotWith id x y

public theorem dotu_eq (x y : Vec n) :
    dotu x y = Nat.fold n (fun i _ s => s + mul x[i] y[i]) zero :=
  dotWith_eq id ..

/--
The conjugated dot product `conj x[0] * y[0] + … + conj x[n - 1] * y[n - 1]`, with the product
`mul`, summed from the left from `0`, as `cdotc` in the reference BLAS.
-/
public def dotc (x y : Vec n) : ComplexFloat32 :=
  dotWith ComplexFloat32.conj x y

public theorem dotc_eq (x y : Vec n) :
    dotc x y = Nat.fold n (fun i _ s => s + mul x[i].conj y[i]) zero :=
  dotWith_eq ComplexFloat32.conj ..

/-! ## `asum` -/

/--
The sum `abs1 x[0] + … + abs1 x[n - 1]` of the absolute values `|re| + |im|` of the elements,
summed from the left, as `scasum` in the reference BLAS. It is not the sum of their moduli.
-/
public def asum (x : Vec n) : Float32 :=
  if hs : x.data.size < USize.size then
    let o := (2 * x.off).toUSize
    let o1 := (2 * x.off + 1).toUSize
    let c := (2 * x.inc).toUSize
    BLAS.Float32.foldUpTo n (fun i h s => s + abs1 x[i])
      (fun i h s => s + abs1 (x.uget o o1 c rfl rfl rfl hs i h)) 0
  else Nat.fold n (fun i h s => s + abs1 x[i]) 0

public theorem asum_eq (x : Vec n) : asum x = Nat.fold n (fun i h s => s + abs1 x[i]) 0 := by
  unfold asum; split
  · exact BLAS.Float32.foldUpTo_eq _ _ _ (by simp) _
  · rfl

/-! ## `nrm2` -/

/--
One part of a step of `nrm2`: it adds the square of `ax`, scaled, to the accumulator of its
range, in the sums `(asml, amed, abig)` of the small, mid-range and big parts, as the real `nrm2`
does for an element (`BLAS.Float32.Vec.nrm2Step`).
-/
@[inline, expose] public def blueAdd (ax : Float32) (s : Float32 × Float32 × Float32) :
    Float32 × Float32 × Float32 :=
  if ax > BLAS.Float32.Blue.tbig then
    (s.1, s.2.1, s.2.2 + ax * BLAS.Float32.Blue.sbig * (ax * BLAS.Float32.Blue.sbig))
  else if ax < BLAS.Float32.Blue.tsml then
    (s.1 + ax * BLAS.Float32.Blue.ssml * (ax * BLAS.Float32.Blue.ssml), s.2.1, s.2.2)
  else (s.1, s.2.1 + ax * ax, s.2.2)

/--
One step of `nrm2`, as in `scnrm2.f90`: it adds the squares of the real part of `x[i]` and then of
its imaginary part.
-/
@[inline, expose] public def nrm2Step (x : Vec n) (i : Nat) (h : i < n)
    (s : Float32 × Float32 × Float32) : Float32 × Float32 × Float32 :=
  blueAdd x[i].im.abs (blueAdd x[i].re.abs s)

/--
`blueAdd ax (asml, amed, abig)`, passed on to the continuation `k` as three `Float32`s, so that a
loop can keep the sums in its variables rather than in a tuple, which would be allocated at every
step.
-/
@[inline] public def blueAddK {β : Type} (ax asml amed abig : Float32)
    (k : Float32 → Float32 → Float32 → β) : β :=
  if ax > BLAS.Float32.Blue.tbig then
    k asml amed (abig + ax * BLAS.Float32.Blue.sbig * (ax * BLAS.Float32.Blue.sbig))
  else if ax < BLAS.Float32.Blue.tsml then
    k (asml + ax * BLAS.Float32.Blue.ssml * (ax * BLAS.Float32.Blue.ssml)) amed abig
  else k asml (amed + ax * ax) abig

public theorem blueAddK_eq {β : Type} (ax asml amed abig : Float32)
    (k : Float32 → Float32 → Float32 → β) :
    blueAddK ax asml amed abig k =
      k (blueAdd ax (asml, amed, abig)).1 (blueAdd ax (asml, amed, abig)).2.1
        (blueAdd ax (asml, amed, abig)).2.2 := by
  unfold blueAddK blueAdd
  split
  · rfl
  · split <;> rfl

/--
The loop of `nrm2` from the index `i`, up to the bound `m`, which is `n`, with the sums `asml`,
`amed` and `abig`, kept in three loop variables.
-/
public def nrm2Loop (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (m : USize) (hm : m.toNat = n)
    (i : USize) (asml amed abig : Float32) : Float32 × Float32 × Float32 :=
  if hi : i < m then
    let z := x.uget o o1 c ho ho1 hc hs i (hm ▸ hi)
    blueAddK z.re.abs asml amed abig fun asml amed abig =>
      blueAddK z.im.abs asml amed abig fun asml amed abig =>
        nrm2Loop x o o1 c ho ho1 hc hs m hm (i + 1) asml amed abig
  else (asml, amed, abig)
termination_by m.toNat - i.toNat
decreasing_by
  all_goals grind

private theorem nrm2Loop_eq (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (m : USize)
    (hm : m.toNat = n) (i : USize) (asml amed abig : Float32) (j : Nat) (hj : i.toNat = j)
    (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl => nrm2Step x l (by lia)) (0, 0, 0) = (asml, amed, abig)) :
    nrm2Loop x o o1 c ho ho1 hc hs m hm i asml amed abig =
      Nat.fold n (nrm2Step x) (0, 0, 0) := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i asml amed abig j with
  | zero =>
    rw [nrm2Loop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    rw [nrm2Loop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem, blueAddK_eq]
    subst hj
    have hstep : Nat.fold (i.toNat + 1) (fun l hl => nrm2Step x l (by lia)) (0, 0, 0) =
        nrm2Step x i.toNat (by lia) (asml, amed, abig) := by
      rw [Nat.fold_succ, hacc]
    exact ih (i + 1) _ _ _ (i.toNat + 1) hsucc (by lia) (by rw [hstep]; rfl) (by lia)

/--
The Euclidean norm `√(|x[0]|² + … + |x[n - 1]|²)`, by Blue's algorithm, as `scnrm2.f90` in the
reference BLAS: the squares of the real and imaginary parts of the elements, in this order, go to
the accumulators of the real `nrm2`, which it then combines by `BLAS.Float32.Vec.nrm2Finish`. It
overflows or underflows only when the norm does.
-/
public def nrm2 (x : Vec n) : Float32 :=
  BLAS.Float32.Vec.nrm2Finish <|
    if hs : x.data.size < USize.size then
      nrm2Loop x _ _ _ rfl rfl rfl hs n.toUSize (x.toNat_toUSize hs) 0 0 0 0
    else Nat.fold n (nrm2Step x) (0, 0, 0)

/--
`nrm2 x` is `nrm2Finish` of the sums of the scaled squares, accumulated from the left by
`nrm2Step`.
-/
public theorem nrm2_eq (x : Vec n) :
    nrm2 x = BLAS.Float32.Vec.nrm2Finish (Nat.fold n (nrm2Step x) (0, 0, 0)) := by
  unfold nrm2
  split
  · rw [nrm2Loop_eq x _ _ _ rfl rfl rfl _ _ _ 0 0 0 0 0 (by simp) (by lia) (by simp)]
  · rfl

/-! ## `iamax` -/

/-!
`iamax` follows `icamax.f90` of the reference BLAS (after LAPACK 3.12.1). It returns the index of
the first element with a `NaN` part, if there is one; otherwise of the first element with an
infinite part, if there is one; and otherwise of the first element of largest `|re| + |im|`. That
sum may overflow for finite parts: from the first element where it does, the reference BLAS
compares `0.25 * |re| + 0.25 * |im|` (`quarter`) instead, for that element and the later ones.

The state of the model is `(k, smax, mode)`: the index and the value of the largest element so
far, and the mode, `0` before any sum overflows, `1` after one has, `2` after an infinite part,
when only a later `NaN` can change the index, and `3` after a `NaN`, when nothing can.
-/

/-- One step of `iamax`, from the state `(k, smax, mode)`. -/
@[expose] public def iamaxStep (x : Vec n) (i : Nat) (h : i < n) (st : Nat × Float32 × Nat) :
    Nat × Float32 × Nat :=
  let z := x[i]
  if st.2.2 = 3 then st
  else if st.2.2 = 2 then if z.re.isNaN || z.im.isNaN then (i, st.2.1, 3) else st
  else if z.re.abs ≤ BLAS.Float32.Blue.maxN ∧ z.im.abs ≤ BLAS.Float32.Blue.maxN then
    if st.2.2 = 0 then
      let v := z.re.abs + z.im.abs
      if v > BLAS.Float32.Blue.maxN then (i, quarter * z.re.abs + quarter * z.im.abs, 1)
      else if v > st.2.1 then (i, v, 0) else st
    else
      let v := quarter * z.re.abs + quarter * z.im.abs
      if v > st.2.1 then (i, v, 1) else st
  else if z.re.isNaN || z.im.isNaN then (i, st.2.1, 3)
  else (i, st.2.1, 2)

/--
The loop of `iamax` after an element with an infinite part, at the index `k`, from the index `i`
up to the bound `m`, which is `n`: it returns the index of the first later element with a `NaN`
part, or `k`.
-/
public def iamaxNaNLoop (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (m : USize)
    (hm : m.toNat = n) (i k : USize) : Nat :=
  if hi : i < m then
    let z := x.uget o o1 c ho ho1 hc hs i (hm ▸ hi)
    if z.re.isNaN || z.im.isNaN then i.toNat
    else iamaxNaNLoop x o o1 c ho ho1 hc hs m hm (i + 1) k
  else k.toNat
termination_by m.toNat - i.toNat
decreasing_by
  grind

/--
The loop of `iamax` from the index `i`, up to the bound `m`, which is `n`, with the index `k` and
value `smax` of the largest element so far, and whether a sum has overflowed. It returns at the
first `NaN` part, as the reference BLAS does, and goes on to `iamaxNaNLoop` at the first infinite
part.
-/
public def iamaxLoop (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (m : USize) (hm : m.toNat = n)
    (i k : USize) (smax : Float32) (scaled : Bool) : Nat :=
  if hi : i < m then
    let z := x.uget o o1 c ho ho1 hc hs i (hm ▸ hi)
    let ar := z.re.abs
    let ai := z.im.abs
    if ar ≤ BLAS.Float32.Blue.maxN ∧ ai ≤ BLAS.Float32.Blue.maxN then
      if !scaled then
        let v := ar + ai
        if v > BLAS.Float32.Blue.maxN then
          iamaxLoop x o o1 c ho ho1 hc hs m hm (i + 1) i (quarter * ar + quarter * ai) true
        else if v > smax then iamaxLoop x o o1 c ho ho1 hc hs m hm (i + 1) i v false
        else iamaxLoop x o o1 c ho ho1 hc hs m hm (i + 1) k smax false
      else
        let v := quarter * ar + quarter * ai
        if v > smax then iamaxLoop x o o1 c ho ho1 hc hs m hm (i + 1) i v true
        else iamaxLoop x o o1 c ho ho1 hc hs m hm (i + 1) k smax true
    else if z.re.isNaN || z.im.isNaN then i.toNat
    else iamaxNaNLoop x o o1 c ho ho1 hc hs m hm (i + 1) i
  else k.toNat
termination_by m.toNat - i.toNat
decreasing_by
  all_goals grind

/-- Once a `NaN` is found, the steps of `iamax` keep the state. -/
private theorem fold_iamaxStep_of_done (x : Vec n) {j : Nat} {st : Nat × Float32 × Nat}
    (hst : st.2.2 = 3) (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) = st) :
    ∀ N (_ : j ≤ N) (hN : N ≤ n),
      Nat.fold N (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) = st
  | 0, hj, _ => by obtain rfl : j = 0 := by lia
                   exact hacc
  | N + 1, hjN, hN => by
    by_cases e : j = N + 1
    · subst e; exact hacc
    · rw [Nat.fold_succ, fold_iamaxStep_of_done x hst hjn hacc N (by lia) (by lia)]
      simp [iamaxStep, hst]

private theorem iamaxNaNLoop_eq (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (m : USize)
    (hm : m.toNat = n) (i k : USize) (smax : Float32) (j : Nat) (hj : i.toNat = j) (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) = (k.toNat, smax, 2)) :
    iamaxNaNLoop x o o1 c ho ho1 hc hs m hm i k =
      (Nat.fold n (iamaxStep x) (0, -1, 0)).1 := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i j with
  | zero =>
    rw [iamaxNaNLoop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    rw [iamaxNaNLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem]
    subst hj
    have hstep : Nat.fold (i.toNat + 1) (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) =
        iamaxStep x i.toNat (by lia) (k.toNat, smax, 2) := by
      rw [Nat.fold_succ, hacc]
    split
    next hn =>
      have hnext : Nat.fold (i.toNat + 1) (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) =
          (i.toNat, smax, 3) := by
        rw [hstep]; simp only [iamaxStep, hn]; simp
      rw [fold_iamaxStep_of_done x (by rfl) (by lia) hnext n (by lia) (Nat.le_refl _)]
    next hn =>
      refine ih (i + 1) (i.toNat + 1) hsucc (by lia) ?_ (by lia)
      rw [hstep]; simp only [iamaxStep, hn]; simp

private theorem iamaxLoop_eq (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (m : USize)
    (hm : m.toNat = n) (i k : USize) (smax : Float32) (scaled : Bool) (j : Nat) (hj : i.toNat = j)
    (hjn : j ≤ n)
    (hacc : Nat.fold j (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) =
      (k.toNat, smax, if scaled then 1 else 0)) :
    iamaxLoop x o o1 c ho ho1 hc hs m hm i k smax scaled =
      (Nat.fold n (iamaxStep x) (0, -1, 0)).1 := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d := ⟨_, rfl⟩
  induction d generalizing i k smax scaled j with
  | zero =>
    rw [iamaxLoop, dite_eq_right_of_eq_false (eq_false (by grind))]
    obtain rfl : j = n := by lia
    rw [hacc]
  | succ d ih =>
    have hi : i < m := by grind
    have hsucc : (i + 1).toNat = j + 1 := by grind
    rw [iamaxLoop, dite_eq_left_of_eq_true (eq_true hi)]
    simp only [uget_eq_getElem]
    subst hj
    have hstep : Nat.fold (i.toNat + 1) (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) =
        iamaxStep x i.toNat (by lia) (k.toNat, smax, if scaled then 1 else 0) := by
      rw [Nat.fold_succ, hacc]
    have hm3 : (if scaled then 1 else 0) ≠ 3 := by split <;> decide
    have hm2 : (if scaled then 1 else 0) ≠ 2 := by split <;> decide
    split
    next hf =>
      cases scaled
      · simp only [Bool.not_false, ↓reduceIte]
        by_cases hv : x[i.toNat].re.abs + x[i.toNat].im.abs > BLAS.Float32.Blue.maxN
        · simp only [hv, ↓reduceIte]
          refine ih (i + 1) i _ true (i.toNat + 1) hsucc (by lia) ?_ (by lia)
          rw [hstep]; simp only [iamaxStep, hm3, hf, hm2, hv]; simp
        · simp only [hv, ↓reduceIte]
          by_cases hv' : x[i.toNat].re.abs + x[i.toNat].im.abs > smax
          · simp only [hv', ↓reduceIte]
            refine ih (i + 1) i _ false (i.toNat + 1) hsucc (by lia) ?_ (by lia)
            rw [hstep]; simp only [iamaxStep, hm3, hf, hm2, hv, hv']; simp
          · simp only [hv', ↓reduceIte]
            refine ih (i + 1) k smax false (i.toNat + 1) hsucc (by lia) ?_ (by lia)
            rw [hstep]; simp only [iamaxStep, hm3, hf, hm2, hv, hv']; simp
      · simp only [Bool.not_true]
        by_cases hv : quarter * x[i.toNat].re.abs + quarter * x[i.toNat].im.abs > smax
        · simp only [hv, ↓reduceIte]
          refine ih (i + 1) i _ true (i.toNat + 1) hsucc (by lia) ?_ (by lia)
          rw [hstep]; simp only [iamaxStep, hf, hv]; simp
        · simp only [hv, ↓reduceIte]
          refine ih (i + 1) k smax true (i.toNat + 1) hsucc (by lia) ?_ (by lia)
          rw [hstep]; simp only [iamaxStep, hf, hv]; simp
    next hf =>
      split
      next hn =>
        have hnext : Nat.fold (i.toNat + 1) (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) =
            (i.toNat, smax, 3) := by
          rw [hstep]; simp only [iamaxStep, hm3, hf, hn]; simp
        rw [fold_iamaxStep_of_done x (by rfl) (by lia) hnext n (by lia) (Nat.le_refl _)]
      next hn =>
        refine iamaxNaNLoop_eq x o o1 c ho ho1 hc hs m hm (i + 1) i smax (i.toNat + 1) hsucc
          (by lia) ?_
        rw [hstep]; simp only [iamaxStep, hm3, hf, hn, hm2]; simp

/--
The index of the first element with a `NaN` part, or else of the first with an infinite part, or
else of the first of largest `|re| + |im|`, as `icamax` in the reference BLAS, but starting at `0`;
it is `0` for the empty vector. `iamax` and `iamax?` return the same index as a `Fin n`.
-/
public def iamax! (x : Vec n) : Nat :=
  if hs : x.data.size < USize.size then
    iamaxLoop x _ _ _ rfl rfl rfl hs n.toUSize (x.toNat_toUSize hs) 0 0 (-1) false
  else (Nat.fold n (iamaxStep x) (0, -1, 0)).1

public theorem iamax!_eq (x : Vec n) : iamax! x = (Nat.fold n (iamaxStep x) (0, -1, 0)).1 := by
  unfold iamax!
  split
  · exact iamaxLoop_eq x _ _ _ rfl rfl rfl _ _ _ 0 0 (-1) false 0 (by simp) (by lia) (by simp)
  · rfl

/-- The steps of `iamax` keep an index below the number of steps. -/
private theorem fst_fold_iamaxStep_lt (x : Vec n) :
    ∀ N (hN : N ≤ n), 0 < N →
      (Nat.fold N (fun l hl => iamaxStep x l (by lia)) (0, -1, 0)).1 < N
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | N + 1, hN, _ => by
    have ih : (Nat.fold N (fun l hl => iamaxStep x l (by lia)) (0, -1, 0)).1 = 0 ∨
        (Nat.fold N (fun l hl => iamaxStep x l (by lia)) (0, -1, 0)).1 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; exact .inl (by simp)
      · exact .inr (fst_fold_iamaxStep_lt x N (by lia) h)
    rw [Nat.fold_succ]
    generalize Nat.fold N (fun l hl => iamaxStep x l (by lia)) (0, -1, 0) = b at ih ⊢
    simp only [iamaxStep]
    repeat' split
    all_goals (try simp only)
    all_goals lia

/-- `iamax! x` is an index of `x`, unless `x` is empty. -/
public theorem iamax!_lt (x : Vec n) (h : n ≠ 0) : iamax! x < n := by
  rw [iamax!_eq]
  exact fst_fold_iamaxStep_lt x n (Nat.le_refl n) (by lia)

/--
The index of the first element with a `NaN` part, or else of the first with an infinite part, or
else of the first of largest `|re| + |im|`, of a nonempty vector, as `icamax` in the reference
BLAS, but starting at `0`. It is `iamax! x`, as a `Fin n`.
-/
@[expose] public def iamax (x : Vec n) (h : n ≠ 0 := by grind) : Fin n :=
  ⟨iamax! x, iamax!_lt x h⟩

@[simp] public theorem val_iamax (x : Vec n) (h : n ≠ 0) : (iamax x h).val = iamax! x := rfl

/-- `iamax`, or `none` for the empty vector. -/
@[expose] public def iamax? (x : Vec n) : Option (Fin n) :=
  if h : n = 0 then none else some (iamax x h)

@[simp] public theorem iamax?_eq_none_iff (x : Vec n) : iamax? x = none ↔ n = 0 := by
  unfold iamax?; split <;> simp_all

public theorem iamax?_eq_some (x : Vec n) (h : n ≠ 0) : iamax? x = some (iamax x h) := by
  simp [iamax?, h]

end Vec

end BLAS.ComplexFloat32
