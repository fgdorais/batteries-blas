/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Level1
public import BatteriesBLAS.Float32.Rot

/-!
# Complex plane rotations

`rot c s x y` applies a plane rotation with real `c` and `s` to two complex vectors, as `csrot` in
the reference BLAS, and `rotg a b` constructs a rotation with real `c` and complex `s`, step for
step as `crotg.f90`.
-/

open ScalarArray Float32Array

namespace BLAS.ComplexFloat32

namespace Vec

variable {n : Nat}

/-! ## `rot` -/

/--
The arrays of `rot c s x y`. A real `c` or `s` times a complex number multiplies both of its
parts, so the real and the imaginary parts rotate independently: this rotates the real parts of
`x` and `y` together, by scalar-arrays' `zipModifyStride`, and then their imaginary parts.
-/
public def rotData (c s : Float32) (x y : Vec n) : Float32Array × Float32Array :=
  let d := zipModifyStride x.data y.data x.reStride y.reStride n (fun u v => c * u + s * v)
    (fun u v => c * v - s * u) x.fits_re y.fits_re
  zipModifyStride d.1 d.2 x.imStride y.imStride n (fun u v => c * u + s * v)
    (fun u v => c * v - s * u) (by rw [size_zipModifyStride_fst]; exact x.fits_im)
    (by rw [size_zipModifyStride_snd]; exact y.fits_im)

@[simp] public theorem size_rotData_fst (c s : Float32) (x y : Vec n) :
    (rotData c s x y).1.size = x.data.size := by
  simp [rotData]

@[simp] public theorem size_rotData_snd (c s : Float32) (x y : Vec n) :
    (rotData c s x y).2.size = y.data.size := by
  simp [rotData]

/-- The arrays of `rotData`, as two `modifyAt`s each, at the real and then the imaginary parts. -/
public theorem rotData_eq (c s : Float32) (x y : Vec n) :
    rotData c s x y =
      ((x.data.modifyAt x.reStride.idx 0 n fun k u => c * u + s * y.data[y.reStride.idx k]!)
          |>.modifyAt x.imStride.idx 0 n fun k u => c * u + s * y.data[y.imStride.idx k]!,
        (y.data.modifyAt y.reStride.idx 0 n fun k v => c * v - s * x.data[x.reStride.idx k]!)
          |>.modifyAt y.imStride.idx 0 n fun k v => c * v - s * x.data[x.imStride.idx k]!) := by
  simp only [rotData, zipModifyStride_eq]
  rw [zipModifyAt_eq _ _ _ _ (fun _ _ hi _ _ hj e => x.fits_re.idx_inj hi hj e)
      (fun _ _ hi _ _ hj e => y.fits_re.idx_inj hi hj e),
    zipModifyAt_eq _ _ _ _ (fun _ _ hi _ _ hj e => x.fits_im.idx_inj hi hj e)
      (fun _ _ hi _ _ hj e => y.fits_im.idx_inj hi hj e)]
  congr 1
  · exact BLAS.Float32.modifyAt_congr_fun _ _ fun k u _ _ => by
      rw [BLAS.Float32.getElem!_modifyAt_of_ne _ _ _ (fun j _ _ e => y.re_ne_im j k e)]
  · exact BLAS.Float32.modifyAt_congr_fun _ _ fun k v _ _ => by
      rw [BLAS.Float32.getElem!_modifyAt_of_ne _ _ _ (fun j _ _ e => x.re_ne_im j k e)]

/-- A part of an element after two `modifyAt`s at the real and imaginary parts of a vector. -/
private theorem getElem!_modifyAt_re_im (x : Vec n) {a : Float32Array} (ha : a.size = x.data.size)
    (F G : Nat → Float32 → Float32) (i : Nat) (h : i < n) :
    ((a.modifyAt x.reStride.idx 0 n F).modifyAt x.imStride.idx 0 n G)[x.reStride.idx i]! =
        F i a[x.reStride.idx i]! ∧
      ((a.modifyAt x.reStride.idx 0 n F).modifyAt x.imStride.idx 0 n G)[x.imStride.idx i]! =
        G i a[x.imStride.idx i]! := by
  have hr := x.fits_re
  have hi := x.fits_im
  rw [← ha] at hr hi
  constructor
  · rw [BLAS.Float32.getElem!_modifyAt_of_ne _ _ _ (fun j _ _ e => x.re_ne_im i j e.symm),
      getElem!_pos (a.modifyAt x.reStride.idx 0 n F) _ (by rw [size_modifyAt]; exact hr.idx_lt h),
      getElem_modifyAt_stride _ hr (Nat.le_refl _) _ (Nat.zero_le _) h,
      getElem!_pos a _ (hr.idx_lt h)]
  · rw [getElem!_pos ((a.modifyAt x.reStride.idx 0 n F).modifyAt x.imStride.idx 0 n G) _
        (by rw [size_modifyAt, size_modifyAt]; exact hi.idx_lt h),
      getElem_modifyAt_stride _ (by rw [size_modifyAt]; exact hi) (Nat.le_refl _) _
        (Nat.zero_le _) h,
      getElem_modifyAt_of_forall_ne _ _ _ (fun j _ _ e => x.re_ne_im j i e),
      getElem!_pos a _ (hi.idx_lt h)]

private theorem re_getElem! (x : Vec n) (i : Nat) (h : i < n) :
    x[i].re = x.data[x.reStride.idx i]! := by
  rw [re_getElem, getElem!_pos x.data _ (x.re_lt h)]; rfl

private theorem im_getElem! (x : Vec n) (i : Nat) (h : i < n) :
    x[i].im = x.data[x.imStride.idx i]! := by
  rw [im_getElem, getElem!_pos x.data _ (x.im_lt h)]; rfl

/--
`rot c s x y` applies the plane rotation `[c s; -s c]` with real `c` and `s` to the pairs
`(x[i], y[i])`, as the reference `csrot`: `x[i] ↦ c * x[i] + s * y[i]` and
`y[i] ↦ c * y[i] - s * x[i]`, where a real times a complex number multiplies both of its parts.
It takes `x` and `y` apart first, so that only their arrays go on to the loops and stay unshared.
-/
@[expose] public def rot (c s : Float32) : Vec n → Vec n → Vec n × Vec n
  | ⟨xd, xo, xi, xp, xb⟩, ⟨yd, yo, yi, yp, yb⟩ =>
    let d := rotData c s ⟨xd, xo, xi, xp, xb⟩ ⟨yd, yo, yi, yp, yb⟩
    have h₁ : d.1.size = xd.size := size_rotData_fst ..
    have h₂ : d.2.size = yd.size := size_rotData_snd ..
    ({ data := d.1, off := xo, inc := xi, inc_pos := xp, bound := by rw [h₁]; exact xb },
     { data := d.2, off := yo, inc := yi, inc_pos := yp, bound := by rw [h₂]; exact yb })

/-- A vector with the offset and stride of `x` and the array `a`, of the size of `x`'s. -/
private theorem getElem_of_data (x : Vec n) (v : Vec n) (ho : v.off = x.off) (hc : v.inc = x.inc)
    (i : Nat) (h : i < n) :
    v[i] = ⟨v.data[x.reStride.idx i]!, v.data[x.imStride.idx i]!⟩ := by
  rw [show v[i] = ⟨v[i].re, v[i].im⟩ from rfl, re_getElem! v i h, im_getElem! v i h]
  simp only [idx_reStride, idx_imStride, ho, hc]

@[simp] public theorem getElem_rot_fst (c s : Float32) (x y : Vec n) (i : Nat) (h : i < n) :
    (rot c s x y).1[i] = ⟨c * x[i].re + s * y[i].re, c * x[i].im + s * y[i].im⟩ := by
  have hd : (rot c s x y).1.data = (rotData c s x y).1 := by cases x; cases y; rfl
  rw [getElem_of_data x _ (by cases x; cases y; rfl) (by cases x; cases y; rfl) i h, hd,
    rotData_eq]
  obtain ⟨h₁, h₂⟩ := getElem!_modifyAt_re_im x rfl
    (fun k u => c * u + s * y.data[y.reStride.idx k]!)
    (fun k u => c * u + s * y.data[y.imStride.idx k]!) i h
  simp only [h₁, h₂, re_getElem! x i h, im_getElem! x i h, re_getElem! y i h, im_getElem! y i h]

@[simp] public theorem getElem_rot_snd (c s : Float32) (x y : Vec n) (i : Nat) (h : i < n) :
    (rot c s x y).2[i] = ⟨c * y[i].re - s * x[i].re, c * y[i].im - s * x[i].im⟩ := by
  have hd : (rot c s x y).2.data = (rotData c s x y).2 := by cases x; cases y; rfl
  rw [getElem_of_data y _ (by cases x; cases y; rfl) (by cases x; cases y; rfl) i h, hd,
    rotData_eq]
  obtain ⟨h₁, h₂⟩ := getElem!_modifyAt_re_im y rfl
    (fun k v => c * v - s * x.data[x.reStride.idx k]!)
    (fun k v => c * v - s * x.data[x.imStride.idx k]!) i h
  simp only [h₁, h₂, re_getElem! x i h, im_getElem! x i h, re_getElem! y i h, im_getElem! y i h]

end Vec

/-! ## `rotg` -/

/--
The result of `rotg a b`: `r`, which the reference `crotg` returns in `a`, the real cosine `c` and
the complex sine `s`, with `c * a + s * b = r` and `-conj s * a + c * b = 0`.
-/
public structure Rotg where
  /-- The rotated `a`. -/
  r : ComplexFloat32
  /-- The cosine, real. -/
  c : Float32
  /-- The sine. -/
  s : ComplexFloat32
deriving Inhabited, Repr

namespace Rotg

/-- `|re|² + |im|²`, the reference `ABSSQ`. -/
@[inline, expose] public def absSq (z : ComplexFloat32) : Float32 := z.re * z.re + z.im * z.im

/-- A complex number divided by a real one, both parts, as gfortran compiles it. -/
@[inline, expose] public def rdiv (z : ComplexFloat32) (d : Float32) : ComplexFloat32 :=
  ⟨z.re / d, z.im / d⟩

/-- The real number `x` as a complex one. -/
@[inline, expose] public def ofReal (x : Float32) : ComplexFloat32 := ⟨x, 0⟩

/-- The square root of `safmin`, the reference `rtmin`. -/
@[expose] public def rtmin : Float32 := BLAS.Float32.Rotg.safmin.sqrt

end Rotg

open Rotg in
open BLAS.Float32.Rotg (fmax fmin safmin safmax) in
/--
`rotg a b` constructs the plane rotation that zeros `b`, step for step as the reference
`crotg.f90` (the Anderson 2017 version), with scaling so that nothing overflows or underflows
unless the result does. The reference's complex divisions by a real number and products with one
divide or multiply both parts, as gfortran compiles them, and its products of two complex numbers
are textbook products.
-/
@[expose] public def rotg (a b : ComplexFloat32) : Rotg :=
  let f := a
  let g := b
  if g.re == 0 && g.im == 0 then { r := f, c := 1, s := zero }
  else if f.re == 0 && f.im == 0 then
    if g.re == 0 then
      let r := g.im.abs
      { r := ofReal r, c := 0, s := rdiv g.conj r }
    else if g.im == 0 then
      let r := g.re.abs
      { r := ofReal r, c := 0, s := rdiv g.conj r }
    else
      let g1 := fmax g.re.abs g.im.abs
      let rtmax := (safmax / 2).sqrt
      if g1 > rtmin && g1 < rtmax then
        let g2 := absSq g
        let d := g2.sqrt
        { r := ofReal d, c := 0, s := rdiv g.conj d }
      else
        let u := fmin safmax (fmax safmin g1)
        let gs := rdiv g u
        let g2 := absSq gs
        let d := g2.sqrt
        { r := ofReal (d * u), c := 0, s := rdiv gs.conj d }
  else
    let f1 := fmax f.re.abs f.im.abs
    let g1 := fmax g.re.abs g.im.abs
    let rtmax := (safmax / 4).sqrt
    if f1 > rtmin && f1 < rtmax && g1 > rtmin && g1 < rtmax then
      let f2 := absSq f
      let g2 := absSq g
      let h2 := f2 + g2
      if f2 ≥ h2 * safmin then
        let c := (f2 / h2).sqrt
        let r := rdiv f c
        let rtmax := rtmax * 2
        if f2 > rtmin && h2 < rtmax then
          { r, c, s := mul g.conj (rdiv f (f2 * h2).sqrt) }
        else { r, c, s := mul g.conj (rdiv r h2) }
      else
        let d := (f2 * h2).sqrt
        let c := f2 / d
        let r := if c ≥ safmin then rdiv f c else rmul (h2 / d) f
        { r, c, s := mul g.conj (rdiv f d) }
    else
      let u := fmin safmax (fmax (fmax safmin f1) g1)
      let gs := rdiv g u
      let g2 := absSq gs
      let (w, fs, f2, h2) :=
        if f1 / u < rtmin then
          let v := fmin safmax (fmax safmin f1)
          let w := v / u
          let fs := rdiv f v
          let f2 := absSq fs
          (w, fs, f2, f2 * (w * w) + g2)
        else
          let fs := rdiv f u
          let f2 := absSq fs
          ((1 : Float32), fs, f2, f2 + g2)
      let (c₁, r₁, s₁) :=
        if f2 ≥ h2 * safmin then
          let c := (f2 / h2).sqrt
          let r := rdiv fs c
          let rtmax := rtmax * 2
          if f2 > rtmin && h2 < rtmax then (c, r, mul gs.conj (rdiv fs (f2 * h2).sqrt))
          else (c, r, mul gs.conj (rdiv r h2))
        else
          let d := (f2 * h2).sqrt
          let c := f2 / d
          let r := if c ≥ safmin then rdiv fs c else rmul (h2 / d) fs
          (c, r, mul gs.conj (rdiv fs d))
      { r := rmul u r₁, c := c₁ * w, s := s₁ }

end BLAS.ComplexFloat32
