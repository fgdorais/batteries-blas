/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Level1
public import BatteriesBLAS.Float64.Rot

/-!
# Complex plane rotations

`rot c s x y` applies a plane rotation with real `c` and `s` to two complex vectors, as `zdrot` in
the reference BLAS, and `rotg a b` constructs a rotation with real `c` and complex `s`, step for
step as `zrotg.f90`.
-/

open ScalarArray Float64Array

namespace BLAS.ComplexFloat64

namespace Vec

variable {n : Nat}

/-! ## `rot` -/

/--
`rot c s x y` applies the plane rotation `[c s; -s c]` with real `c` and `s` to the pairs
`(x[i], y[i])`, as the reference `zdrot`: `x[i] ↦ c * x[i] + s * y[i]` and
`y[i] ↦ c * y[i] - s * x[i]`, where `c` and `s` are the complex numbers `(c, 0)` and `(s, 0)` and
the products are those of gfortran (`mul`), as the Fortran rules of mixed arithmetic make them.
It computes the new `x` in a copy of its array, which keeps the old `x` for the new `y`, and then
the new `y` in place when its array is not shared.
-/
@[expose] public def rot (c s : Float) : Vec n → Vec n → Vec n × Vec n
  | ⟨xd, xo, xi, xp, xb⟩, ⟨yd, yo, yi, yp, yb⟩ =>
    let x : Vec n := ⟨xd, xo, xi, xp, xb⟩
    let y : Vec n := ⟨yd, yo, yi, yp, yb⟩
    let c' := ofReal c
    let s' := ofReal s
    let xd' := zipWithData (fun u w => mulRe c' u + mulRe s' w) (fun u w => mulIm c' u + mulIm s' w)
      y x
    let yd' := zipWithData (fun v w => mulRe c' v - mulRe s' w) (fun v w => mulIm c' v - mulIm s' w)
      x y
    ({ data := xd', off := xo, inc := xi, inc_pos := xp,
       bound := by rw [size_zipWithData]; exact xb },
     { data := yd', off := yo, inc := yi, inc_pos := yp,
       bound := by rw [size_zipWithData]; exact yb })

@[simp] public theorem getElem_rot_fst (c s : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (rot c s x y).1[i] = mul (ofReal c) x[i] + mul (ofReal s) y[i] := by
  obtain ⟨xd, xo, xi, xp, xb⟩ := x
  obtain ⟨yd, yo, yi, yp, yb⟩ := y
  rw [getElem_of_data_eq_zipWithData (v := (rot c s _ _).1) _ _ ⟨yd, yo, yi, yp, yb⟩
    ⟨xd, xo, xi, xp, xb⟩ rfl rfl rfl i h]
  simp only [mulRe_eq, mulIm_eq]
  rfl

@[simp] public theorem getElem_rot_snd (c s : Float) (x y : Vec n) (i : Nat) (h : i < n) :
    (rot c s x y).2[i] = mul (ofReal c) y[i] - mul (ofReal s) x[i] := by
  obtain ⟨xd, xo, xi, xp, xb⟩ := x
  obtain ⟨yd, yo, yi, yp, yb⟩ := y
  rw [getElem_of_data_eq_zipWithData (v := (rot c s _ _).2) _ _
    ⟨xd, xo, xi, xp, xb⟩ ⟨yd, yo, yi, yp, yb⟩ rfl rfl rfl i h]
  simp only [mulRe_eq, mulIm_eq]
  rfl

end Vec

/-! ## `rotg` -/

/--
The result of `rotg a b`: `r`, which the reference `zrotg` returns in `a`, the real cosine `c` and
the complex sine `s`, with `c * a + s * b = r` and `-conj s * a + c * b = 0`.
-/
public structure Rotg where
  /-- The rotated `a`. -/
  r : ComplexFloat
  /-- The cosine, real. -/
  c : Float
  /-- The sine. -/
  s : ComplexFloat
deriving Inhabited, Repr

namespace Rotg

/-- `|re|² + |im|²`, the reference `ABSSQ`. -/
@[inline, expose] public def absSq (z : ComplexFloat) : Float := z.re * z.re + z.im * z.im

/-- The square root of `safmin`, the reference `rtmin`. -/
@[expose] public def rtmin : Float := BLAS.Float64.Rotg.safmin.sqrt

end Rotg

open Rotg in
open BLAS.Float64.Rotg (fmax fmin safmin safmax) in
/--
`rotg a b` constructs the plane rotation that zeros `b`, step for step as the reference
`zrotg.f90` (the Anderson 2017 version), with scaling so that nothing overflows or underflows
unless the result does. As gfortran compiles it, a real number that divides or multiplies a
complex one is the complex number `(r, 0)`, the quotients are those of `__divdc3` (`div`) and the
products those of `mul`.
-/
@[expose] public def rotg (a b : ComplexFloat) : Rotg :=
  let f := a
  let g := b
  if g.re == 0 && g.im == 0 then { r := f, c := 1, s := zero }
  else if f.re == 0 && f.im == 0 then
    if g.re == 0 then
      let r := g.im.abs
      { r := ofReal r, c := 0, s := div g.conj (ofReal r) }
    else if g.im == 0 then
      let r := g.re.abs
      { r := ofReal r, c := 0, s := div g.conj (ofReal r) }
    else
      let g1 := fmax g.re.abs g.im.abs
      let rtmax := (safmax / 2).sqrt
      if g1 > rtmin && g1 < rtmax then
        let g2 := absSq g
        let d := g2.sqrt
        { r := ofReal d, c := 0, s := div g.conj (ofReal d) }
      else
        let u := fmin safmax (fmax safmin g1)
        let gs := div g (ofReal u)
        let g2 := absSq gs
        let d := g2.sqrt
        { r := ofReal (d * u), c := 0, s := div gs.conj (ofReal d) }
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
        let r := div f (ofReal c)
        let rtmax := rtmax * 2
        if f2 > rtmin && h2 < rtmax then
          { r, c, s := mul g.conj (div f (ofReal (f2 * h2).sqrt)) }
        else { r, c, s := mul g.conj (div r (ofReal h2)) }
      else
        let d := (f2 * h2).sqrt
        let c := f2 / d
        let r := if c ≥ safmin then div f (ofReal c) else mul f (ofReal (h2 / d))
        { r, c, s := mul g.conj (div f (ofReal d)) }
    else
      let u := fmin safmax (fmax (fmax safmin f1) g1)
      let gs := div g (ofReal u)
      let g2 := absSq gs
      let (w, fs, f2, h2) :=
        if f1 / u < rtmin then
          let v := fmin safmax (fmax safmin f1)
          let w := v / u
          let fs := div f (ofReal v)
          let f2 := absSq fs
          (w, fs, f2, f2 * (w * w) + g2)
        else
          let fs := div f (ofReal u)
          let f2 := absSq fs
          ((1 : Float), fs, f2, f2 + g2)
      let (c₁, r₁, s₁) :=
        if f2 ≥ h2 * safmin then
          let c := (f2 / h2).sqrt
          let r := div fs (ofReal c)
          let rtmax := rtmax * 2
          if f2 > rtmin && h2 < rtmax then (c, r, mul gs.conj (div fs (ofReal (f2 * h2).sqrt)))
          else (c, r, mul gs.conj (div r (ofReal h2)))
        else
          let d := (f2 * h2).sqrt
          let c := f2 / d
          let r := if c ≥ safmin then div fs (ofReal c) else mul fs (ofReal (h2 / d))
          (c, r, mul gs.conj (div fs (ofReal d)))
      { r := mul r₁ (ofReal u), c := c₁ * w, s := s₁ }

end BLAS.ComplexFloat64
