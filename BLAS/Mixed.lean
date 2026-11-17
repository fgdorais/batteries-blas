/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32

/-!
# Mixed precision

The reference BLAS routines that take `Float32` vectors and compute in `Float`: `dsdot` and
`sdsdot`, the dot products of single precision vectors summed in double precision. They have no
`Float64` version, so they are written by hand, unlike the rest of `BLAS.Float32`, which
`scripts/generate.py` generates from `BLAS.Float64`.
-/

open ScalarArray

namespace BLAS.Float32

namespace Vec

variable {n : Nat}

/--
The dot product of `x` and `y` in `Float`, added to `init` from the left:
`init + x[0] * y[0] + … + x[n - 1] * y[n - 1]`, where each product is of the elements converted to
`Float`, so that it is exact.
-/
public def dsdotFrom (init : Float) (x y : Vec n) : Float :=
  if hs : x.data.size < USize.size ∧ y.data.size < USize.size then
    let xo := x.off.toUSize
    let xc := x.inc.toUSize
    let yo := y.off.toUSize
    let yc := y.inc.toUSize
    foldUpTo n (fun i h s => s + x[i].toFloat * y[i].toFloat)
      (fun i h s => s + (x.uget xo xc rfl rfl hs.1 i h).toFloat *
        (y.uget yo yc rfl rfl hs.2 i h).toFloat) init
  else Nat.fold n (fun i h s => s + x[i].toFloat * y[i].toFloat) init

public theorem dsdotFrom_eq (init : Float) (x y : Vec n) :
    dsdotFrom init x y = Nat.fold n (fun i h s => s + x[i].toFloat * y[i].toFloat) init := by
  unfold dsdotFrom; split
  · exact foldUpTo_eq _ _ _ (by simp) _
  · rfl

/--
`dsdot x y` is the dot product of the `Float32` vectors `x` and `y`, summed in `Float` from the
left, as the reference `dsdot`: `x[0] * y[0] + … + x[n - 1] * y[n - 1]`, with the elements
converted to `Float`.
-/
public def dsdot (x y : Vec n) : Float := dsdotFrom 0 x y

public theorem dsdot_eq (x y : Vec n) :
    dsdot x y = Nat.fold n (fun i h s => s + x[i].toFloat * y[i].toFloat) 0 :=
  dsdotFrom_eq 0 x y

/--
`sdsdot sb x y` is `sb` plus the dot product of the `Float32` vectors `x` and `y`, summed in
`Float` from `sb`, and rounded to `Float32` once at the end, as the reference `sdsdot`.
-/
public def sdsdot (sb : Float32) (x y : Vec n) : Float32 := (dsdotFrom sb.toFloat x y).toFloat32

public theorem sdsdot_eq (sb : Float32) (x y : Vec n) :
    sdsdot sb x y =
      (Nat.fold n (fun i h s => s + x[i].toFloat * y[i].toFloat) sb.toFloat).toFloat32 := by
  rw [sdsdot, dsdotFrom_eq]

end Vec

end BLAS.Float32
