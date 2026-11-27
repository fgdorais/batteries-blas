/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesComplexFloat.ComplexFloat.Basic
public import BatteriesComplexFloat.ComplexFloat32.Basic

/-!
# Complex division of the reference BLAS

gfortran compiles a complex division to a call of `__divdc3` (`__divsc3` in single precision) of
libgcc, so the reference BLAS divides as these functions do, rather than as the division of
`ComplexFloat`. `BLAS.ComplexFloat64.div` and `BLAS.ComplexFloat32.div` are these functions, as
in `libgcc2.c` since GCC 12, with the same operations in the same order. They differ between the
precisions, so this file is written by hand rather than generated:

* `__divdc3` is Smith's algorithm: it divides by the part of the divisor that is the largest in
  absolute value, after scaling the operands by powers of two when they are near the limits of the
  range, and it computes in another order when the ratio of the parts of the divisor is subnormal;
* `__divsc3` converts its operands to `Float` and computes the textbook quotient
  `((a * c + b * d) / (c * c + d * d), (b * c - a * d) / (c * c + d * d))` there, which is exact
  enough, and rounds it to `Float32`.

Both then recover the infinities and zeros that came out as `NaN + NaN * I`: a nonzero number
divided by zero, an infinite one by a finite one, and a finite one by an infinite one. In
single precision this recovery is in `Float32`.
-/

namespace BLAS.ComplexFloat64

/-- The largest finite `Float` divided by `2`, `RBIG` of `libgcc2.c`. -/
@[expose] public def divBig : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF / 2

/-- The smallest normal `Float`, `2 ^ (-1022)`, `RMIN` of `libgcc2.c`. -/
@[expose] public def divMin : Float := Float.ofBits 0x0010000000000000

/-- The machine epsilon `2 ^ (-52)`, `RMIN2` of `libgcc2.c`. -/
@[expose] public def divMin2 : Float := Float.ofBits 0x3CB0000000000000

/-- `2 ^ 52`, the scale factor `RMINSCAL` of `libgcc2.c`. -/
@[expose] public def divScale : Float := Float.ofBits 0x4330000000000000

/-- `divBig * divMin2`, `RMAX2` of `libgcc2.c`. -/
@[expose] public def divMax2 : Float := divBig * divMin2

/--
The recovery of `__divdc3` when its quotient came out as `NaN + NaN * I`: of `a + b * I` divided
by `c + d * I`, with `x` and `y` the parts computed.
-/
@[expose] public def divRecover (a b c d x y : Float) : ComplexFloat :=
  let inf : Float := 1 / 0
  if x.isNaN && y.isNaN then
    if c == 0 && d == 0 && (!a.isNaN || !b.isNaN) then
      ⟨Float.copySign inf c * a, Float.copySign inf c * b⟩
    else if (a.isInf || b.isInf) && c.isFinite && d.isFinite then
      let a := Float.copySign (if a.isInf then 1 else 0) a
      let b := Float.copySign (if b.isInf then 1 else 0) b
      ⟨inf * (a * c + b * d), inf * (b * c - a * d)⟩
    else if (c.isInf || d.isInf) && a.isFinite && b.isFinite then
      let c := Float.copySign (if c.isInf then 1 else 0) c
      let d := Float.copySign (if d.isInf then 1 else 0) d
      ⟨0 * (a * c + b * d), 0 * (b * c - a * d)⟩
    else ⟨x, y⟩
  else ⟨x, y⟩

/--
The quotient `z / w` that gfortran compiles, by `__divdc3` of libgcc: Smith's algorithm, with the
scalings and the recovery of infinities of `libgcc2.c`. A real divisor `r` is the complex number
`(r, 0)`, as the Fortran rules of mixed arithmetic make it.
-/
@[expose] public def div (z w : ComplexFloat) : ComplexFloat :=
  let a := z.re
  let b := z.im
  let c := w.re
  let d := w.im
  if c.abs < d.abs then
    let (a, b, c, d) := if d.abs ≥ divBig then (a / 2, b / 2, c / 2, d / 2) else (a, b, c, d)
    let (a, b, c, d) :=
      if d.abs < divMin2 then (a * divScale, b * divScale, c * divScale, d * divScale)
      else if (a.abs < divMin && b.abs < divMax2 && d.abs < divMax2) ||
          (b.abs < divMin && a.abs < divMax2 && d.abs < divMax2) then
        (a * divScale, b * divScale, c * divScale, d * divScale)
      else (a, b, c, d)
    let ratio := c / d
    let denom := c * ratio + d
    if ratio.abs > divMin then
      divRecover a b c d ((a * ratio + b) / denom) ((b * ratio - a) / denom)
    else divRecover a b c d ((c * (a / d) + b) / denom) ((c * (b / d) - a) / denom)
  else
    let (a, b, c, d) := if c.abs ≥ divBig then (a / 2, b / 2, c / 2, d / 2) else (a, b, c, d)
    let (a, b, c, d) :=
      if c.abs < divMin2 then (a * divScale, b * divScale, c * divScale, d * divScale)
      else if (a.abs < divMin && b.abs < divMax2 && c.abs < divMax2) ||
          (b.abs < divMin && a.abs < divMax2 && c.abs < divMax2) then
        (a * divScale, b * divScale, c * divScale, d * divScale)
      else (a, b, c, d)
    let ratio := d / c
    let denom := d * ratio + c
    if ratio.abs > divMin then
      divRecover a b c d ((b * ratio + a) / denom) ((b - a * ratio) / denom)
    else divRecover a b c d ((a + d * (b / c)) / denom) ((b - d * (a / c)) / denom)

end BLAS.ComplexFloat64

namespace BLAS.ComplexFloat32

/--
The quotient `z / w` that gfortran compiles, by `__divsc3` of libgcc: the textbook quotient,
computed in `Float` and rounded to `Float32`, and then, when both of its parts are `NaN`, the
recovery of infinities and zeros of `__divdc3`, in `Float32`. A real divisor `r` is the complex
number `(r, 0)`, as the Fortran rules of mixed arithmetic make it.
-/
@[expose] public def div (z w : ComplexFloat32) : ComplexFloat32 :=
  let a := z.re
  let b := z.im
  let c := w.re
  let d := w.im
  let ad := a.toFloat
  let bd := b.toFloat
  let cd := c.toFloat
  let dd := d.toFloat
  let denom := cd * cd + dd * dd
  let x := ((ad * cd + bd * dd) / denom).toFloat32
  let y := ((bd * cd - ad * dd) / denom).toFloat32
  let inf : Float32 := 1 / 0
  if x.isNaN && y.isNaN then
    if c == 0 && d == 0 && (!a.isNaN || !b.isNaN) then
      ⟨Float32.copySign inf c * a, Float32.copySign inf c * b⟩
    else if (a.isInf || b.isInf) && c.isFinite && d.isFinite then
      let a := Float32.copySign (if a.isInf then 1 else 0) a
      let b := Float32.copySign (if b.isInf then 1 else 0) b
      ⟨inf * (a * c + b * d), inf * (b * c - a * d)⟩
    else if (c.isInf || d.isInf) && a.isFinite && b.isFinite then
      let c := Float32.copySign (if c.isInf then 1 else 0) c
      let d := Float32.copySign (if d.isInf then 1 else 0) d
      ⟨0 * (a * c + b * d), 0 * (b * c - a * d)⟩
    else ⟨x, y⟩
  else ⟨x, y⟩

end BLAS.ComplexFloat32
