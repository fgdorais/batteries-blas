/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesComplexFloat.ComplexFloat32.Basic

/-!
# Complex arithmetic of the reference BLAS

The complex routines compute as the reference BLAS does when gfortran compiles it with its usual
flags, rather than with the arithmetic of `ComplexFloat32`, whose products and quotients follow
Annex G of the C standard and correct their rounding errors with fused multiply-adds:

* a product of complex numbers is the textbook formula
  `(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)`, with no recovery of infinities;
* a product of a real and a complex number multiplies both parts by the real number, as gfortran
  does when it knows the imaginary part of the real operand to be zero;
* sums and differences are componentwise, as they are for `ComplexFloat32`.

Sums of `ComplexFloat32`s use its `+` and `-`, which are already componentwise.
-/

namespace BLAS.ComplexFloat32

/-- The textbook product `(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)`. -/
@[inline, expose] public def mul (a b : ComplexFloat32) : ComplexFloat32 :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- The product `(α * z.re, α * z.im)` of a real and a complex number. -/
@[inline, expose] public def rmul (α : Float32) (z : ComplexFloat32) : ComplexFloat32 :=
  ⟨α * z.re, α * z.im⟩

/--
The product `(z.re * r, z.im * r)` of a complex and a real number, with the real number on the
right, as gfortran computes `TEMP1*DBLE(A(J,J))` in `chemv`.
-/
@[inline, expose] public def mulr (z : ComplexFloat32) (r : Float32) : ComplexFloat32 :=
  ⟨z.re * r, z.im * r⟩

/-- `|z.re| + |z.im|`, the absolute value that the reference BLAS uses in `icamax` and `scasum`. -/
@[inline, expose] public def abs1 (z : ComplexFloat32) : Float32 := z.re.abs + z.im.abs

/--
`0.25`, the factor of the scaled sums of `icamax`. It is a constant, so that compiled loops do not
build it from its decimal digits at each use.
-/
@[expose] public def quarter : Float32 := 0.25

/-- `z` with both parts `+0`. -/
@[expose] public def zero : ComplexFloat32 := ⟨0, 0⟩

@[simp] public theorem re_mul (a b : ComplexFloat32) :
    (mul a b).re = a.re * b.re - a.im * b.im := rfl

@[simp] public theorem im_mul (a b : ComplexFloat32) :
    (mul a b).im = a.re * b.im + a.im * b.re := rfl

@[simp] public theorem re_rmul (α : Float32) (z : ComplexFloat32) :
    (rmul α z).re = α * z.re := rfl

@[simp] public theorem im_rmul (α : Float32) (z : ComplexFloat32) :
    (rmul α z).im = α * z.im := rfl

end BLAS.ComplexFloat32
