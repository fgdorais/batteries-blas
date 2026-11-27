/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesComplexFloat.ComplexFloat.Basic

/-!
# Complex arithmetic of the reference BLAS

The complex routines compute as the reference BLAS does when gfortran compiles it with its usual
flags, rather than with the arithmetic of `ComplexFloat`, whose products and quotients follow
Annex G of the C standard and correct their rounding errors with fused multiply-adds:

* a product of complex numbers is the textbook formula
  `(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)`, with no recovery of infinities;
* a product of a real and a complex number multiplies both parts by the real number, as gfortran
  does when it knows the imaginary part of the real operand to be zero;
* sums and differences are componentwise, as they are for `ComplexFloat`.

Sums of `ComplexFloat`s use its `+` and `-`, which are already componentwise.
-/

namespace BLAS.ComplexFloat64

/-- The textbook product `(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)`. -/
@[inline, expose] public def mul (a b : ComplexFloat) : ComplexFloat :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- The product `(α * z.re, α * z.im)` of a real and a complex number. -/
@[inline, expose] public def rmul (α : Float) (z : ComplexFloat) : ComplexFloat :=
  ⟨α * z.re, α * z.im⟩

/-- `|z.re| + |z.im|`, the absolute value that the reference BLAS uses in `izamax` and `dzasum`. -/
@[inline, expose] public def abs1 (z : ComplexFloat) : Float := z.re.abs + z.im.abs

/--
`0.25`, the factor of the scaled sums of `izamax`. It is a constant, so that compiled loops do not
build it from its decimal digits at each use.
-/
@[expose] public def quarter : Float := 0.25

/-- `z` with both parts `+0`. -/
@[expose] public def zero : ComplexFloat := ⟨0, 0⟩

@[simp] public theorem re_mul (a b : ComplexFloat) :
    (mul a b).re = a.re * b.re - a.im * b.im := rfl

@[simp] public theorem im_mul (a b : ComplexFloat) :
    (mul a b).im = a.re * b.im + a.im * b.re := rfl

@[simp] public theorem re_rmul (α : Float) (z : ComplexFloat) :
    (rmul α z).re = α * z.re := rfl

@[simp] public theorem im_rmul (α : Float) (z : ComplexFloat) :
    (rmul α z).im = α * z.im := rfl

end BLAS.ComplexFloat64
