/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesComplexFloat.ComplexFloat.Basic
public import BatteriesBLAS.ComplexDiv

/-!
# Complex arithmetic of the reference BLAS

The complex routines compute as the reference BLAS does when gfortran compiles it with its usual
flags, rather than with the arithmetic of `ComplexFloat`, whose products and quotients follow
Annex G of the C standard and correct their rounding errors with fused multiply-adds:

* a product of complex numbers is the textbook formula
  `(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)`, unless both parts of it are `NaN`:
  then it recovers the infinities as `__muldc3` of libgcc does, which gfortran calls in that case;
* a real number that multiplies a complex one is the complex number `(r, 0)`, as the Fortran
  rules of mixed arithmetic make it, so that the product is the complex product above; only
  `zdscal` scales both parts of its vector by a real number, and `rscal` does the same;
* sums and differences are componentwise, as they are for `ComplexFloat`.

Sums of `ComplexFloat`s use its `+` and `-`, which are already componentwise.
-/

namespace BLAS.ComplexFloat64

/-- The real number `x` as a complex number, `(x, 0)`. -/
@[inline, expose] public def ofReal (x : Float) : ComplexFloat := ⟨x, 0⟩

/-- The infinity `+∞`. -/
@[expose] public def infinity : Float := 1 / 0

/--
The product of `a` and `b` when both parts of the textbook product are `NaN`, as `__muldc3` of
libgcc computes it: when a factor is infinite, it replaces the parts of that factor by `±1` for
an infinite part and `±0` for the others, and the `NaN` parts of the other factor by `±0`, with
their signs; otherwise, when one of the four products of parts overflowed, it replaces the `NaN`
parts of both factors by `±0`. In either case the result is `∞` times the textbook product of the
new factors, and otherwise it is the textbook product.
-/
@[expose] public def mulRecover (a b : ComplexFloat) : ComplexFloat :=
  let ac := a.re * b.re
  let bd := a.im * b.im
  let ad := a.re * b.im
  let bc := a.im * b.re
  let box (u : Float) := Float.copySign (if u.isInf then 1 else 0) u
  let unNaN (u : Float) := if u.isNaN then Float.copySign 0 u else u
  let aInf := a.re.isInf || a.im.isInf
  let bInf := b.re.isInf || b.im.isInf
  let a₁ := if aInf then (⟨box a.re, box a.im⟩ : ComplexFloat) else a
  let b₁ := if aInf then (⟨unNaN b.re, unNaN b.im⟩ : ComplexFloat) else b
  let a₂ := if bInf then (⟨unNaN a₁.re, unNaN a₁.im⟩ : ComplexFloat) else a₁
  let b₂ := if bInf then (⟨box b₁.re, box b₁.im⟩ : ComplexFloat) else b₁
  if aInf || bInf then
    ⟨infinity * (a₂.re * b₂.re - a₂.im * b₂.im), infinity * (a₂.re * b₂.im + a₂.im * b₂.re)⟩
  else if ac.isInf || bd.isInf || ad.isInf || bc.isInf then
    let a₃ : ComplexFloat := ⟨unNaN a.re, unNaN a.im⟩
    let b₃ : ComplexFloat := ⟨unNaN b.re, unNaN b.im⟩
    ⟨infinity * (a₃.re * b₃.re - a₃.im * b₃.im), infinity * (a₃.re * b₃.im + a₃.im * b₃.re)⟩
  else ⟨ac - bd, ad + bc⟩

/--
The product of complex numbers that gfortran compiles: the textbook product
`(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)`, or `mulRecover a b` when both of its
parts are `NaN`.
-/
@[inline, expose] public def mul (a b : ComplexFloat) : ComplexFloat :=
  let x := a.re * b.re - a.im * b.im
  let y := a.re * b.im + a.im * b.re
  if x == x || y == y then ⟨x, y⟩ else mulRecover a b

/-- The real part of `mulRecover`, of the parts of the factors, out of line. -/
@[noinline, expose] public def mulRecoverRe (ar ai br bi : Float) : Float :=
  (mulRecover ⟨ar, ai⟩ ⟨br, bi⟩).re

/-- The imaginary part of `mulRecover`, of the parts of the factors, out of line. -/
@[noinline, expose] public def mulRecoverIm (ar ai br bi : Float) : Float :=
  (mulRecover ⟨ar, ai⟩ ⟨br, bi⟩).im

/--
The real part of `mul a b`, for loops that keep the parts in separate variables: it computes in
floats, and calls `mulRecoverRe` out of line in the rare case, so that no `ComplexFloat` is built.
-/
@[inline, expose] public def mulRe (a b : ComplexFloat) : Float :=
  let x := a.re * b.re - a.im * b.im
  let y := a.re * b.im + a.im * b.re
  if x == x || y == y then x else mulRecoverRe a.re a.im b.re b.im

/-- The imaginary part of `mul a b`, as `mulRe`. -/
@[inline, expose] public def mulIm (a b : ComplexFloat) : Float :=
  let x := a.re * b.re - a.im * b.im
  let y := a.re * b.im + a.im * b.re
  if x == x || y == y then y else mulRecoverIm a.re a.im b.re b.im

@[simp] public theorem mulRe_eq (a b : ComplexFloat) : mulRe a b = (mul a b).re := by
  simp only [mulRe, mul]; split <;> rfl

@[simp] public theorem mulIm_eq (a b : ComplexFloat) : mulIm a b = (mul a b).im := by
  simp only [mulIm, mul]; split <;> rfl

/--
The product `(α * z.re, α * z.im)` of a real and a complex number, part by part, as `zdscal`
computes it.
-/
@[inline, expose] public def rmul (α : Float) (z : ComplexFloat) : ComplexFloat :=
  ⟨α * z.re, α * z.im⟩

/--
The product `mul z (ofReal r)` of a complex and a real number, with the real number on the right,
as gfortran computes `TEMP1*DBLE(A(J,J))` in `zhemv`.
-/
@[inline, expose] public def mulr (z : ComplexFloat) (r : Float) : ComplexFloat :=
  mul z (ofReal r)

/-- `|z.re| + |z.im|`, the absolute value that the reference BLAS uses in `izamax` and `dzasum`. -/
@[inline, expose] public def abs1 (z : ComplexFloat) : Float := z.re.abs + z.im.abs

/--
`0.25`, the factor of the scaled sums of `izamax`. It is a constant, so that compiled loops do not
build it from its decimal digits at each use.
-/
@[expose] public def quarter : Float := 0.25

/-- `z` with both parts `+0`. -/
@[expose] public def zero : ComplexFloat := ⟨0, 0⟩

@[simp] public theorem re_rmul (α : Float) (z : ComplexFloat) :
    (rmul α z).re = α * z.re := rfl

@[simp] public theorem im_rmul (α : Float) (z : ComplexFloat) :
    (rmul α z).im = α * z.im := rfl

end BLAS.ComplexFloat64
