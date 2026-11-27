/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BatteriesBLAS
import BatteriesBLASTest.Util
meta import BatteriesBLAS
meta import BatteriesBLASTest.Util

/-!
Tests for the Level 1 routines on `ComplexFloat`: updates, rotations and reductions.
-/

open ScalarArray BLAS.ComplexFloat64

namespace BLASTest.ComplexFloat64

/-- The complex number `re + im * I`. -/
def c (re im : Float) : ComplexFloat := ⟨re, im⟩

/-- The vector `[0, 1 - I, 2 - 2 * I, …]` scaled by `s`. -/
def ramp (n : Nat) (s : Float := 1) : Vec n :=
  .ofFn fun i => c (s * i.val.toFloat) (-s * i.val.toFloat)

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The infinity. -/
def inf : Float := 1 / 0

/-- A `NaN`. -/
def nan : Float := 0 / 0

/--
The address of the array of `x`, with `x`. It is not inlined, so the address is taken before `x`
goes on to a routine, and doesn't keep the array alive past it.
-/
@[noinline] def withAddr (x : Vec n) : USize × Vec n := (BLASTest.addr x.data, x)

/-! ## Storage -/

-- Element `i` has its real part at the index `2 * i` and its imaginary part at `2 * i + 1`.
#guard (Vec.ofList (n := 2) [c 1 2, c 3 4]).data.toList == [1, 2, 3, 4]
#guard eqList (Vec.ofArray (n := 2) (.ofList [1, 2, 3, 4]) rfl).toList [c 1 2, c 3 4]

-- The offset and the stride count elements: the elements `1` and `3` of six.
#guard
  let a : Float64Array := .ofList [0, 0, 1, 2, 0, 0, 3, 4, 0, 0, 0, 0]
  match Vec.ofStride? (n := 2) a 1 2 with
  | some x => eqList x.toList [c 1 2, c 3 4]
  | none => false
#guard (Vec.ofStride? (n := 2) (.ofList [0, 0, 1, 2, 0, 0, 3]) 1 2).isNone

/-! ## `axpy` -/

-- `(2 + I) * (1 + 2 * I) = 5 * I` and `(2 + I) * (3 - I) = 7 + I`.
#guard eqList (Vec.axpy (c 2 1) (.ofList (n := 2) [c 1 2, c 3 (-1)])
  (.ofList (n := 2) [c 1 1, c 0 0])).toList [c 1 6, c 7 1]
#guard eqList (Vec.axpy (c 1 0) (ramp 0) (ramp 0)).toList []

-- Every element, past 16 bits of index.
#guard
  let n := 70000
  let z := Vec.axpy (c 0 1) (ramp n) (ramp n 0.5)
  (List.range n).all fun i =>
    z.toList[i]! == c (0.5 * i.toFloat + i.toFloat) (-0.5 * i.toFloat + i.toFloat)

-- The textbook product: `(1 + 0 * I) * (∞ + I)` has the imaginary part `1 * 1 + 0 * ∞`, a
-- `NaN`.
#guard
  match (Vec.axpy (c 1 0) (.ofList (n := 1) [c inf 1]) (.ofList (n := 1) [c 0 0])).toList with
  | [z] => z.re == inf && z.im.isNaN
  | _ => false

-- As in the reference BLAS, `|α.re| + |α.im| = 0` returns `y` without reading `x`.
#guard eqList (Vec.axpy (c 0 (-0)) (.ofList (n := 2) [c inf nan, c nan 1])
  (.ofList (n := 2) [c 1 2, c 3 4])).toList [c 1 2, c 3 4]

-- A strided `y` in a larger array: the entries outside `y` are unchanged.
#guard
  let a : Float64Array := .ofList [9, 9, 1, 1, 9, 9, 2, 2, 9, 9]
  match Vec.ofStride? (n := 2) a 1 2 with
  | some y =>
    let z := Vec.axpy (c 0 1) (.ofList (n := 2) [c 1 0, c 0 1]) y
    z.data.toList == [9, 9, 1, 2, 9, 9, 1, 2, 9, 9]
  | none => false

/-- Whether `axpy` updates an unshared `y` in place. -/
def axpyInPlace (n : Nat) : Bool :=
  let (p, y) := withAddr (ramp n)
  let z := Vec.axpy (c 2 1) (ramp n 3) y
  BLASTest.addr z.data == p

#guard axpyInPlace 1000

/-! ## `scal` and `rscal` -/

#guard eqList (Vec.scal (c 0 1) (.ofList (n := 2) [c 1 2, c 3 (-4)])).toList [c (-2) 1, c 4 3]
#guard eqList (Vec.rscal 2 (.ofList (n := 2) [c 1 2, c 3 (-4)])).toList [c 2 4, c 6 (-8)]

-- As in the reference BLAS, `α = 1` returns `x`, so an infinity doesn't turn into a `NaN`.
#guard
  match (Vec.scal (c 1 0) (.ofList (n := 1) [c inf 1])).toList with
  | [z] => z.re == inf && z.im == 1
  | _ => false
#guard
  match (Vec.scal (c 1 (-0)) (.ofList (n := 1) [c inf 1])).toList with
  | [z] => z.re == inf && z.im == 1
  | _ => false
#guard
  match (Vec.scal (c 2 0) (.ofList (n := 1) [c inf 1])).toList with
  | [z] => z.re == inf && z.im.isNaN
  | _ => false
#guard
  match (Vec.rscal 1 (.ofList (n := 1) [c nan inf])).toList with
  | [z] => z.re.isNaN && z.im == inf
  | _ => false

/-- Whether `scal` updates an unshared `x` in place. -/
def scalInPlace (n : Nat) : Bool :=
  let (p, x) := withAddr (ramp n)
  let z := Vec.scal (c 2 1) x
  BLASTest.addr z.data == p

#guard scalInPlace 1000

/-! ## `copy` and `swap` -/

#guard eqList (Vec.copy (.ofList (n := 2) [c 1 2, c 3 4]) (ramp 2)).toList [c 1 2, c 3 4]

#guard
  let a : Float64Array := .ofList [9, 9, 0, 0, 9, 9, 0, 0]
  match Vec.ofStride? (n := 2) a 1 2 with
  | some y => (Vec.copy (.ofList (n := 2) [c 1 2, c 3 4]) y).data.toList == [9, 9, 1, 2, 9, 9, 3, 4]
  | none => false

#guard
  let (x, y) := Vec.swap (.ofList (n := 1) [c 1 2]) (.ofList (n := 1) [c 3 4])
  eqList x.toList [c 3 4] && eqList y.toList [c 1 2]

/-! ## `dotu` and `dotc` -/

-- `(1 + 2 * I) * (3 + 4 * I) + (5 - I) * (2 * I) = -5 + 10 * I + 2 + 10 * I`.
#guard Vec.dotu (.ofList (n := 2) [c 1 2, c 5 (-1)]) (.ofList (n := 2) [c 3 4, c 0 2]) ==
  c (-3) 20
-- `(1 - 2 * I) * (3 + 4 * I) + (5 + I) * (2 * I) = 11 - 2 * I - 2 + 10 * I`.
#guard Vec.dotc (.ofList (n := 2) [c 1 2, c 5 (-1)]) (.ofList (n := 2) [c 3 4, c 0 2]) ==
  c 9 8
#guard Vec.dotc (ramp 0) (ramp 0) == c 0 0
-- `dotc x x` is the sum of the squared moduli.
#guard Vec.dotc (ramp 4) (ramp 4) == c 28 0

-- Summed from the left, from `0`: `1e16 + 1 - 1e16` is `0` in that order, not `1`.
#guard Vec.dotu (.ofList (n := 3) [c 1e16 0, c 1 0, c (-1e16) 0]) (.ofList (n := 3) [c 1 0, c 1 0,
  c 1 0]) == c 0 0

/-! ## `asum` -/

-- The sum of `|re| + |im|`, not of the moduli.
#guard Vec.asum (.ofList (n := 2) [c 3 (-4), c (-1) 0]) == 8
#guard Vec.asum (ramp 0) == 0
#guard (Vec.asum (.ofList (n := 2) [c 1 nan, c 2 3])).isNaN

/-! ## `nrm2` -/

#guard Vec.nrm2 (.ofList (n := 1) [c 3 4]) == 5
#guard Vec.nrm2 (.ofList (n := 2) [c 3 0, c 0 4]) == 5
#guard Vec.nrm2 (ramp 0) == 0
#guard (Vec.nrm2 (.ofList (n := 2) [c inf 1, c nan 0])).isNaN
#guard Vec.nrm2 (.ofList (n := 2) [c inf 1, c 0 0]) == inf

-- Squares that overflow or underflow.
#guard Vec.nrm2 (.ofList (n := 1) [c (Float.scaleB 3 600) (Float.scaleB 4 600)]) ==
  Float.scaleB 5 600
#guard Vec.nrm2 (.ofList (n := 1) [c (Float.scaleB 3 (-600)) (Float.scaleB 4 (-600))]) ==
  Float.scaleB 5 (-600)

/-! ## `iamax` -/

#guard Vec.iamax! (.ofList (n := 3) [c 1 1, c (-3) 0, c 0 2]) = 1
#guard Vec.iamax! (ramp 0) = 0
#guard Vec.iamax! (.ofList (n := 1) [c nan nan]) = 0
-- The first of the largest.
#guard Vec.iamax! (.ofList (n := 3) [c 1 0, c 2 0, c 0 (-2)]) = 1
-- The first `NaN` part wins, even after an infinite one.
#guard Vec.iamax! (.ofList (n := 4) [c 1 1, c inf 0, c 2 nan, c nan 0]) = 2
-- The first infinite part wins over larger finite elements and later infinities.
#guard Vec.iamax! (.ofList (n := 4) [c 1 1, c 0 (-inf), c 5 5, c inf inf]) = 1
-- `|re| + |im|` overflows: from there on, `0.25 * |re| + 0.25 * |im|` is compared.
#guard Vec.iamax! (.ofList (n := 3) [c 1 1, c 1e308 1e308, c 1.5e308 1.5e308]) = 2
#guard Vec.iamax! (.ofList (n := 3) [c 1 1, c 1.5e308 1.5e308, c 1e308 1e308]) = 1

#guard (Vec.iamax (.ofList (n := 2) [c 1 0, c 0 3])).val = 1
#guard Vec.iamax? (ramp 0) = none
#guard (Vec.iamax? (.ofList (n := 2) [c 1 0, c 0 3])).map (·.val) = some 1

/-! ## `rot` and `rotg` -/

#guard
  let (x, y) := Vec.rot 0.5 2 (.ofList (n := 2) [c 1 2, c 3 4]) (.ofList (n := 2) [c 4 2, c 0 1])
  eqList x.toList [c 8.5 5, c 1.5 4] && eqList y.toList [c 0 (-3), c (-6) (-7.5)]

#guard
  let a : Float64Array := .ofList [9, 9, 1, 2, 9, 9, 3, 4]
  match Vec.ofStride? (n := 2) a 1 2 with
  | some x =>
    let (x', _) := Vec.rot 0 1 x (.ofList (n := 2) [c 5 6, c 7 8])
    x'.data.toList == [9, 9, 5, 6, 9, 9, 7, 8]
  | none => false

#guard
  let g := rotg (c 3 0) (c 4 0)
  g.c == 0.6 && g.r == c 5 0 && g.s == c 0.8 0
#guard
  let g := rotg (c 1 2) (c 0 0)
  g.c == 1 && g.r == c 1 2 && g.s == c 0 0
#guard
  let g := rotg (c 0 0) (c 0 2)
  g.c == 0 && g.r == c 2 0 && g.s == c 0 (-1)
#guard
  let g := rotg (c 0 0) (c 3 4)
  g.c == 0 && g.r == c 5 0 && g.s == c 0.6 (-0.8)

-- The rotation zeros `b`: `-conj s * a + c * b = 0`, up to rounding.
#guard
  let a := c 1 2
  let b := c 3 (-1)
  let g := rotg a b
  let z := c (-(g.s.re * a.re + g.s.im * a.im) + g.c * b.re)
    (-(g.s.re * a.im - g.s.im * a.re) + g.c * b.im)
  z.re.abs < 1e-15 && z.im.abs < 1e-15 && g.c > 0

end BLASTest.ComplexFloat64
