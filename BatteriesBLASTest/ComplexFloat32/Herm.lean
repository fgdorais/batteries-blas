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
Tests for the Hermitian Level 2 routines on `ComplexFloat32`: `hemv`, `her` and `her2`.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Herm

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- A `NaN`. -/
def nan : Float32 := 0 / 0

/-- The vector with the elements of `l`. -/
def v (l : List ComplexFloat32) : Vec l.length := .ofList l

/--
`[[2, 1 + I], [1 - I, 3]]`, with only its upper triangle stored: the diagonal has nonzero
imaginary parts and the lower triangle holds `99 + 99 * I`, which the upper routines don't read.
-/
def U : Mat 2 2 := .ofFn fun i j => #[#[c 2 9, c 1 1], #[c 99 99, c 3 9]][i]![j]!

/-- The same matrix, with only its lower triangle stored. -/
def L : Mat 2 2 := .ofFn fun i j => #[#[c 2 9, c 99 99], #[c 1 (-1), c 3 9]][i]![j]!

/-! ## `hemv` -/

-- `A * [1, I] = [1 + I, 1 + 2 * I]`, from either triangle.
#guard eqList (Mat.hemv true (c 1 0) U (v [c 1 0, c 0 1]) (c 0 0) (v [c 5 5, c 7 7])).toList
  [c 1 1, c 1 2]
#guard eqList (Mat.hemv false (c 1 0) L (v [c 1 0, c 0 1]) (c 0 0) (v [c 5 5, c 7 7])).toList
  [c 1 1, c 1 2]
-- `I * A * x + 2 * y`.
#guard eqList (Mat.hemv true (c 0 1) U (v [c 1 0, c 0 1]) (c 2 0) (v [c 1 0, c 0 1])).toList
  [c 1 1, c (-2) 3]
-- `α = 0` scales `y` by `β`; `α = 0` and `β = 1` return `y`.
#guard eqList (Mat.hemv true (c 0 0) U (v [c nan 0, c 0 1]) (c 0 1) (v [c 1 0, c 0 1])).toList
  [c 0 1, c (-1) 0]
#guard (Mat.hemv false (c 0 0) L (v [c nan 0, c 0 1]) (c 1 0) (v [c 1 2, c 3 4])).toList ==
  [c 1 2, c 3 4]

/-! ## `her` -/

-- `A + [1, I] * [1, I]ᴴ`: the diagonal becomes real, the other triangle is unchanged.
#guard eqList ((Mat.her true 1 (v [c 1 0, c 0 1]) U).toList.take 3) [c 3 0, c 99 99, c 1 0]
#guard (Mat.her true 1 (v [c 1 0, c 0 1]) U)[(1, 1)] == c 4 0
#guard eqList (Mat.her false 1 (v [c 1 0, c 0 1]) L).toList
  [c 3 0, c 1 0, c 99 99, c 4 0]
-- A zero `x[j]` still sets the imaginary part of the diagonal to `0`, but `α = 0` doesn't.
#guard eqList (Mat.her true 1 (v [c 0 0, c 0 0]) U).toList [c 2 0, c 99 99, c 1 1, c 3 0]
#guard (Mat.her true 0 (v [c 1 0, c 0 1]) U)[(0, 0)] == c 2 9

/-! ## `her2` -/

-- `A + x * yᴴ + y * xᴴ` with `x = [1, 0]` and `y = [0, I]` adds `-I` above the diagonal.
#guard eqList (Mat.her2 true (c 1 0) (v [c 1 0, c 0 0]) (v [c 0 0, c 0 1]) U).toList
  [c 2 0, c 99 99, c 1 0, c 3 0]
#guard eqList (Mat.her2 false (c 1 0) (v [c 1 0, c 0 0]) (v [c 0 0, c 0 1]) L).toList
  [c 2 0, c 1 0, c 99 99, c 3 0]
-- `α = I` and `x = y = [1, 1]`: `α + conj α = 0`, so only the diagonal changes.
#guard eqList (Mat.her2 true (c 0 1) (v [c 1 0, c 1 0]) (v [c 1 0, c 1 0]) U).toList
  [c 2 0, c 99 99, c 1 1, c 3 0]
-- `α = 0` returns `A`.
#guard (Mat.her2 true (c 0 0) (v [c 1 0, c 0 1]) (v [c 1 0, c 0 1]) U)[(0, 0)] == c 2 9

end BLASTest.ComplexFloat32.Herm
