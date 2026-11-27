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
Tests for the complex triangular products of Level 3 on `ComplexFloat32`: `trmm`, `trmmT`, `trmmC`,
`trmmRight`, `trmmRightT` and `trmmRightC`.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Trmm3

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The `2 × 2` matrix with rows `r₀` and `r₁`. -/
def M (r₀ r₁ : List ComplexFloat32) : Mat 2 2 := .ofFn fun i j => #[r₀.toArray, r₁.toArray][i]![j]!

/-- The upper triangle `[[2 + I, 1 + I], [0, 3]]`, with `99 + 99 * I` below it, which isn't read. -/
def TU : Mat 2 2 := M [c 2 1, c 1 1] [c 99 99, c 3 0]

/-- The lower triangle `[[2 + I, 0], [1 + I, 3]]`, the transpose of `TU`. -/
def TL : Mat 2 2 := M [c 2 1, c 99 99] [c 1 1, c 3 0]

/-- `[[1, I], [2, 0]]`. -/
def B : Mat 2 2 := M [c 1 0, c 0 1] [c 2 0, c 0 0]

/-! ## The six forms (the lists are by columns) -/

#guard eqList (Mat.trmm .upper .nonUnit (c 1 0) TU B).toList [c 4 3, c 6 0, c (-1) 2, c 0 0]
#guard eqList (Mat.trmm .lower .nonUnit (c 1 0) TL B).toList [c 2 1, c 7 1, c (-1) 2, c (-1) 1]
#guard eqList (Mat.trmmT .upper .nonUnit (c 1 0) TU B).toList [c 2 1, c 7 1, c (-1) 2, c (-1) 1]
#guard eqList (Mat.trmmT .lower .nonUnit (c 1 0) TL B).toList [c 4 3, c 6 0, c (-1) 2, c 0 0]
#guard eqList (Mat.trmmC .upper .nonUnit (c 1 0) TU B).toList [c 2 (-1), c 7 (-1), c 1 2, c 1 1]
#guard eqList (Mat.trmmRight .upper .nonUnit (c 1 0) TU B).toList [c 2 1, c 4 2, c 1 4, c 2 2]
#guard eqList (Mat.trmmRight .lower .nonUnit (c 1 0) TL B).toList [c 1 2, c 4 2, c 0 3, c 0 0]
#guard eqList (Mat.trmmRightT .upper .nonUnit (c 1 0) TU B).toList [c 1 2, c 4 2, c 0 3, c 0 0]
#guard eqList (Mat.trmmRightT .lower .nonUnit (c 1 0) TL B).toList [c 2 1, c 4 2, c 1 4, c 2 2]
#guard eqList (Mat.trmmRightC .upper .nonUnit (c 1 0) TU B).toList
  [c 3 0, c 4 (-2), c 0 3, c 0 0]

/-! ## A unit diagonal, `α`, and `α = 0` -/

#guard eqList (Mat.trmm .upper .unit (c 1 0) TU B).toList [c 3 2, c 2 0, c 0 1, c 0 0]
#guard eqList (Mat.trmm .upper .nonUnit (c 0 1) TU B).toList [c (-3) 4, c 0 6, c (-2) (-1), c 0 0]
-- `α = 0` sets `B` to `0` without reading it.
#guard eqList
  (Mat.trmmRight .upper .nonUnit (c 0 0) TU (M [c (0 / 0) 0, c 1 0] [c 1 0, c 1 0])).toList
  [c 0 0, c 0 0, c 0 0, c 0 0]

end BLASTest.ComplexFloat32.Trmm3
