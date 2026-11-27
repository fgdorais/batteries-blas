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
Tests for the complex triangular solves of Level 3 on `ComplexFloat32`: `trsm`, `trsmT`, `trsmC`,
`trsmRight`, `trsmRightT` and `trsmRightC`. Each one undoes the matching product of `trmm` on
these small integer matrices, where every operation is exact.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Trsm3

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

/-! ## Each solve undoes the matching product -/

#guard eqList (Mat.trsm .upper .nonUnit (c 1 0) TU
  (Mat.trmm .upper .nonUnit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsm .upper .unit (c 1 0) TU
  (Mat.trmm .upper .unit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsm .lower .nonUnit (c 1 0) TL
  (Mat.trmm .lower .nonUnit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsm .lower .unit (c 1 0) TL
  (Mat.trmm .lower .unit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmT .upper .nonUnit (c 1 0) TU
  (Mat.trmmT .upper .nonUnit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmT .upper .unit (c 1 0) TU
  (Mat.trmmT .upper .unit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmT .lower .nonUnit (c 1 0) TL
  (Mat.trmmT .lower .nonUnit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmT .lower .unit (c 1 0) TL
  (Mat.trmmT .lower .unit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmC .upper .nonUnit (c 1 0) TU
  (Mat.trmmC .upper .nonUnit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmC .upper .unit (c 1 0) TU
  (Mat.trmmC .upper .unit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmC .lower .nonUnit (c 1 0) TL
  (Mat.trmmC .lower .nonUnit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmC .lower .unit (c 1 0) TL
  (Mat.trmmC .lower .unit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmRight .upper .nonUnit (c 1 0) TU
  (Mat.trmmRight .upper .nonUnit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmRight .upper .unit (c 1 0) TU
  (Mat.trmmRight .upper .unit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmRight .lower .nonUnit (c 1 0) TL
  (Mat.trmmRight .lower .nonUnit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmRight .lower .unit (c 1 0) TL
  (Mat.trmmRight .lower .unit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmRightT .upper .nonUnit (c 1 0) TU
  (Mat.trmmRightT .upper .nonUnit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmRightT .upper .unit (c 1 0) TU
  (Mat.trmmRightT .upper .unit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmRightT .lower .nonUnit (c 1 0) TL
  (Mat.trmmRightT .lower .nonUnit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmRightT .lower .unit (c 1 0) TL
  (Mat.trmmRightT .lower .unit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmRightC .upper .nonUnit (c 1 0) TU
  (Mat.trmmRightC .upper .nonUnit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmRightC .upper .unit (c 1 0) TU
  (Mat.trmmRightC .upper .unit (c 1 0) TU B)).toList B.toList
#guard eqList (Mat.trsmRightC .lower .nonUnit (c 1 0) TL
  (Mat.trmmRightC .lower .nonUnit (c 1 0) TL B)).toList B.toList
#guard eqList (Mat.trsmRightC .lower .unit (c 1 0) TL
  (Mat.trmmRightC .lower .unit (c 1 0) TL B)).toList B.toList

/-! ## `α`, and `α = 0` -/

-- `trsm` with `α = I` solves for `I * B`.
#guard eqList (Mat.trsm .upper .nonUnit (c 0 1) TU (Mat.trmm .upper .nonUnit (c 1 0) TU B)).toList
  [c 0 1, c 0 2, c (-1) 0, c 0 0]
#guard eqList (Mat.trsmRightC .lower .nonUnit (c 0 1) TL
  (Mat.trmmRightC .lower .nonUnit (c 1 0) TL B)).toList [c 0 1, c 0 2, c (-1) 0, c 0 0]
-- `α = 0` sets `B` to `0` without reading it.
#guard eqList
  (Mat.trsmRightT .upper .nonUnit (c 0 0) TU (M [c (0 / 0) 0, c 1 0] [c 1 0, c 1 0])).toList
  [c 0 0, c 0 0, c 0 0, c 0 0]

end BLASTest.ComplexFloat32.Trsm3
