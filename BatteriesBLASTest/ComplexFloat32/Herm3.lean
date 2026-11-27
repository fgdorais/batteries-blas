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
Tests for the Hermitian Level 3 routines on `ComplexFloat32`: `hemm`, `hemmRight`, `herk`, `herkC`,
`her2k` and `her2kC`.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Herm3

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The `2 × 2` matrix with rows `r₀` and `r₁`. -/
def M (r₀ r₁ : List ComplexFloat32) : Mat 2 2 := .ofFn fun i j => #[r₀.toArray, r₁.toArray][i]![j]!

/--
The Hermitian `[[2, 1 + I], [1 - I, 3]]` in its upper triangle, with `99 + 99 * I` below it and an
imaginary part on the diagonal, which aren't read.
-/
def HU : Mat 2 2 := M [c 2 5, c 1 1] [c 99 99, c 3 7]

/-- The same matrix in its lower triangle. -/
def HL : Mat 2 2 := M [c 2 5, c 99 99] [c 1 (-1), c 3 7]

/-- `[[1, I], [2, 0]]`. -/
def B : Mat 2 2 := M [c 1 0, c 0 1] [c 2 0, c 0 0]

/-- `[[1, I], [2, 1 - I]]`. -/
def A : Mat 2 2 := M [c 1 0, c 0 1] [c 2 0, c 1 (-1)]

/-- The matrix of `9 + 9 * I`. -/
def C9 : Mat 2 2 := .ofFn fun _ _ => c 9 9

/-- The matrix of zeros. -/
def Z : Mat 2 2 := .ofFn fun _ _ => c 0 0

/-! ## `hemm` and `hemmRight` -/

#guard eqList (Mat.hemm .upper (c 1 0) HU B (c 0 0) C9).toList [c 4 2, c 7 (-1), c 0 2, c 1 1]
#guard eqList (Mat.hemm .lower (c 1 0) HL B (c 0 0) C9).toList [c 4 2, c 7 (-1), c 0 2, c 1 1]
#guard eqList (Mat.hemmRight .upper (c 1 0) HU B (c 0 0) C9).toList [c 3 1, c 4 0, c 1 4, c 2 2]
#guard eqList (Mat.hemmRight .lower (c 1 0) HL B (c 0 0) C9).toList [c 3 1, c 4 0, c 1 4, c 2 2]
-- `β = 1` adds to `C`, and `α = 0` only scales it.
#guard eqList (Mat.hemm .upper (c 1 0) HU B (c 1 0) Z).toList [c 4 2, c 7 (-1), c 0 2, c 1 1]
#guard eqList (Mat.hemm .upper (c 0 0) HU B (c 2 0) C9).toList [c 18 18, c 18 18, c 18 18, c 18 18]

/-! ## `herk`, `herkC`, `her2k` and `her2kC`: the other triangle is unchanged -/

#guard eqList (Mat.herk .upper 1 A 0 C9).toList [c 2 0, c 9 9, c 1 1, c 6 0]
#guard eqList (Mat.herkC .lower 1 A 0 C9).toList [c 5 0, c 2 1, c 9 9, c 3 0]
#guard eqList (Mat.her2k .upper (c 0 1) A B 0 C9).toList [c 0 0, c 9 9, c 1 1, c 0 0]
#guard eqList (Mat.her2kC .lower (c 0 1) A B 0 C9).toList [c 0 0, c (-2) 2, c 9 9, c 0 0]
-- With `β = 1`, the imaginary parts of the diagonal are set to `0`, unless `α = 0` or `k = 0`.
#guard eqList (Mat.herk .upper 1 A 1 C9).toList [c 11 0, c 9 9, c 10 10, c 15 0]
#guard eqList (Mat.herk .upper 0 A 1 C9).toList C9.toList
#guard eqList (Mat.her2k .lower (c 0 1) (.ofFn fun _ _ => c 1 0 : Mat 2 0)
  (.ofFn fun _ _ => c 1 0 : Mat 2 0) 1 C9).toList C9.toList
-- `herk` skips the terms with `A[j, l] = 0`: with `A[1, 0] = 0`, the infinity in `A[0, 0]` doesn't
-- make element `(0, 1)` a `NaN`.
#guard eqList [(Mat.herk .upper 1 (M [c (1 / 0) 0, c 1 0] [c 0 0, c 1 0]) 0 C9).toList[2]!]
  [c 1 0]

end BLASTest.ComplexFloat32.Herm3
