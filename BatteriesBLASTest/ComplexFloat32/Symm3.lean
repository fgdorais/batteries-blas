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
Tests for the complex symmetric Level 3 routines on `ComplexFloat32`: `symm`, `symmRight`, `syrk`,
`syrkT`, `syr2k` and `syr2kT`.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Symm3

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The `2 × 2` matrix with rows `r₀` and `r₁`. -/
def M (r₀ r₁ : List ComplexFloat32) : Mat 2 2 := .ofFn fun i j => #[r₀.toArray, r₁.toArray][i]![j]!

/-- The symmetric `[[2 + I, 1 + I], [1 + I, 3]]` in its upper triangle, with `99 + 99 * I` below
it, which isn't read. -/
def SU : Mat 2 2 := M [c 2 1, c 1 1] [c 99 99, c 3 0]

/-- The same matrix in its lower triangle. -/
def SL : Mat 2 2 := M [c 2 1, c 99 99] [c 1 1, c 3 0]

/-- `[[1, I], [2, 0]]`. -/
def B : Mat 2 2 := M [c 1 0, c 0 1] [c 2 0, c 0 0]

/-- `[[1, I], [2, 1 - I]]`. -/
def A : Mat 2 2 := M [c 1 0, c 0 1] [c 2 0, c 1 (-1)]

/-- The matrix of `9 + 9 * I`. -/
def C9 : Mat 2 2 := .ofFn fun _ _ => c 9 9

/-- The matrix of zeros. -/
def Z : Mat 2 2 := .ofFn fun _ _ => c 0 0

/-! ## `symm` and `symmRight` (the lists are by columns) -/

#guard eqList (Mat.symm .upper (c 1 0) SU B (c 0 0) C9).toList [c 4 3, c 7 1, c (-1) 2, c (-1) 1]
#guard eqList (Mat.symm .lower (c 1 0) SL B (c 0 0) C9).toList [c 4 3, c 7 1, c (-1) 2, c (-1) 1]
#guard eqList (Mat.symmRight .upper (c 1 0) SU B (c 0 0) C9).toList [c 1 2, c 4 2, c 1 4, c 2 2]
#guard eqList (Mat.symmRight .lower (c 1 0) SL B (c 0 0) C9).toList [c 1 2, c 4 2, c 1 4, c 2 2]
-- `β = 1` adds to `C`, and `α = 0` only scales it.
#guard eqList (Mat.symm .upper (c 1 0) SU B (c 1 0) Z).toList [c 4 3, c 7 1, c (-1) 2, c (-1) 1]
#guard eqList (Mat.symm .upper (c 0 0) SU B (c 2 0) C9).toList [c 18 18, c 18 18, c 18 18, c 18 18]

/-! ## `syrk`, `syrkT`, `syr2k` and `syr2kT`: the other triangle is unchanged -/

#guard eqList (Mat.syrk .upper (c 1 0) A (c 0 0) C9).toList [c 0 0, c 9 9, c 3 1, c 4 (-2)]
#guard eqList (Mat.syrkT .lower (c 1 0) A (c 0 0) C9).toList [c 5 0, c 2 (-1), c 9 9, c (-1) (-2)]
#guard eqList (Mat.syr2k .upper (c 0 1) A B (c 0 0) C9).toList [c 0 0, c 9 9, c (-1) 5, c 0 8]
#guard eqList (Mat.syr2kT .lower (c 0 1) A B (c 0 0) C9).toList [c 0 10, c 0 2, c 9 9, c 0 (-2)]
-- Unlike `herk`, the diagonal keeps its imaginary part.
#guard eqList (Mat.syrk .upper (c 1 0) A (c 1 0) C9).toList [c 9 9, c 9 9, c 12 10, c 13 7]
#guard eqList (Mat.syrk .upper (c 0 0) A (c 1 0) C9).toList C9.toList
#guard eqList (Mat.syr2k .lower (c 0 1) (.ofFn fun _ _ => c 1 0 : Mat 2 0)
  (.ofFn fun _ _ => c 1 0 : Mat 2 0) (c 1 0) C9).toList C9.toList
-- `syrk` skips the terms with `A[j, l] = 0`: with `A[1, 0] = 0`, the infinity in `A[0, 0]` doesn't
-- make element `(0, 1)` a `NaN`.
#guard eqList [(Mat.syrk .upper (c 1 0) (M [c (1 / 0) 0, c 1 0] [c 0 0, c 1 0]) (c 0 0)
  C9).toList[2]!] [c 1 0]

end BLASTest.ComplexFloat32.Symm3
