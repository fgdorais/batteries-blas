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
Tests for the Level 2 routines on `ComplexFloat32`: `gemv`, `gemvT`, `gemvC`, `geru` and `gerc`.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Level2

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The infinity. -/
def inf : Float32 := 1 / 0

/-- A `NaN`. -/
def nan : Float32 := 0 / 0

/-- Whether a float is a `NaN`. -/
def isNaN' (z : ComplexFloat32) : Bool := z.re.isNaN || z.im.isNaN

/-- `[[1 + I, 2], [3, -I]]`. -/
def A : Mat 2 2 := .ofFn fun i j => #[#[c 1 1, c 2 0], #[c 3 0, c 0 (-1)]][i]![j]!

/-- The vector with the elements of `l`. -/
def v (l : List ComplexFloat32) : Vec l.length := .ofList l

/-! ## Storage -/

-- Element `(i, j)` has its parts at `2 * (ld * j + i)` and the next index.
#guard (A.data.toList == [1, 1, 3, 0, 2, 0, 0, -1])
#guard eqList A.toList [c 1 1, c 3 0, c 2 0, c 0 (-1)]
-- A leading dimension larger than the number of rows skips the elements between the columns.
#guard ((Mat.ofLd? (m := 1) (n := 2) A.data 0 2).map Mat.toList) == some [c 1 1, c 2 0]
#guard ((Mat.ofLd? (m := 2) (n := 2) A.data 1 2).map Mat.toList) == none

/-! ## `gemv` -/

-- `A * [1, I] = [1 + 3 * I, 4]`.
#guard eqList (Mat.gemv (c 1 0) A (v [c 1 0, c 0 1]) (c 0 0) (v [c 5 5, c 7 7])).toList
  [c 1 3, c 4 0]
-- `2 * A * x + I * y`.
#guard eqList (Mat.gemv (c 2 0) A (v [c 1 0, c 0 1]) (c 0 1) (v [c 1 0, c 0 1])).toList
  [c 2 7, c 7 0]
-- `β = 0` writes zeros without reading `y`, even a `NaN`.
#guard eqList (Mat.gemv (c 0 0) A (v [c 1 0, c 0 1]) (c 0 0) (v [c nan nan, c inf 0])).toList
  [c 0 0, c 0 0]
-- `α = 0` and `β = 1` return `y`, and so does `n = 0`.
#guard (Mat.gemv (c 0 0) A (v [c nan 0, c 0 1]) (c 1 0) (v [c 1 2, c 3 4])).toList ==
  [c 1 2, c 3 4]
#guard (Mat.gemv (m := 2) (n := 0) (c 1 0) (.ofFn fun _ _ => c 0 0) (v []) (c 0 0)
  (v [c nan 2, c 3 4])).toList.map (·.im) == [2, 4]
-- No column is skipped: a zero `x[j]` times an infinite column still gives a `NaN`.
#guard isNaN' (Mat.gemv (c 1 0) (.ofFn fun _ _ => c inf 0 : Mat 1 1) (v [c 0 0]) (c 1 0)
  (v [c 1 0]))[0]
-- A strided `y`, inside a larger array, leaves the other entries alone.
#guard ((Vec.ofStride? (n := 2) (Float32Array.ofFn (n := 6) fun i => i.val.toFloat32) 0 2).map
  fun y => (Mat.gemv (c 1 0) A (v [c 1 0, c 0 1]) (c 0 0) y).data.toList) ==
  some [1, 3, 2, 3, 4, 0]

/-! ## `gemvT` and `gemvC` -/

-- `Aᵀ * [1, I] = [1 + 4 * I, 3]` and `Aᴴ * [1, I] = [1 + 2 * I, 1]`.
#guard eqList (Mat.gemvT (c 1 0) A (v [c 1 0, c 0 1]) (c 0 0) (v [c 0 0, c 0 0])).toList
  [c 1 4, c 3 0]
#guard eqList (Mat.gemvC (c 1 0) A (v [c 1 0, c 0 1]) (c 0 0) (v [c 0 0, c 0 0])).toList
  [c 1 2, c 1 0]
-- `α = 0` scales `y` by `β`.
#guard eqList (Mat.gemvC (c 0 0) A (v [c 1 0, c 0 1]) (c 0 2) (v [c 1 0, c 0 1])).toList
  [c 0 2, c (-2) 0]
-- `m = 0` returns `y`, without scaling it.
#guard eqList (Mat.gemvT (m := 0) (n := 2) (c 1 0) (.ofFn fun _ _ => c 0 0) (v []) (c 0 0)
  (v [c 1 2, c 3 4])).toList [c 1 2, c 3 4]

/-! ## `geru` and `gerc` -/

-- `A + [1, I] * [1, 2]ᵀ` and `A + [1, I] * [I, 2]ᴴ`.
#guard eqList (Mat.geru (c 1 0) (v [c 1 0, c 0 1]) (v [c 1 0, c 2 0]) A).toList
  [c 2 1, c 3 1, c 4 0, c 0 1]
#guard eqList (Mat.gerc (c 1 0) (v [c 1 0, c 0 1]) (v [c 0 1, c 2 0]) A).toList
  [c 1 0, c 4 0, c 4 0, c 0 1]
-- A zero `y[j]` skips column `j`, even with a `NaN` in `x`.
#guard (Mat.geru (c 1 0) (v [c nan 0, c 0 1]) (v [c 0 0, c 2 0]) A).toList.take 2 ==
  [c 1 1, c 3 0]
-- `α = 0` returns `A`.
#guard (Mat.gerc (c 0 0) (v [c nan 0, c 0 1]) (v [c 1 0, c 2 0]) A).toList == A.toList

end BLASTest.ComplexFloat32.Level2
