/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BLAS
meta import BLAS

/-!
Tests for the mixed precision routines, `dsdot` and `sdsdot`. They are written by hand, since the
routines have no `Float64` version to generate them from.
-/

open BLAS.Float32

#guard Vec.dsdot (.ofList (n := 3) [1, 2, 3]) (.ofList (n := 3) [4, 5, 6]) == 32
#guard Vec.sdsdot 0.5 (.ofList (n := 3) [1, 2, 3]) (.ofList (n := 3) [4, 5, 6]) == 32.5
#guard Vec.dsdot (n := 0) (.ofList []) (.ofList []) == 0
#guard Vec.sdsdot (n := 0) 2 (.ofList []) (.ofList []) == 2

-- `2 ^ 24 + 1 + 1` is `2 ^ 24` in `Float32`, summed from the left, and `2 ^ 24 + 2` in `Float`,
-- which `sdsdot` rounds to `Float32` once, exactly.
#guard
  let x : Vec 3 := .ofList [16777216, 1, 1]
  let y : Vec 3 := .ofList [1, 1, 1]
  Vec.dot x y == 16777216 && Vec.dsdot x y == 16777218 && Vec.sdsdot 0 x y == 16777218

-- The products are exact in `Float`: `(1 + 2 ^ (-12)) ^ 2 = 1 + 2 ^ (-11) + 2 ^ (-24)`, which
-- `Float32` rounds to `1 + 2 ^ (-11)`.
#guard
  let e : Float32 := 1 + Float32.scaleB 1 (-12)
  let x : Vec 1 := .ofList [e]
  Vec.dot x x == 1 + Float32.scaleB 1 (-11) &&
    Vec.dsdot x x == 1 + Float.scaleB 1 (-11) + Float.scaleB 1 (-24)

/-- The vector `[0, 1, …, n - 1]` in an array of `-1`, from `off` with the stride `inc`. -/
def strided (n off inc : Nat) (s : Nat := 0) : Vec n :=
  let a : ScalarArray.Float32Array := .ofFn (n := off + inc * n) fun p =>
    if off ≤ p.val ∧ (p.val - off) % inc = 0 ∧ (p.val - off) / inc < n then
      ((p.val - off) / inc + s).toFloat32
    else -1
  (Vec.ofStride? a off inc).getD (.ofFn fun i => (i.val + s).toFloat32)

-- Strided vectors give the dot product of their elements, in `Float`.
#guard
  let x := strided 100 3 2
  let y := strided 100 1 3 5
  Vec.dsdot x y ==
      (List.range 100).foldl (fun s (i : Nat) => s + i.toFloat * (i + 5).toFloat) 0 &&
    Vec.sdsdot 1 x y ==
      ((List.range 100).foldl (fun s (i : Nat) => s + i.toFloat * (i + 5).toFloat) 1).toFloat32
