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
Tests for the triangular Level 2 routines on `ComplexFloat32`: `trmv`, `trmvT`, `trmvC`, `trsv`,
`trsvT` and `trsvC`.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Tri

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The vector with the elements of `l`. -/
def v (l : List ComplexFloat32) : Vec l.length := .ofList l

/-- `[[1 + I, 2], [0, I]]`, with `99 + 99 * I` below the diagonal, which isn't read. -/
def U : Mat 2 2 := .ofFn fun i j => #[#[c 1 1, c 2 0], #[c 99 99, c 0 1]][i]![j]!

/-- `[[1 + I, 0], [2, I]]`, with `99 + 99 * I` above the diagonal, which isn't read. -/
def L : Mat 2 2 := .ofFn fun i j => #[#[c 1 1, c 99 99], #[c 2 0, c 0 1]][i]![j]!

/-- `[1, I]`. -/
def x : Vec 2 := v [c 1 0, c 0 1]

/-! ## `trmv`, `trmvT` and `trmvC` -/

#guard eqList (Mat.trmv .upper .nonUnit U x).toList [c 1 3, c (-1) 0]
#guard eqList (Mat.trmv .upper .unit U x).toList [c 1 2, c 0 1]
#guard eqList (Mat.trmv .lower .nonUnit L x).toList [c 1 1, c 1 0]
#guard eqList (Mat.trmv .lower .unit L x).toList [c 1 0, c 2 1]
#guard eqList (Mat.trmvT .upper .nonUnit U x).toList [c 1 1, c 1 0]
#guard eqList (Mat.trmvT .lower .nonUnit L x).toList [c 1 3, c (-1) 0]
#guard eqList (Mat.trmvC .upper .nonUnit U x).toList [c 1 (-1), c 3 0]
#guard eqList (Mat.trmvC .lower .unit L x).toList [c 1 2, c 0 1]

/-! ## `trsv`, `trsvT` and `trsvC`: they undo the products above. -/

#guard eqList (Mat.trsv .upper .nonUnit U (v [c 1 3, c (-1) 0])).toList x.toList
#guard eqList (Mat.trsv .upper .unit U (v [c 1 2, c 0 1])).toList x.toList
#guard eqList (Mat.trsv .lower .nonUnit L (v [c 1 1, c 1 0])).toList x.toList
#guard eqList (Mat.trsv .lower .unit L (v [c 1 0, c 2 1])).toList x.toList
#guard eqList (Mat.trsvT .upper .nonUnit U (v [c 1 1, c 1 0])).toList x.toList
#guard eqList (Mat.trsvT .lower .nonUnit L (v [c 1 3, c (-1) 0])).toList x.toList
#guard eqList (Mat.trsvC .upper .nonUnit U (v [c 1 (-1), c 3 0])).toList x.toList
#guard eqList (Mat.trsvC .lower .unit L (v [c 1 2, c 0 1])).toList x.toList

-- Without the zero skips of LAPACK 3.12: a zero `x[j]` still multiplies column `j`, so an
-- infinity above it gives `NaN`.
#guard ((Mat.trmv .upper .unit (.ofFn fun i j => #[#[c 1 0, c (1/0) 0], #[c 0 0, c 1 0]][i]![j]!)
  (v [c 1 0, c 0 0])).toList.head!.re).isNaN

end BLASTest.ComplexFloat32.Tri
