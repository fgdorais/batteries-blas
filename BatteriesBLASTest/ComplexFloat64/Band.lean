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
Tests for the complex band routines of Level 2 on `ComplexFloat`: `gbmv`, `gbmvT`, `gbmvC`,
`hbmv`, `tbmv`, `tbmvT`, `tbmvC`, `tbsv`, `tbsvT` and `tbsvC`. Each one is compared with the
dense routine on the same matrix, with zeros outside the band: the dense routine runs the same
operations, and adds or subtracts products with those zeros, which don't change the nonzero values
here.
-/

open ScalarArray BLAS.ComplexFloat64

namespace BLASTest.ComplexFloat64.Band

/-- The complex number `re + im * I`. -/
def c (re im : Float) : ComplexFloat := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The elements of the matrices: nonzero, with thirds. -/
def f (i j : Nat) : ComplexFloat :=
  c ((1 + (3 * i + j) % 4).toFloat / 3) ((1 + (i + 2 * j) % 3).toFloat / 3 - 1)

/-- A vector with nonzero elements. -/
def x (n : Nat) : Vec n := .ofFn fun i => c ((i.val + 1).toFloat / 3) ((i.val + 2).toFloat / 7)

/-- Another vector with nonzero elements. -/
def y (n : Nat) : Vec n := .ofFn fun i => c (2 - i.val.toFloat / 5) (i.val.toFloat / 3 + 1)

def α : ComplexFloat := c (1 / 3) (-2)
def β : ComplexFloat := c (-1 / 2) (1 / 7)

/-! ## `gbmv`, `gbmvT` and `gbmvC` -/

/-- The band storage of the `6 × 5` matrix `f` with `1` subdiagonal and `2` superdiagonals. -/
def GB : Mat (1 + 2 + 1) 5 := .ofFn fun r j =>
  if j.val ≤ r.val + j.val - 2 + 2 ∧ 2 ≤ r.val + j.val ∧ r.val + j.val - 2 < 6 then
    f (r.val + j.val - 2) j.val
  else c 99 99

/-- The dense `6 × 5` matrix of `GB`, with zeros outside the band. -/
def GD : Mat 6 5 := .ofFn fun i j =>
  if j.val ≤ i.val + 2 ∧ i.val ≤ j.val + 1 then f i.val j.val else c 0 0

#guard eqList (Mat.gbmv 1 2 α GB (x 5) β (y 6)).toList (Mat.gemv α GD (x 5) β (y 6)).toList
#guard eqList (Mat.gbmvT 1 2 α GB (x 6) β (y 5)).toList (Mat.gemvT α GD (x 6) β (y 5)).toList
#guard eqList (Mat.gbmvC 1 2 α GB (x 6) β (y 5)).toList (Mat.gemvC α GD (x 6) β (y 5)).toList
#guard eqList (Mat.gbmv 1 2 (c 0 0) GB (x 5) (c 0 0) (y 6)).toList (List.replicate 6 (c 0 0))
#guard eqList (Mat.gbmvT 1 2 (c 0 0) GB (x 6) (c 1 0) (y 5)).toList (y 5).toList

/-! ## The band storage of a triangle with `2` off-diagonals, of order `5` -/

/-- The band storage of the triangle `uplo` of `f`, with `99 + 99 * I` outside the matrix. -/
def TB (uplo : BLAS.Float64.Uplo) : Mat (2 + 1) 5 := .ofFn fun r j =>
  match uplo with
  | .upper => if 2 ≤ r.val + j.val then f (r.val + j.val - 2) j.val else c 99 99
  | .lower => if r.val + j.val < 5 then f (r.val + j.val) j.val else c 99 99

/-- The dense matrix of `TB uplo`, with zeros in the triangle outside the band. -/
def TD (uplo : BLAS.Float64.Uplo) : Mat 5 5 := .ofFn fun i j =>
  match uplo with
  | .upper =>
    if i.val ≤ j.val then (if j.val ≤ i.val + 2 then f i.val j.val else c 0 0) else c 99 99
  | .lower =>
    if j.val ≤ i.val then (if i.val ≤ j.val + 2 then f i.val j.val else c 0 0) else c 99 99

/-- The four combinations of the triangle and the diagonal. -/
def cases : List (BLAS.Float64.Uplo × BLAS.Float64.Diag) :=
  [(.upper, .nonUnit), (.upper, .unit), (.lower, .nonUnit), (.lower, .unit)]

/-! ## `hbmv` -/

#guard [BLAS.Float64.Uplo.upper, .lower].all fun u =>
  eqList (Mat.hbmv u α (TB u) (x 5) β (y 5)).toList (Mat.hemv u α (TD u) (x 5) β (y 5)).toList

/-! ## `tbmv`, `tbmvT` and `tbmvC` -/

#guard cases.all fun (u, d) =>
  eqList (Mat.tbmv u d (TB u) (x 5)).toList (Mat.trmv u d (TD u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tbmvT u d (TB u) (x 5)).toList (Mat.trmvT u d (TD u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tbmvC u d (TB u) (x 5)).toList (Mat.trmvC u d (TD u) (x 5)).toList

/-! ## `tbsv`, `tbsvT` and `tbsvC` -/

#guard cases.all fun (u, d) =>
  eqList (Mat.tbsv u d (TB u) (x 5)).toList (Mat.trsv u d (TD u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tbsvT u d (TB u) (x 5)).toList (Mat.trsvT u d (TD u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tbsvC u d (TB u) (x 5)).toList (Mat.trsvC u d (TD u) (x 5)).toList

end BLASTest.ComplexFloat64.Band
