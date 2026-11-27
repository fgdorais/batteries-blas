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
Tests for the complex packed routines of Level 2 on `ComplexFloat32`: `hpmv`, `hpr`, `hpr2`,
`tpmv`, `tpmvT`, `tpmvC`, `tpsv`, `tpsvT` and `tpsvC`. Each one is compared with the dense routine
on the same triangle, which runs the same operations in the same order.
-/

open ScalarArray BLAS.ComplexFloat32

namespace BLASTest.ComplexFloat32.Packed

/-- The complex number `re + im * I`. -/
def c (re im : Float32) : ComplexFloat32 := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat32) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- The elements of the matrices: nonzero, with thirds. -/
def f (i j : Nat) : ComplexFloat32 :=
  c ((1 + (3 * i + j) % 4).toFloat32 / 3 + (if i = j then 2 else 0))
    ((1 + (i + 2 * j) % 3).toFloat32 / 3 - 1)

/-- A vector with nonzero elements. -/
def x (n : Nat) : Vec n := .ofFn fun i => c ((i.val + 1).toFloat32 / 3) ((i.val + 2).toFloat32 / 7)

/-- Another vector with nonzero elements. -/
def y (n : Nat) : Vec n := .ofFn fun i => c (2 - i.val.toFloat32 / 5) (i.val.toFloat32 / 3 + 1)

/-- A vector whose elements `1` and `3` are zero. -/
def z (n : Nat) : Vec n := .ofFn fun i =>
  if i.val = 1 ∨ i.val = 3 then c 0 0 else c ((i.val + 1).toFloat32 / 3) (1 / 7)

def α : ComplexFloat32 := c (1 / 3) (-2)
def β : ComplexFloat32 := c (-1 / 2) (1 / 7)

/-- The dense `5 × 5` matrix of `f`, with `99 + 99 * I` outside the triangle `uplo`. -/
def D (uplo : BLAS.Float32.Uplo) : Mat 5 5 := .ofFn fun i j =>
  match uplo with
  | .upper => if i.val ≤ j.val then f i.val j.val else c 99 99
  | .lower => if j.val ≤ i.val then f i.val j.val else c 99 99

/-- The triangle `uplo` of a `5 × 5` matrix, packed by columns. -/
def pack (uplo : BLAS.Float32.Uplo) (A : Mat 5 5) : List ComplexFloat32 :=
  match uplo with
  | .upper => (List.range 5).flatMap fun j => (List.range (j + 1)).map fun i => A.bget0 i j
  | .lower => (List.range 5).flatMap fun j => (List.range' j (5 - j)).map fun i => A.bget0 i j

/-- The packed triangle `uplo` of `D uplo`. -/
def P (uplo : BLAS.Float32.Uplo) : Vec (5 * (5 + 1) / 2) :=
  .ofFn fun q => (pack uplo (D uplo)).getD q.val (c 0 0)

/-- The four combinations of the triangle and the diagonal. -/
def cases : List (BLAS.Float32.Uplo × BLAS.Float32.Diag) :=
  [(.upper, .nonUnit), (.upper, .unit), (.lower, .nonUnit), (.lower, .unit)]

def uplos : List BLAS.Float32.Uplo := [.upper, .lower]

#guard uplos.all fun u => (P u).toList.length == 15

/-! ## `hpmv` -/

#guard uplos.all fun u =>
  eqList (Mat.hpmv u α (P u) (x 5) β (y 5)).toList (Mat.hemv u α (D u) (x 5) β (y 5)).toList
#guard uplos.all fun u =>
  eqList (Mat.hpmv u (c 0 0) (P u) (x 5) (c 1 0) (y 5)).toList (y 5).toList

/-! ## `hpr` and `hpr2` -/

#guard uplos.all fun u =>
  eqList (Mat.hpr u (-2 / 3) (x 5) (P u)).toList (pack u (Mat.her u (-2 / 3) (x 5) (D u)))
#guard uplos.all fun u =>
  eqList (Mat.hpr u (-2 / 3) (z 5) (P u)).toList (pack u (Mat.her u (-2 / 3) (z 5) (D u)))
#guard uplos.all fun u =>
  eqList (Mat.hpr2 u α (x 5) (y 5) (P u)).toList (pack u (Mat.her2 u α (x 5) (y 5) (D u)))
#guard uplos.all fun u =>
  eqList (Mat.hpr2 u α (z 5) (z 5) (P u)).toList (pack u (Mat.her2 u α (z 5) (z 5) (D u)))

/-! ## `tpmv`, `tpmvT` and `tpmvC` -/

#guard cases.all fun (u, d) =>
  eqList (Mat.tpmv u d (P u) (x 5)).toList (Mat.trmv u d (D u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tpmvT u d (P u) (x 5)).toList (Mat.trmvT u d (D u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tpmvC u d (P u) (x 5)).toList (Mat.trmvC u d (D u) (x 5)).toList

/-! ## `tpsv`, `tpsvT` and `tpsvC` -/

#guard cases.all fun (u, d) =>
  eqList (Mat.tpsv u d (P u) (x 5)).toList (Mat.trsv u d (D u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tpsvT u d (P u) (x 5)).toList (Mat.trsvT u d (D u) (x 5)).toList
#guard cases.all fun (u, d) =>
  eqList (Mat.tpsvC u d (P u) (x 5)).toList (Mat.trsvC u d (D u) (x 5)).toList

end BLASTest.ComplexFloat32.Packed
