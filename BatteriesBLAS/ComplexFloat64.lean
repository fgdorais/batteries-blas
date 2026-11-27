/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat64.Basic
public import BatteriesBLAS.ComplexFloat64.Vec
public import BatteriesBLAS.ComplexFloat64.Level1
public import BatteriesBLAS.ComplexFloat64.Rot
public import BatteriesBLAS.ComplexFloat64.Mat
public import BatteriesBLAS.ComplexFloat64.Level2

/-!
# BLAS on `ComplexFloat`

The complex routines, on vectors and matrices of `ComplexFloat` stored in `Float64Array`s with
interleaved real and imaginary parts, as in Fortran.
-/
