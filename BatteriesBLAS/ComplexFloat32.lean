/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.ComplexFloat32.Basic
public import BatteriesBLAS.ComplexFloat32.Vec
public import BatteriesBLAS.ComplexFloat32.Level1
public import BatteriesBLAS.ComplexFloat32.Rot
public import BatteriesBLAS.ComplexFloat32.Mat
public import BatteriesBLAS.ComplexFloat32.Level2
public import BatteriesBLAS.ComplexFloat32.Herm
public import BatteriesBLAS.ComplexFloat32.Tri
public import BatteriesBLAS.ComplexFloat32.Gemm
public import BatteriesBLAS.ComplexFloat32.Herm3
public import BatteriesBLAS.ComplexFloat32.Symm3
public import BatteriesBLAS.ComplexFloat32.Trmm3
public import BatteriesBLAS.ComplexFloat32.Trsm3
public import BatteriesBLAS.ComplexFloat32.Band

/-!
# BLAS on `ComplexFloat32`

The complex routines, on vectors and matrices of `ComplexFloat32` stored in `Float32Array`s with
interleaved real and imaginary parts, as in Fortran.
-/
