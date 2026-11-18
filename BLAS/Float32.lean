/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BLAS.Float32.Vec
public import BLAS.Float32.Loop
public import BLAS.Float32.Level1
public import BLAS.Float32.Rot
public import BLAS.Float32.PMat
public import BLAS.Float32.Mat
public import BLAS.Float32.Level2
public import BLAS.Float32.Trsv
public import BLAS.Float32.Syrk
public import BLAS.Float32.Level3
public import BLAS.Float32.GemmBlocked
public import BLAS.Float32.Gemm
public import BLAS.Float32.GemmT
public import BLAS.Float32.TrsvT
public import BLAS.Float32.Trmv
public import BLAS.Float32.Trsm
public import BLAS.Float32.TrsmT
public import BLAS.Float32.Trmm
public import BLAS.Float32.TrmmRight
public import BLAS.Float32.Symv
public import BLAS.Float32.Symm
public import BLAS.Float32.Syr
public import BLAS.Float32.Syr2k
public import BLAS.Float32.Gemmtr
public import BLAS.Float32.View

/-!
# BLAS on `Float32`

The routines on vectors and matrices of `Float32`, stored in `Float32Array`s.
-/
