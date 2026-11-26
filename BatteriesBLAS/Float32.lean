/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float32.Vec
public import BatteriesBLAS.Float32.Loop
public import BatteriesBLAS.Float32.Level1
public import BatteriesBLAS.Float32.Rot
public import BatteriesBLAS.Float32.PMat
public import BatteriesBLAS.Float32.Mat
public import BatteriesBLAS.Float32.Level2
public import BatteriesBLAS.Float32.Trsv
public import BatteriesBLAS.Float32.Syrk
public import BatteriesBLAS.Float32.Level3
public import BatteriesBLAS.Float32.GemmBlocked
public import BatteriesBLAS.Float32.Gemm
public import BatteriesBLAS.Float32.GemmT
public import BatteriesBLAS.Float32.TrsvT
public import BatteriesBLAS.Float32.Trmv
public import BatteriesBLAS.Float32.Trsm
public import BatteriesBLAS.Float32.TrsmT
public import BatteriesBLAS.Float32.Trmm
public import BatteriesBLAS.Float32.TrmmRight
public import BatteriesBLAS.Float32.Symv
public import BatteriesBLAS.Float32.Symm
public import BatteriesBLAS.Float32.Syr
public import BatteriesBLAS.Float32.Syr2k
public import BatteriesBLAS.Float32.Gemmtr
public import BatteriesBLAS.Float32.Gbmv
public import BatteriesBLAS.Float32.Sbmv
public import BatteriesBLAS.Float32.Tbmv
public import BatteriesBLAS.Float32.Tbsv
public import BatteriesBLAS.Float32.Packed
public import BatteriesBLAS.Float32.Tpmv
public import BatteriesBLAS.Float32.Tpsv
public import BatteriesBLAS.Float32.Spmv
public import BatteriesBLAS.Float32.Spr
public import BatteriesBLAS.Float32.View
public import BatteriesBLAS.Float32.BandView
public import BatteriesBLAS.Float32.PackedView

/-!
# BLAS on `Float32`

The routines on vectors and matrices of `Float32`, stored in `Float32Array`s.
-/
