/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BatteriesBLAS.Float64.Vec
public import BatteriesBLAS.Float64.Loop
public import BatteriesBLAS.Float64.Level1
public import BatteriesBLAS.Float64.Rot
public import BatteriesBLAS.Float64.PMat
public import BatteriesBLAS.Float64.Mat
public import BatteriesBLAS.Float64.Level2
public import BatteriesBLAS.Float64.Trsv
public import BatteriesBLAS.Float64.Syrk
public import BatteriesBLAS.Float64.Level3
public import BatteriesBLAS.Float64.GemmBlocked
public import BatteriesBLAS.Float64.Gemm
public import BatteriesBLAS.Float64.GemmT
public import BatteriesBLAS.Float64.TrsvT
public import BatteriesBLAS.Float64.Trmv
public import BatteriesBLAS.Float64.Trsm
public import BatteriesBLAS.Float64.TrsmT
public import BatteriesBLAS.Float64.Trmm
public import BatteriesBLAS.Float64.TrmmRight
public import BatteriesBLAS.Float64.Symv
public import BatteriesBLAS.Float64.Symm
public import BatteriesBLAS.Float64.Syr
public import BatteriesBLAS.Float64.Syr2k
public import BatteriesBLAS.Float64.Gemmtr
public import BatteriesBLAS.Float64.Gbmv
public import BatteriesBLAS.Float64.Sbmv
public import BatteriesBLAS.Float64.Tbmv
public import BatteriesBLAS.Float64.Tbsv
public import BatteriesBLAS.Float64.Packed
public import BatteriesBLAS.Float64.Tpmv
public import BatteriesBLAS.Float64.Tpsv
public import BatteriesBLAS.Float64.Spmv
public import BatteriesBLAS.Float64.Spr
public import BatteriesBLAS.Float64.View
public import BatteriesBLAS.Float64.BandView
public import BatteriesBLAS.Float64.PackedView

/-!
# BLAS on `Float`

The routines on vectors and matrices of `Float`, stored in `Float64Array`s.
-/
