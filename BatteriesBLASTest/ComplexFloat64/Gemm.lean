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
Tests for the complex matrix products: `gemm` and its eight variants with `A` or `B` transposed
or conjugated and transposed.
-/

open ScalarArray BLAS.ComplexFloat64

namespace BLASTest.ComplexFloat64.Gemm

/-- The complex number `re + im * I`. -/
def c (re im : Float) : ComplexFloat := ⟨re, im⟩

/-- Whether two lists of complex numbers are equal, part by part, as IEEE numbers. -/
def eqList (a b : List ComplexFloat) : Bool :=
  a.length == b.length && (a.zip b).all fun p => p.1 == p.2

/-- `[[1 + I, 2, I], [0, I, 3 - I]]`. -/
def A : Mat 2 3 := .ofFn fun i j => #[#[c 1 1, c 2 0, c 0 1], #[c 0 0, c 0 1, c 3 (-1)]][i]![j]!

/-- `[[1, I], [2, 1 - I], [-1, 2 * I]]`. -/
def B : Mat 3 2 :=
  .ofFn fun i j => #[#[c 1 0, c 0 1], #[c 2 0, c 1 (-1)], #[c (-1) 0, c 0 2]][i]![j]!

/-- The transpose of `M`. -/
def tr {m n : Nat} (M : Mat m n) : Mat n m := .ofFn fun i j => M[(j.val, i.val)]

/-- The conjugate transpose of `M`. -/
def ct {m n : Nat} (M : Mat m n) : Mat n m := .ofFn fun i j => M[(j.val, i.val)].conj

/-- The `2 × 2` matrix of zeros. -/
def Z : Mat 2 2 := .ofFn fun _ _ => c 0 0

/-- The `2 × 2` matrix of ones. -/
def O : Mat 2 2 := .ofFn fun _ _ => c 1 0

/-- `A * B = [[5, -1 - I], [-3 + 3 * I, 3 + 7 * I]]`, column after column. -/
def AB : List ComplexFloat := [c 5 0, c (-3) 3, c (-1) (-1), c 3 7]

/-! ## The nine variants, each given the factors that make the product `A * B` -/

#guard eqList (Mat.gemm (c 1 0) A B (c 0 0) Z).toList AB
#guard eqList (Mat.gemmNT (c 1 0) A (tr B) (c 0 0) Z).toList AB
#guard eqList (Mat.gemmNC (c 1 0) A (ct B) (c 0 0) Z).toList AB
#guard eqList (Mat.gemmTN (c 1 0) (tr A) B (c 0 0) Z).toList AB
#guard eqList (Mat.gemmTT (c 1 0) (tr A) (tr B) (c 0 0) Z).toList AB
#guard eqList (Mat.gemmTC (c 1 0) (tr A) (ct B) (c 0 0) Z).toList AB
#guard eqList (Mat.gemmCN (c 1 0) (ct A) B (c 0 0) Z).toList AB
#guard eqList (Mat.gemmCT (c 1 0) (ct A) (tr B) (c 0 0) Z).toList AB
#guard eqList (Mat.gemmCC (c 1 0) (ct A) (ct B) (c 0 0) Z).toList AB

/-! ## `α` and `β`: `I * A * B + 2 * O` -/

#guard eqList (Mat.gemm (c 0 1) A B (c 2 0) O).toList [c 2 5, c (-1) (-3), c 3 (-1), c (-5) 3]
#guard eqList (Mat.gemmCT (c 0 1) (ct A) (tr B) (c 2 0) O).toList
  [c 2 5, c (-1) (-3), c 3 (-1), c (-5) 3]

-- `α = 0` scales `C` by `β`, without reading `A` or `B`.
#guard eqList (Mat.gemmTN (c 0 0) (tr A) B (c 2 0) O).toList [c 2 0, c 2 0, c 2 0, c 2 0]

/-! ## Empty sums, as in `zgemm` -/

/-- An infinite `α`. -/
def inf : ComplexFloat := c (1 / 0) 0

-- With `k = 0` and `β = 1`, `C` is returned as it is.
#guard eqList (Mat.gemmTN inf (.ofFn fun _ _ => c 1 0 : Mat 0 2) (.ofFn fun _ _ => c 1 0 : Mat 0 2)
  (c 1 0) O).toList O.toList
-- With `k = 0` and `β ≠ 1`, `A` as it is scales `C` by `β`, but `A` transposed computes
-- `mul α 0 + mul β C[i, j]`, which is `NaN` for an infinite `α`.
#guard eqList (Mat.gemm inf (.ofFn fun _ _ => c 1 0 : Mat 2 0) (.ofFn fun _ _ => c 1 0 : Mat 0 2)
  (c 2 0) O).toList [c 2 0, c 2 0, c 2 0, c 2 0]
#guard ((Mat.gemmTN inf (.ofFn fun _ _ => c 1 0 : Mat 0 2) (.ofFn fun _ _ => c 1 0 : Mat 0 2)
  (c 2 0) O).toList.head!.re).isNaN

end BLASTest.ComplexFloat64.Gemm
