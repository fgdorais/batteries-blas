/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# The operations of the `blas%` notation

`blas%` (in `BLAS.Notation`) reads an update such as `y := α • A * x + β • y` and expands it to a
single call of one of the classes below, such as `MulAdd.run α A x β y`. Each instance of a class
is one routine of the library, for one kind of operand: `MulAdd` on a matrix and a vector is
`gemv`, on a transposed matrix and a vector `gemvT`, and on two matrices `gemm`. An update that no
instance covers, such as `Aᵀ * B` for which the library has no routine, is a type class error at
compile time, never a slower combination of routines.

The classes are independent of the element type. Their instances, with a `simp` lemma for each
that unfolds it to its routine, are next to the routines' views, in `BLAS.Float64.View` and
`BLAS.Float32.View`.
-/

namespace BLAS

/--
The transpose of the matrix `mat`, with no copy: a view that selects the transposed routines, such
as `gemvT` for `Aᵀ * x`.
-/
public structure Transpose (α : Type) where
  /-- The matrix that is transposed. -/
  mat : α

/--
`MulAdd.run α a x β y` is `α * a * x + β * y`, over `y`, by a single routine: `gemv`, `gemvT` or
`gemm`, depending on the kinds of `a` and `x`. `blas%` expands `y := α • a * x + β • y` to it.
-/
public class MulAdd (S : outParam Type) (A X Y : Type) where
  /-- `run α a x β y` is `α * a * x + β * y`, over `y`. -/
  run : S → A → X → S → Y → Y

/-- `Axpy.run α x y` is `α * x + y`, over `y`. `blas%` expands `y := α • x + y` to it. -/
public class Axpy (S : outParam Type) (X : Type) where
  /-- `run α x y` is `α * x + y`, over `y`. -/
  run : S → X → X → X

/-- `Scal.run α x` is `α * x`, over `x`. `blas%` expands `x := α • x` to it. -/
public class Scal (S : outParam Type) (X : Type) where
  /-- `run α x` is `α * x`, over `x`. -/
  run : S → X → X

/-- `Copy.run x y` is `x`, over `y`. `blas%` expands `y := x` to it. -/
public class Copy (X : Type) where
  /-- `run x y` copies `x` over `y`. -/
  run : X → X → X

/--
`Solve.run t x` is `t⁻¹ * x`, over `x`, for a triangular view `t`. `blas%` expands
`x := t⁻¹ * x` to it.
-/
public class Solve (T X : Type) where
  /-- `run t x` solves `t * y = x`, over `x`. -/
  run : T → X → X

/--
`ScaledSolve.run α t b` is `α * t⁻¹ * b`, over `b`, for a triangular view `t`. `blas%` expands
`b := α • t⁻¹ * b` to it.
-/
public class ScaledSolve (S : outParam Type) (T X : Type) where
  /-- `run α t b` solves `t * y = α * b`, over `b`. -/
  run : S → T → X → X

/--
`SolveRight.run α b t` is `α * b * t⁻¹`, over `b`, for a triangular view `t`. `blas%` expands
`b := α • b * t⁻¹` to it.
-/
public class SolveRight (S : outParam Type) (T X : Type) where
  /-- `run α b t` solves `y * t = α * b`, over `b`. -/
  run : S → X → T → X

end BLAS
