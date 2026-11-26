/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# The operations of the `blas%` notation

`blas%` (in `BatteriesBLAS.Notation`) reads an update such as `y := α • A * x + β • y` and expands
it to a single call of one of the classes below, such as `MulAdd.run α A x β y`. Each instance of a
class is one routine of the library, for one kind of operand: `MulAdd` on a matrix and a vector is
`gemv`, on a transposed matrix and a vector `gemvT`, on two matrices `gemm`, and on transposes
`gemmTN`, `gemmNT` and `gemmTT`, on a symmetric view `symv` or `symm`, and over a triangle `gemmtr`.
An update that no instance covers, such as `Aᵀ * x` with the wrong sizes, is a type class error at
compile time, never a slower combination of routines.

`MulAcc`, `RankKAcc` and `Rank2KAcc` are the updates with `β = 1`: an instance of `MulAdd`, `RankK`
or `Rank2K` gives one, and the routines with no `β`, `ger`, `syr` and `syr2`, have their own.

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
`MulAdd.run α a x β y` is `α * a * x + β * y`, over `y`, by a single routine: `gemv`, `gemvT`,
`gemm`, `gemmTN`, `gemmNT` or `gemmTT`, depending on the kinds of `a` and `x`. `blas%` expands
`y := α • a * x + β • y` to it.
-/
public class MulAdd (S : outParam Type) (A X Y : Type) where
  /-- `run α a x β y` is `α * a * x + β * y`, over `y`. -/
  run : S → A → X → S → Y → Y

/-- `Axpy.run α x y` is `α * x + y`, over `y`. `blas%` expands `y := α • x + y` to it. -/
public class Axpy (S : outParam Type) (X : Type) where
  /-- `run α x y` is `α * x + y`, over `y`. -/
  run : S → X → X → X

/--
`Axpby.run α x β y` is `α * x + β * y`, over `y`. `blas%` expands `y := α • x + β • y` to it, and
`y := α • x` with `β = 0`.
-/
public class Axpby (S : outParam Type) (X : Type) where
  /-- `run α x β y` is `α * x + β * y`, over `y`. -/
  run : S → X → S → X → X

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

/--
`MulAcc.run α a x y` is `α * a * x + y`, over `y`. `blas%` expands `y := α • a * x + y` to it. It
is `MulAdd.run α a x 1 y` if `MulAdd` has an instance, and otherwise a routine with no `β`, such as
`ger` for `A := α • x * yᵀ + A`.
-/
public class MulAcc (S : outParam Type) (A X Y : Type) where
  /-- `run α a x y` is `α * a * x + y`, over `y`. -/
  run : S → A → X → Y → Y

/-- `α * a * x + y` is `α * a * x + 1 * y`. -/
public instance (priority := low) {S A X Y : Type} [MulAdd S A X Y] [OfNat S 1] :
    MulAcc S A X Y where
  run α a x y := MulAdd.run α a x 1 y

@[simp] public theorem mulAcc_eq {S A X Y : Type} [MulAdd S A X Y] [OfNat S 1] (α : S) (a : A)
    (x : X) (y : Y) : MulAcc.run α a x y = MulAdd.run α a x 1 y := rfl

/--
`MulIn.run t x` is `t * x`, over `x`, for a triangular view `t`. `blas%` expands `x := t * x` to
it.
-/
public class MulIn (T X : Type) where
  /-- `run t x` is `t * x`, over `x`. -/
  run : T → X → X

/--
`ScaledMulIn.run α t b` is `α * t * b`, over `b`, for a triangular view `t`. `blas%` expands
`b := α • t * b` to it.
-/
public class ScaledMulIn (S : outParam Type) (T X : Type) where
  /-- `run α t b` is `α * t * b`, over `b`. -/
  run : S → T → X → X

/--
`MulInRight.run α b t` is `α * b * t`, over `b`, for a triangular view `t`. `blas%` expands
`b := α • b * t` to it.
-/
public class MulInRight (S : outParam Type) (T X : Type) where
  /-- `run α b t` is `α * b * t`, over `b`. -/
  run : S → X → T → X

/--
`RankK.run α a β c` is `α * a * aᵀ + β * c`, over the triangle `c`, if `a` is a matrix, and
`α * aᵀ * a + β * c` if `a` is the transpose `aᵀ`: `syrk` or `syrkT`. `blas%` expands
`C.lower := α • A * Aᵀ + β • C.lower` to it.
-/
public class RankK (S : outParam Type) (A C : Type) where
  /-- `run α a β c` is `α * a * aᵀ + β * c`, over the triangle `c`. -/
  run : S → A → S → C → C

/--
`RankKAcc.run α a c` is `α * a * aᵀ + c`, over the triangle `c`. It is `RankK.run α a 1 c` if
`RankK` has an instance, and otherwise a routine with no `β`, such as `syr` for a vector `a`.
-/
public class RankKAcc (S : outParam Type) (A C : Type) where
  /-- `run α a c` is `α * a * aᵀ + c`, over the triangle `c`. -/
  run : S → A → C → C

/-- `α * a * aᵀ + c` is `α * a * aᵀ + 1 * c`. -/
public instance (priority := low) {S A C : Type} [RankK S A C] [OfNat S 1] :
    RankKAcc S A C where
  run α a c := RankK.run α a 1 c

@[simp] public theorem rankKAcc_eq {S A C : Type} [RankK S A C] [OfNat S 1] (α : S) (a : A)
    (c : C) : RankKAcc.run α a c = RankK.run α a 1 c := rfl

/--
`Rank2K.run α a b β c` is `α * a * bᵀ + α * b * aᵀ + β * c`, over the triangle `c`, if `a` and `b`
are matrices, and `α * aᵀ * b + α * bᵀ * a + β * c` if they are the transposes `aᵀ` and `bᵀ`:
`syr2k` or `syr2kT`. `blas%` expands `C.lower := α • A * Bᵀ + α • B * Aᵀ + β • C.lower` to it.
-/
public class Rank2K (S : outParam Type) (A C : Type) where
  /-- `run α a b β c` is `α * a * bᵀ + α * b * aᵀ + β * c`, over the triangle `c`. -/
  run : S → A → A → S → C → C

/--
`Rank2KAcc.run α a b c` is `α * a * bᵀ + α * b * aᵀ + c`, over the triangle `c`. It is
`Rank2K.run α a b 1 c` if `Rank2K` has an instance, and otherwise a routine with no `β`, such as
`syr2` for vectors `a` and `b`.
-/
public class Rank2KAcc (S : outParam Type) (A C : Type) where
  /-- `run α a b c` is `α * a * bᵀ + α * b * aᵀ + c`, over the triangle `c`. -/
  run : S → A → A → C → C

/-- `α * a * bᵀ + α * b * aᵀ + c` is `α * a * bᵀ + α * b * aᵀ + 1 * c`. -/
public instance (priority := low) {S A C : Type} [Rank2K S A C] [OfNat S 1] :
    Rank2KAcc S A C where
  run α a b c := Rank2K.run α a b 1 c

@[simp] public theorem rank2KAcc_eq {S A C : Type} [Rank2K S A C] [OfNat S 1] (α : S) (a b : A)
    (c : C) : Rank2KAcc.run α a b c = Rank2K.run α a b 1 c := rfl

end BLAS
