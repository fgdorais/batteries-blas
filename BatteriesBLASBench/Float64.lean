/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BatteriesBLAS
public import BatteriesBLASBench.Basic

/-!
# Benchmarks of the `Float64` routines

The benchmarks of `lake exe bench`, with hand-written reference loops for comparison.
-/

open ScalarArray

namespace BLASBench.Float64

/-- A vector of `n` elements computed from their indices. -/
def vec (n : Nat) : Float64Array := .ofFn (n := n) fun i => (i.val % 7).toFloat - 3

/-- An index below `a.usize` is a valid index of `a`. -/
theorem lt_size_of_lt_usize {a : Float64Array} {i : USize} (h : i < a.usize) : i.toNat < a.size :=
  Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) a.toNat_usize_le

/-
The references are hand-written loops over `USize` indices bounded by `usize`, with unchecked reads
and writes, so that a ratio below 1 isn't due to a slow reference. They use scalar-arrays'
`Float64Array`, which has the lemmas on `usize` and `uset` that prove the indices valid.
-/

/-- `α * x + y`. -/
partial def refAxpy (α : Float) (x y : Float64Array) : Float64Array :=
  if hs : x.size = y.size then loop hs y rfl 0 else y
where
  /-- The loop from index `i`, over `z` of the size of `y`. -/
  loop (hs : x.size = y.size) (z : Float64Array) (hz : z.size = y.size) (i : USize) :
      Float64Array :=
    if h : i < x.usize then
      have hx := lt_size_of_lt_usize h
      loop hs (z.uset i (α * x.uget i hx + z.uget i (by lia)) (by lia)) (by simp [hz]) (i + 1)
    else z

/-- The dot product. -/
partial def refDot (x y : Float64Array) : Float :=
  if hs : x.size = y.size then loop hs 0 0 else 0
where
  /-- The loop from index `i`. -/
  loop (hs : x.size = y.size) (i : USize) (s : Float) : Float :=
    if h : i < x.usize then
      have hx := lt_size_of_lt_usize h
      loop hs (i + 1) (s + x.uget i hx * y.uget i (by lia))
    else s

/-- A sum of `f x[i]`. -/
@[specialize] partial def refSum (f : Float → Float) (x : Float64Array) : Float :=
  loop 0 0
where
  /-- The loop from index `i`. -/
  @[specialize] loop (i : USize) (s : Float) : Float :=
    if h : i < x.usize then loop (i + 1) (s + f (x.uget i (lt_size_of_lt_usize h))) else s

/-- `iamax`. -/
partial def refIamax (x : Float64Array) : Nat :=
  loop 0 0 0
where
  /-- The loop from index `i`. -/
  loop (i : USize) (k : USize) (m : Float) : Nat :=
    if h : i < x.usize then
      let a := (x.uget i (lt_size_of_lt_usize h)).abs
      if i == 0 || a > m then loop (i + 1) i a else loop (i + 1) k m
    else k.toNat

/-- The benchmarks. -/
def rows (rounds n : Nat) : IO (List Row) := do
  let x := vec n
  let v : BLAS.Float64.Vec n := .ofArray x (by simp [x, vec])
  let axpy ← time rounds n fun _ => Id.run do
    let mut z := v
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.axpy 0.5 v z
    return z.data[0]!
  let axpy' ← time rounds n fun _ => Id.run do
    let mut z := x
    for _ in [0:reps] do
      z := refAxpy 0.5 x z
    return z[0]!
  let dot ← time rounds n fun _ => BLAS.Float64.Vec.dot v v
  let dot' ← time rounds n fun _ => refDot x x
  let nrm2 ← time rounds n fun _ => BLAS.Float64.Vec.nrm2 v
  let nrm2' ← time rounds n fun _ => (refSum (fun a => a * a) x).sqrt
  let iamax ← time rounds n fun _ => (BLAS.Float64.Vec.iamax! v).toFloat
  let iamax' ← time rounds n fun _ => (refIamax x).toFloat
  -- A strided vector: every other element of an array of `2 * n`, against the contiguous one.
  let x2 := vec (2 * n)
  let v2 : BLAS.Float64.Vec n := (BLAS.Float64.Vec.ofStride? x2 0 2).getD v
  let axpy2 ← time rounds n fun _ => Id.run do
    let mut z := v2
    for _ in [0:reps] do
      z := BLAS.Float64.Vec.axpy 0.5 v2 z
    return z.data[0]!
  return [⟨s!"axpy ×{reps}", axpy, some axpy'⟩, ⟨"dot", dot, some dot'⟩,
    ⟨"nrm2", nrm2, some nrm2'⟩, ⟨"iamax", iamax, some iamax'⟩,
    ⟨s!"axpy ×{reps}, stride 2 / stride 1", axpy2, some axpy⟩]

/-- An `m × m` matrix computed from its indices. -/
def mat (m s : Nat) : BLAS.Float64.Mat m m :=
  .ofFn fun i j => ((i.val * 7 + j.val * 13 + s) % 11).toFloat - 5

/--
The `gemm` benchmarks for `m × m` matrices: the rows of `gemm`, `gemmTN`, and `gemmtr` on the
lower triangle, and the floating-point operations of `gemm`. Each timed call depends on its
argument, which is `m`, so that the compiler can't hoist it out of the timing loop.
-/
def gemmRows (rounds m : Nat) : IO (List Row × Nat) := do
  let A := mat m 1
  let B := mat m 2
  let C := mat m 3
  let α (q : Nat) := 1.5 + (q - m).toFloat
  let tb ← time rounds m fun q => (BLAS.Float64.Mat.gemm (α q) A B 0.5 C).data[0]!
  let ttn ← time rounds m fun q => (BLAS.Float64.Mat.gemmTN (α q) A B 0.5 C).data[0]!
  let ttr ← time rounds m fun q => (BLAS.Float64.Mat.gemmtr .lower (α q) A B 0.5 C).data[0]!
  return ([⟨s!"gemm {m}", tb, none⟩, ⟨s!"gemmTN {m} / gemm", ttn, some tb⟩,
    ⟨s!"gemmtr lower {m}, half the operations / gemm", ttr, some tb⟩], 2 * m * m * m)

/--
The Level 2 benchmarks for `m × m` matrices, ten calls per round: `gemv`, `gemvT` and `ger`,
`trsv` and `trsvT` on the lower triangle, `symv` on the lower triangle and `syr2` on the upper
one. Each makes `2 * m * m` floating-point operations per call, except the triangular ones, which
make about `m * m`.
-/
def level2Rows (rounds m : Nat) : IO (List Row × Nat) := do
  let A := mat m 1
  let x : BLAS.Float64.Vec m := .ofArray (vec m) (by simp [vec])
  let α (q : Nat) := 1.5 + (q - m).toFloat
  let tv ← time rounds m fun q => Id.run do
    let mut y := x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.gemv (α q) A x 0.5 y
    return y.data[0]!
  let tt ← time rounds m fun q => Id.run do
    let mut y := x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.gemvT (α q) A x 0.5 y
    return y.data[0]!
  let tg ← time rounds m fun q => Id.run do
    let mut B := A
    for _ in [0:reps] do
      B := BLAS.Float64.Mat.ger (α q) x x B
    return B.data[0]!
  let T : BLAS.Float64.Mat m m := .ofFn fun i j =>
    if i.val = j.val then (m + 4 + i.val).toFloat
    else ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let tl ← time rounds m fun q => Id.run do
    let mut y := BLAS.Float64.Vec.scal (α q) x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.trsv .lower .nonUnit T y
    return y.data[0]!
  let tlT ← time rounds m fun q => Id.run do
    let mut y := BLAS.Float64.Vec.scal (α q) x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.trsvT .lower .nonUnit T y
    return y.data[0]!
  let tsl ← time rounds m fun q => Id.run do
    let mut y := x
    for _ in [0:reps] do
      y := BLAS.Float64.Mat.symv .lower (α q) T x 0.5 y
    return y.data[0]!
  let ty2u ← time rounds m fun q => Id.run do
    let mut B := A
    for _ in [0:reps] do
      B := BLAS.Float64.Mat.syr2 .upper (α q) x x B
    return B.data[0]!
  return ([⟨s!"gemv {m} ×{reps}", tv, none⟩, ⟨s!"gemvT {m} ×{reps}", tt, none⟩,
    ⟨s!"ger {m} ×{reps}", tg, none⟩, ⟨s!"trsv lower {m} ×{reps}", tl, none⟩,
    ⟨s!"trsvT lower {m} ×{reps} / trsv", tlT, some tl⟩,
    ⟨s!"symv lower {m} ×{reps} / gemv", tsl, some tv⟩,
    ⟨s!"syr2 upper {m} ×{reps} / ger", ty2u, some tg⟩],
    2 * m * m * reps)

/--
The Level 3 benchmarks for `m × m` matrices: `syrk`, `syrkT`, `trsm`, `trsmT`, `trmm`, `symm`
and `syr2k` on the lower triangle and `trsmRight` on the upper one, with a non-unit diagonal. Each
makes about `m * m * m` floating-point operations per call, and `2 * m * m * m` for `symm` and
`syr2k`. As for `gemm`, each call copies the shared `C` or `B` first.
-/
def level3Rows (rounds m : Nat) : IO (List Row × Nat) := do
  let A := mat m 1
  let B := mat m 2
  let C := mat m 3
  let α (q : Nat) := 1.5 + (q - m).toFloat
  let T : BLAS.Float64.Mat m m := .ofFn fun i j =>
    if i.val = j.val then (m + 4 + i.val).toFloat
    else ((i.val * 7 + j.val * 13) % 11).toFloat - 5
  let ts ← time rounds m fun q => (BLAS.Float64.Mat.syrk .lower (α q) A 0.5 C).data[0]!
  let tt ← time rounds m fun q => (BLAS.Float64.Mat.syrkT .lower (α q) A 0.5 C).data[0]!
  let tl ← time rounds m fun q => (BLAS.Float64.Mat.trsm .lower .nonUnit (α q) T C).data[0]!
  let tr ← time rounds m fun q => (BLAS.Float64.Mat.trsmRight .upper .nonUnit (α q) T C).data[0]!
  let tlT ← time rounds m fun q => (BLAS.Float64.Mat.trsmT .lower .nonUnit (α q) T C).data[0]!
  let tm ← time rounds m fun q => (BLAS.Float64.Mat.trmm .lower .nonUnit (α q) T C).data[0]!
  let tsm ← time rounds m fun q => (BLAS.Float64.Mat.symm .lower (α q) T A 0.5 C).data[0]!
  let ts2 ← time rounds m fun q => (BLAS.Float64.Mat.syr2k .lower (α q) A B 0.5 C).data[0]!
  return ([⟨s!"syrk lower {m}", ts, none⟩, ⟨s!"syrkT lower {m}", tt, none⟩,
    ⟨s!"trsm lower {m}", tl, none⟩, ⟨s!"trsmRight upper {m}", tr, none⟩,
    ⟨s!"trsmT lower {m} / trsm", tlT, some tl⟩, ⟨s!"trmm lower {m} / trsm", tm, some tl⟩,
    ⟨s!"symm lower {m}, 2 m³ operations", tsm, none⟩,
    ⟨s!"syr2k lower {m}, 2 m³ operations / syrk", ts2, some ts⟩], m * m * m)

/--
All the benchmarks: Level 1, Level 2, `gemm`, and the rest of Level 3, each with its floating-point
operations.
-/
public def all (rounds n : Nat) :
    IO (List Row × List (List Row × Nat) × List (List Row × Nat) × List (List Row × Nat)) := do
  let rows ← rows rounds n
  let level2 ← level2Sizes.mapM (level2Rows rounds)
  let gemm ← gemmSizes.mapM (gemmRows rounds)
  let level3 ← level3Sizes.mapM (level3Rows rounds)
  return (rows, level2, gemm, level3)

end BLASBench.Float64
