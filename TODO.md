# TODO: performance

Possible performance improvements, found by comparing with OpenBLAS 0.3.26 and the Netlib reference
BLAS through `scripts/blas_compare.py` (see the README). The ratios are OpenBLAS's speed on one
thread over ours, measured on a 4-core Xeon with AVX-512. The estimates come from C prototypes
compiled like our kernels (`-O3 -ffp-contract=off`, baseline x86-64), and are not promises.

Every item keeps the specifications exact, in the order of operations of the reference BLAS.
Changes that would reorder them, such as partial sums in `dot`, `asum` and `nrm2`, are left out.

## `gemm` (3.4–4.4× behind, 4.4–6× in `Float32`)

- Measured, not worth it: wider kernels. In C prototypes in the exact order, a sweep of four
  columns and four terms runs at the speed of the current two columns and four terms (about 20
  GFLOP/s), and register tiles that carry 16 or 32 accumulators across the terms, which would need
  `inplace` loops with more than four variables, run at 5–9 GFLOP/s, slower than the current
  kernel: each accumulator is one chain of dependent additions.
- [ ] Revisit packing `A` and `B` with a wider kernel. Packing the 256 × 128 block of `A` measured
  within noise with the current kernel.
- [ ] Parallel `gemm` over blocks of columns of `C`, with `Task`. Each column is independent, so
  the result stays the same to the bit. OpenBLAS on 4 threads is 10–18× ahead.

## Transposed `gemm`

- [x] `gemmTN`, `gemmTT`: compute four rows of two columns of `C` per pass over four columns of
  `A` and two of `B`, with eight sums, so that each pass reads `A` once for two columns of `B`.
  Each sum keeps its order. About 1.15–1.4× locally (7.4–9.5 GFLOP/s at 256–1024, from 6.4–7.2).
  A Lean recursion with eight `Float` arguments and an eight-variable `inplace` loop measured the
  same.

## `gemmtr`

- [ ] `gemmtr`, `gemmtrNT`: run the kernel of `gemm`, two columns and four terms at a time, on the
  rows of each column in the triangle. They run at 5.3–7.7 GFLOP/s at 64–1024, at the speed of
  `gemmNaive`, one column and one term at a time, against 16–20 for `gemm`. Each element keeps its
  order of terms. Not measured yet.

## `syrk`, `syrkT`, `trsm` and `trsmRight` (6.6–9.3×, 8–11×, 2.2–4.5× and 3–8× behind at 256–1024)

- [x] `syrkT`: compute four elements of a column at a time, with the sums of `gemvT`. About 2×.
- [ ] `syrk`: sweep the rows of a block for several terms at a time, as `gemm` does. Each element
  keeps its order of terms, including the skipped ones.
- [x] `syrk`: two columns at a time, which share the reads of each column of `A`, with each column's
  skipped terms kept. About 1.5×.
- [x] `trsm`: solve four columns of `B` at a time, which share the reads of `A`. The columns are
  independent, so each keeps its order of operations. About 2× at 1024, where a column at a time
  read all of `A` from memory for each column, and 1–1.2× at 256.
- [ ] `trsmRight`: subtract four solved columns per pass over the rows of column `j`, as `gemv` adds
  four columns, so that each element keeps its order of operations. It is 3× behind at 256 and 8×
  at 1024, where `trsm` is 2.2× and 4.5×. Not measured yet.
- [x] `trsmT`: solve four columns of `B` at a time, which share the reads of `A`, each with its
  dot products in their order. About 2–3× locally (5.5–7 GFLOP/s at 256–1024, near `trsm`).
- [x] `trsmRightT`: solve a column at a time with Lean recursion over the columns (three nested
  `inplace` loops compiled to mutual calls), subtracting four solved columns per pass over the rows
  of the column, in order. At parity with `trsmRight` locally (5.7–12.5 GFLOP/s at 256–1024), from
  2–6× slower.
- [ ] `trmm`, `trmmRight`, `trmmRightT`: four columns of `B` at a time, as `trsm` does, or four
  added columns per pass over the rows, as `gemv` adds four columns. Each element keeps its order
  of operations. They run at 1–1.9× the time of `trsm` and `trsmRight` (4.5–8.2 GFLOP/s at
  256–1024), one column at a time.
- [x] `trmmT`: four columns at a time, which share the reads of `A`, each with its dot products in
  their order. About 2–3× locally (6–8 GFLOP/s at 256–1024, near `trsm`).
- [x] `symm`: four columns of `B` and `C` at a time, which share the reads of `A`, each element with
  its operations in their order. About 1.1–1.4× locally (6.2–7.7 GFLOP/s at 256–1024, from
  5.4–6.1).
- [ ] `symm`: check the four-column pass at power-of-two leading dimensions on several CPUs. It
  streams nine columns at once, and on one AMD EPYC 9V74 run (8-way L1) it ran at 2.8 GFLOP/s at
  512 and 1024, against 5.9 at 256. Three columns (seven streams) would stay within 8 ways.
- [ ] `symmRight`: four added columns of `B` per pass over the rows of a column of `C`, as `gemv`
  adds four columns. Each element keeps its order of operations. It runs at 5.4–7.8 GFLOP/s at
  256–1024, one column at a time.
- [ ] `syr2k`: two columns at a time, as `syrk` does, with each column's skipped terms kept. It runs
  at 5.2–7.3 GFLOP/s at 256–1024, one column at a time.
- [ ] `trsm`, `trsmRight`: update the rest of `B` by the `gemm` kernel after each block of solved
  rows or columns. This changes the order of the updates of an element only if the blocks reorder
  its terms, so it needs care to stay exact.

## `iamax` (1.6–1.9× behind, 2.4× in `Float32`)

- [ ] Find the largest `|x[i]|` with several independent running maxima, then the first index that
  holds it: 4× faster on typical data, 1.6× in the worst case, with the same result. Proving it
  needs order lemmas on `Float` that core doesn't have yet: `<` is a strict total order on
  non-`NaN` floats, no comparison with `NaN` is true, and `|x|` is `NaN` only when `x` is. Propose
  them to core, for `Float` and `Float32`.

## Complex Level 1

Measured at 1M elements on the cloud Xeon against the Netlib BLAS 3.12.0 (gfortran `-O2`), in ns per
element. The products of libgcc (`mul`, with the recovery of infinities when both parts are `NaN`)
cost `dotc` and `dotu` about 1.1× (1.4 against 1.3, by a pass with textbook products and a flag,
redone with `mul` when the flag drops), `scal` 1.15× and `rot` 1.7× (8 against 4.7). `nrm2`,
`copy` and `asum` are at parity or faster.

- [ ] `iamax` is 2.2× behind (2.9 against 1.3 ns). The loop is tight; the extra cost is likely the
  finiteness tests of both parts before the sum. Try a loop specialized for the unscaled case, or
  the independent running maxima above.
- [ ] `rot` updates `x` in a copy of its array, so that the old `x` is left for the update of `y`;
  one pass over both arrays, with a loop on two arrays of four parts per step, would not copy.
- [ ] `scal`, `axpy` and the `axpy` of the columns of Level 2 test for the recovery twice per
  element, once per part; one test per element, or a pass with a flag as in `dotc`, would be
  faster.
- [ ] `copy` of contiguous vectors could copy the whole range at once.

## Complex Level 2

At 512 on the cloud Xeon, `gemv`, `gemvT`, `gemvC` and `geru` run at 5.6–6.8 GFLOP/s, against
5.5–6.2 for the Netlib BLAS. They take one column of `A` per pass; several columns per pass, as the
real `gemv` does, would read and write `y` less often.

`hemv`, `her` and `her2` run at 0.5–0.7× the speed of the Netlib BLAS at 512 (2.4–3.9 against
4.9–6.4 GFLOP/s), with the products of libgcc.

`trmv`, `trmvT`, `trmvC`, `trsv`, `trsvT` and `trsvC` run at 3.2–3.7 GFLOP/s at 512, against
3.4–5.2 for the Netlib BLAS (0.7–1.0×), one column per step.

- [ ] Triangular: several columns per step, as the real `trsvT` and `trmvT` take four rows per pass,
  with each element's terms in their order.
- [ ] `hemv` makes two passes over each column, the `axpy` into `y` and the dot product with `x`,
  where the reference makes one; fusing them, with each sum in its order, would read the column
  once.
- [ ] `her2` makes two passes over each column, one for the `x` term and one for the `y` term; one
  pass with both terms, in the same order, would read and write the column once.

## Complex Level 3

`gemm` and its variants run at 0.5–0.95× the speed of the Netlib BLAS on the cloud Xeon: at 512,
3.1–4.2 GFLOP/s against 4.4–5.7 for `gemm`, `gemmNT`, `gemmNC`, `gemmTN` and `gemmCN`, and 1.5
against 2.5–2.9 for the four with both factors transposed. They run the loops of `zgemm`: one
`axpy` per column of `A` and column of `C`, or one dot product per element of `C`.

- [ ] `gemm` (`A` as it is): two columns of `C` per sweep of the rows, as the real `gemm` does,
  with each element's terms in their order.
- [ ] `gemmTT`, `gemmTC`, `gemmCT` and `gemmCC` read the rows of `B` with the stride `ld`; copying
  each row of `B` into a contiguous vector first, as the real `gemmTT` copies `B`, would keep the
  order of the products.

`hemm`, `hemmRight`, `herk`, `herkC`, `her2k` and `her2kC` run at 0.55–0.9× the speed of the
Netlib BLAS at 512 on the cloud Xeon (3.2–4.2 GFLOP/s against 3.6–6.1).

- [ ] `her2k` makes two passes over each column per term, one for `A` and one for `B`, and
  `her2kC` two sums per element; one pass with both, in the same order, would read `C`, or the
  columns of `A` and `B`, once (0.55× now).
- [ ] `hemm` makes one pass per row for the update of the column and one for the dot product, where
  the reference makes one.

`symm`, `symmRight`, `syrk`, `syrkT`, `syr2k` and `syr2kT` run at 0.45–0.85× the speed of the
Netlib BLAS at 512 on the cloud Xeon (2.8–4.3 GFLOP/s against 4.5–6.4), with the same loops as
their Hermitian counterparts.

- [ ] `symm` (0.5×) and `syr2k` have the same two passes as `hemm` and `her2k`; the same fusions
  would apply.

`trmm` and its variants run at 0.45–0.85× the speed of the Netlib BLAS at 512 on the cloud Xeon
(2.0–4.1 GFLOP/s against 3.9–6.4): 0.45–0.65× for `trmm` (`A` as it is), and 0.7–0.85× for the
others.

- [ ] `trmm` writes the diagonal element of each step with a write of its own, after the `axpy`
  of the column; folding it into the same pass, or several rows per pass, as the real `trmm` does,
  would read and write the column less often.

## Level 2 (0.9–1.3× at 1024 and 2048, 1.2–1.8× at 256)

- [x] `trmvT`: four elements per pass, which share the reads of `x`, each with its terms in their
  order (the terms of the four elements' own rows first). At the speed of `trsv` locally
  (5–6.5 GFLOP/s at 256–2048, from 3–3.7).
- [x] `trsvT`: four elements per pass, as `gemvT` computes four dot products, with each element's
  terms in their order: the four share the solved range, then finish their 4 × 4 triangle. About
  1.5–2× locally (5–6.3 GFLOP/s at 256–2048, near `trsv`, from 3.2–4.5).

- [x] `symv`: four columns per sweep, each `y[i]` with the four column terms in column order and
  four dot products, then the 4 × 4 block in the order of the reference. About 1.65× locally
  (8.7–10 GFLOP/s at 256–2048, from 5.1–6.2).

- [ ] `trsv`: update the rest of `x` four columns at a time after each block of four solved
  elements, as `gemv` does. Each element keeps its order of operations. Not measured yet.
- [ ] `gemv` with strided `x` and `y` is 1.05–3× behind, and 2.4–7.4× behind in `Float32`, where
  Netlib is also up to 6% faster at 256 and 1024. Not investigated yet.
- [ ] The band routines `gbmv`, `gbmvT`, `sbmv`, `tbmv`, `tbmvT`, `tbsv` and `tbsvT` are not
  benchmarked yet, against `scripts/cblas_bench.c` or otherwise. They run the loops of the reference
  BLAS one column at a time; `gbmv` and `sbmv` could take two or four columns per pass, as `gemv`
  does, with each element's terms in their order.
- [ ] The packed routines `spmv`, `spr`, `spr2`, `tpmv`, `tpmvT`, `tpsv` and `tpsvT` are not
  benchmarked yet either. They run the loops of the reference BLAS one column at a time, with the
  packed index computed per element; `spmv` could take two columns per pass, as `symv` does.
- [ ] `gemvT` at 256 is 1.8× behind, and 4.5× in `Float32`, against 1.0–1.1× (1.6–1.7× in
  `Float32`) at 1024 and 2048. Not investigated yet.

## Build

- [ ] An opt-in Lake option for `-march=native`, which gives 10–30% on Level 2 and `gemm` and
  nothing on Level 1, but makes binaries that only run on CPUs like the one that built them. The
  tests pass with it, since `-ffp-contract=off` stays on.
