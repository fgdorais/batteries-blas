/*
 * Copyright © 2026 François G. Dorais. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 *
 * Times a C BLAS on the benchmarks of `lake exe bench`, for comparison. It is not part of the
 * library, which has no C dependency.
 *
 * It loads the CBLAS interface from a shared library at run time, so the same binary times any
 * implementation, for example OpenBLAS and Netlib's reference BLAS:
 *
 *   cc -O2 -o cblas_bench scripts/cblas_bench.c -ldl
 *   ./cblas_bench /usr/lib/x86_64-linux-gnu/blas/libblas.so.3 [size] [rounds]
 *
 * It times the double-precision routines, `ddot` and so on, or the single-precision ones, `sdot`
 * and so on, when compiled with `-DSINGLE`, to compare with `lake exe bench --float32`.
 *
 * It prints `name<TAB>milliseconds` lines, with the names, inputs, repetitions and sizes of
 * `lake exe bench --tsv`, and each time is the fastest of `rounds` runs. `scripts/blas_compare.py`
 * puts the two side by side.
 */
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* The CBLAS enums, with the values of the reference `cblas.h`. */
enum { RowMajor = 101, ColMajor = 102 };
enum { NoTrans = 111, Trans = 112 };
enum { Upper = 121, Lower = 122 };
enum { NonUnit = 131 };
enum { Left = 141, Right = 142 };

/* The precision: `double` by default, `float` with `-DSINGLE`. */
#ifdef SINGLE
typedef float real;
#define CBLAS(name) "cblas_s" name
#define CBLAS_I(name) "cblas_is" name
#else
typedef double real;
#define CBLAS(name) "cblas_d" name
#define CBLAS_I(name) "cblas_id" name
#endif

/* The routines, named after their double-precision versions. */
static real (*ddot)(int, const real *, int, const real *, int);
static void (*daxpy)(int, real, const real *, int, real *, int);
static void (*dcopy)(int, const real *, int, real *, int);
static real (*dnrm2)(int, const real *, int);
static size_t (*idamax)(int, const real *, int);
static void (*dgemv)(int, int, int, int, real, const real *, int, const real *, int,
                     real, real *, int);
static void (*dger)(int, int, int, real, const real *, int, const real *, int, real *,
                    int);
static void (*dtrsv)(int, int, int, int, int, const real *, int, real *, int);
static void (*dgemm)(int, int, int, int, int, int, real, const real *, int, const real *,
                     int, real, real *, int);
static void (*dsyrk)(int, int, int, int, int, real, const real *, int, real, real *, int);
static void (*dtrsm)(int, int, int, int, int, int, int, real, const real *, int, real *, int);
static void (*dsymv)(int, int, int, real, const real *, int, const real *, int, real, real *,
                     int);
static void (*dsyr2)(int, int, int, real, const real *, int, const real *, int, real *, int);
static void (*dtrmm)(int, int, int, int, int, int, int, real, const real *, int, real *, int);
static void (*dsymm)(int, int, int, int, int, real, const real *, int, const real *, int, real,
                     real *, int);
static void (*dsyr2k)(int, int, int, int, int, real, const real *, int, const real *, int, real,
                      real *, int);
/* Not in Netlib's BLAS 3.12: `NULL` when the library has neither `gemmtr` nor OpenBLAS's
   `gemmt`. */
static void (*dgemmtr)(int, int, int, int, int, int, real, const real *, int, const real *, int,
                       real, real *, int);

static void *sym(void *lib, const char *name) {
  void *p = dlsym(lib, name);
  if (!p) {
    fprintf(stderr, "missing %s\n", name);
    exit(1);
  }
  return p;
}

static int rounds = 10;
static const int reps = 10;
/* Keeps the results live. */
static volatile double sink;

static uint64_t now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

/* Prints the fastest of `rounds` runs of `f`, in milliseconds. */
static void time_it(const char *name, double (*f)(void *), void *env) {
  uint64_t best = UINT64_MAX;
  for (int r = 0; r < rounds; r++) {
    uint64_t t0 = now();
    sink += f(env);
    uint64_t t1 = now();
    if (t1 - t0 < best) best = t1 - t0;
  }
  printf("%s\t%.3f\n", name, best / 1e6);
}

/* The inputs of `lake exe bench`. */
static real *vec(size_t n) {
  real *x = malloc(n * sizeof(real));
  for (size_t i = 0; i < n; i++) x[i] = (real)(i % 7) - 3;
  return x;
}

static real *mat(int m, int s) {
  real *a = malloc((size_t)m * m * sizeof(real));
  for (int j = 0; j < m; j++)
    for (int i = 0; i < m; i++) a[i + (size_t)m * j] = (real)((i * 7 + j * 13 + s) % 11) - 5;
  return a;
}

/* What a benchmark works on: `x` is read, `z` and `w` are scratch copies, `inc` is the stride. */
typedef struct {
  int n, inc;
  real *x, *z, *w;
} L1;

/* The updates copy their input first, as the first update of `lake exe bench` does. */
static double b_axpy(void *e) {
  L1 *v = e;
  dcopy(v->n, v->x, v->inc, v->z, v->inc);
  for (int k = 0; k < reps; k++) daxpy(v->n, 0.5, v->x, v->inc, v->z, v->inc);
  return v->z[0];
}
static double b_dot(void *e) {
  L1 *v = e;
  return ddot(v->n, v->x, v->inc, v->x, v->inc);
}
static double b_nrm2(void *e) {
  L1 *v = e;
  return dnrm2(v->n, v->x, 1);
}
static double b_iamax(void *e) {
  L1 *v = e;
  return (double)idamax(v->n, v->x, 1);
}

/* `b` holds the triangular matrix once the general benchmarks are done, and `c` is scratch. */
typedef struct {
  int m, inc;
  real *a, *x, *y, *b, *c;
} L2;

static double b_gemv(void *e) {
  L2 *v = e;
  int m = v->m;
  dcopy(m, v->x, v->inc, v->y, v->inc);
  for (int k = 0; k < reps; k++)
    dgemv(ColMajor, NoTrans, m, m, 1.5, v->a, m, v->x, v->inc, 0.5, v->y, v->inc);
  return v->y[0];
}
static double b_gemvT(void *e) {
  L2 *v = e;
  int m = v->m;
  dcopy(m, v->x, 1, v->y, 1);
  for (int k = 0; k < reps; k++)
    dgemv(ColMajor, Trans, m, m, 1.5, v->a, m, v->x, 1, 0.5, v->y, 1);
  return v->y[0];
}
static double b_ger(void *e) {
  L2 *v = e;
  int m = v->m;
  memcpy(v->b, v->a, (size_t)m * m * sizeof(real));
  for (int k = 0; k < reps; k++) dger(ColMajor, m, m, 1.5, v->x, 1, v->x, 1, v->b, m);
  return v->b[0];
}
static double trsv(L2 *v, int trans) {
  int m = v->m;
  for (int i = 0; i < m; i++) v->y[i] = 1.5 * v->x[i];
  for (int k = 0; k < reps; k++) dtrsv(ColMajor, Lower, trans, NonUnit, m, v->b, m, v->y, 1);
  return v->y[0];
}
static double b_trsvL(void *e) { return trsv(e, NoTrans); }
static double b_trsvTL(void *e) { return trsv(e, Trans); }
/* `symv` reads the triangular matrix as symmetric, as `lake exe bench` does. */
static double b_symvL(void *e) {
  L2 *v = e;
  int m = v->m;
  dcopy(m, v->x, 1, v->y, 1);
  for (int k = 0; k < reps; k++)
    dsymv(ColMajor, Lower, m, 1.5, v->b, m, v->x, 1, 0.5, v->y, 1);
  return v->y[0];
}
static double b_syr2(void *e) {
  L2 *v = e;
  int m = v->m;
  memcpy(v->c, v->a, (size_t)m * m * sizeof(real));
  for (int k = 0; k < reps; k++) dsyr2(ColMajor, Upper, m, 1.5, v->x, 1, v->x, 1, v->c, m);
  return v->c[0];
}

/* For `gemm`, `a`, `b` and `c` are `A`, `B` and `C`; for the others, `b` is the triangular matrix
   and `d` is the second matrix of `syr2k`. `ld` is the leading dimension, and `z` is scratch. */
typedef struct {
  int m, ld;
  real *a, *b, *c, *z, *d;
} L3;

/* `gemm` of `lake exe bench` returns a new matrix, so this one writes into a copy of `C`. */
static double b_gemm(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dgemm(ColMajor, NoTrans, NoTrans, m, m, m, 1.5, v->a, m, v->b, m, 0.5, v->z, m);
  return v->z[0];
}
static double b_gemmTN(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dgemm(ColMajor, Trans, NoTrans, m, m, m, 1.5, v->a, m, v->b, m, 0.5, v->z, m);
  return v->z[0];
}
static double b_gemmtr(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dgemmtr(ColMajor, Lower, NoTrans, NoTrans, m, m, 1.5, v->a, m, v->b, m, 0.5, v->z, m);
  return v->z[0];
}

/* As `gemm`, `syrk` and `trsm` write into a copy of `C`, or of `B`, which is `c`. */
static double b_syrk(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dsyrk(ColMajor, Lower, NoTrans, m, m, 1.5, v->a, m, 0.5, v->z, m);
  return v->z[0];
}
static double b_syrkT(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dsyrk(ColMajor, Lower, Trans, m, m, 1.5, v->a, m, 0.5, v->z, m);
  return v->z[0];
}
/* `b` holds the triangular matrix. */
static double tri3(L3 *v, int side, int uplo, int trans, int solve) {
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  if (solve) dtrsm(ColMajor, side, uplo, trans, NonUnit, m, m, 1.5, v->b, m, v->z, m);
  else dtrmm(ColMajor, side, uplo, trans, NonUnit, m, m, 1.5, v->b, m, v->z, m);
  return v->z[0];
}
static double b_trsmL(void *e) { return tri3(e, Left, Lower, NoTrans, 1); }
static double b_trsmR(void *e) { return tri3(e, Right, Upper, NoTrans, 1); }
static double b_trsmTL(void *e) { return tri3(e, Left, Lower, Trans, 1); }
static double b_trmmL(void *e) { return tri3(e, Left, Lower, NoTrans, 0); }
/* `symm` reads the triangular matrix as symmetric, as `lake exe bench` does. */
static double b_symmL(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dsymm(ColMajor, Left, Lower, m, m, 1.5, v->b, m, v->a, m, 0.5, v->z, m);
  return v->z[0];
}
static double b_syr2k(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(real));
  dsyr2k(ColMajor, Lower, NoTrans, m, m, 1.5, v->a, m, v->d, m, 0.5, v->z, m);
  return v->z[0];
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s libblas.so [size] [rounds]\n", argv[0]);
    return 1;
  }
  void *lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
  if (!lib) {
    fprintf(stderr, "%s\n", dlerror());
    return 1;
  }
  int n = argc > 2 ? atoi(argv[2]) : 1000000;
  if (argc > 3) rounds = atoi(argv[3]);
  ddot = sym(lib, CBLAS("dot"));
  daxpy = sym(lib, CBLAS("axpy"));
  dcopy = sym(lib, CBLAS("copy"));
  dnrm2 = sym(lib, CBLAS("nrm2"));
  idamax = sym(lib, CBLAS_I("amax"));
  dgemv = sym(lib, CBLAS("gemv"));
  dger = sym(lib, CBLAS("ger"));
  dtrsv = sym(lib, CBLAS("trsv"));
  dgemm = sym(lib, CBLAS("gemm"));
  dsyrk = sym(lib, CBLAS("syrk"));
  dtrsm = sym(lib, CBLAS("trsm"));
  dsymv = sym(lib, CBLAS("symv"));
  dsyr2 = sym(lib, CBLAS("syr2"));
  dtrmm = sym(lib, CBLAS("trmm"));
  dsymm = sym(lib, CBLAS("symm"));
  dsyr2k = sym(lib, CBLAS("syr2k"));
  dgemmtr = dlsym(lib, CBLAS("gemmtr"));
  if (!dgemmtr) dgemmtr = dlsym(lib, CBLAS("gemmt"));

  char name[64];
  L1 v = {n, 1, vec(n), vec(n), vec(n)};
  snprintf(name, sizeof name, "axpy ×%d", reps);
  time_it(name, b_axpy, &v);
  time_it("dot", b_dot, &v);
  time_it("nrm2", b_nrm2, &v);
  time_it("iamax", b_iamax, &v);
  L1 v2 = {n, 2, vec(2 * (size_t)n), vec(2 * (size_t)n), NULL};
  snprintf(name, sizeof name, "axpy ×%d, stride 2 / stride 1", reps);
  time_it(name, b_axpy, &v2);

  /* The sizes of `lake exe bench`. */
  {
    int m = 512;
    L2 w = {m, 1, mat(m, 1), vec(m), vec(2 * (size_t)m), mat(m, 1), mat(m, 1)};
    snprintf(name, sizeof name, "gemv %d ×%d", m, reps);
    time_it(name, b_gemv, &w);
    snprintf(name, sizeof name, "gemvT %d ×%d", m, reps);
    time_it(name, b_gemvT, &w);
    snprintf(name, sizeof name, "ger %d ×%d", m, reps);
    time_it(name, b_ger, &w);
    for (int j = 0; j < m; j++)
      for (int i = 0; i < m; i++)
        w.b[i + (size_t)m * j] = i == j ? m + 4 + i : (real)((i * 7 + j * 13) % 11) - 5;
    struct { const char *name; double (*f)(void *); } more[] = {
      {"trsv lower %d ×%d", b_trsvL}, {"trsvT lower %d ×%d / trsv", b_trsvTL},
      {"symv lower %d ×%d / gemv", b_symvL}, {"syr2 upper %d ×%d / ger", b_syr2}};
    for (size_t i = 0; i < sizeof more / sizeof more[0]; i++) {
      snprintf(name, sizeof name, more[i].name, m, reps);
      time_it(name, more[i].f, &w);
    }
  }

  int l3[] = {512, 1024};
  for (int s = 0; s < 2; s++) {
    int m = l3[s];
    L3 g = {m, m, mat(m, 1), mat(m, 2), mat(m, 3), mat(m, 3), NULL};
    snprintf(name, sizeof name, "gemm %d", m);
    time_it(name, b_gemm, &g);
    snprintf(name, sizeof name, "gemmTN %d / gemm", m);
    time_it(name, b_gemmTN, &g);
    if (dgemmtr) {
      snprintf(name, sizeof name, "gemmtr lower %d, half the operations / gemm", m);
      time_it(name, b_gemmtr, &g);
    }
  }

  {
    int m = 512;
    L3 g = {m, m, mat(m, 1), mat(m, 1), mat(m, 3), mat(m, 3), mat(m, 2)};
    for (int j = 0; j < m; j++)
      for (int i = 0; i < m; i++)
        g.b[i + (size_t)m * j] = i == j ? m + 4 + i : (real)((i * 7 + j * 13) % 11) - 5;
    struct { const char *name; double (*f)(void *); } more[] = {
      {"syrk lower %d", b_syrk}, {"syrkT lower %d", b_syrkT}, {"trsm lower %d", b_trsmL},
      {"trsmRight upper %d", b_trsmR}, {"trsmT lower %d / trsm", b_trsmTL},
      {"trmm lower %d / trsm", b_trmmL}, {"symm lower %d, 2 m³ operations", b_symmL},
      {"syr2k lower %d, 2 m³ operations / syrk", b_syr2k}};
    for (size_t i = 0; i < sizeof more / sizeof more[0]; i++) {
      snprintf(name, sizeof name, more[i].name, m);
      time_it(name, more[i].f, &g);
    }
  }
  return 0;
}
