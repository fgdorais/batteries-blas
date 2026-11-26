#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Compare `lake exe bench` with C BLAS implementations.

Usage: blas_compare.py LEAN.tsv NAME=OTHER.tsv...

LEAN.tsv holds the `lake exe bench --tsv` output, and each OTHER.tsv the `cblas_bench` output of
one implementation, which is labeled NAME. Each file may hold several runs, of which the fastest
time is kept. The table shows each time in milliseconds, or GFLOP/s where the operation count is
known, and the ratio of the implementation's speed to BatteriesBLAS's: 2.0 means it is twice as fast.
"""

import re
import sys


def load(path):
    times = {}
    order = []
    with open(path) as f:
        for line in f:
            name, _, ms = line.rstrip("\n").partition("\t")
            if not ms:
                continue
            if name not in times:
                order.append(name)
                times[name] = float(ms)
            else:
                times[name] = min(times[name], float(ms))
    return order, times


def flops(name):
    """The floating-point operations of a benchmark, if they are counted."""
    m = re.fullmatch(r"(\w+)(?: lower| upper)? (\d+) ×(\d+)(?: / \w+)?", name)
    if m and m.group(1) in ("gemv", "gemvT", "ger", "symv", "syr2"):
        return 2 * int(m.group(2)) ** 2 * int(m.group(3))
    if m and m.group(1) in ("trsv", "trsvT"):
        return int(m.group(2)) ** 2 * int(m.group(3))
    m = re.fullmatch(r"gemm(?:TN)? (\d+)(?: / gemm)?", name)
    if m:
        return 2 * int(m.group(1)) ** 3
    m = re.fullmatch(r"(\w+) (?:lower|upper) (\d+)(, 2 m³ operations|, half the operations)?"
                     r"(?: / \w+)?", name)
    if m and m.group(1) in ("syrk", "syrkT", "trsm", "trsmT", "trsmRight", "trmm", "symm", "syr2k",
                            "gemmtr"):
        return (2 if m.group(3) == ", 2 m³ operations" else 1) * int(m.group(2)) ** 3
    return None


def main():
    if len(sys.argv) < 3 or any("=" not in a for a in sys.argv[2:]):
        sys.exit(__doc__)
    order, lean = load(sys.argv[1])
    others = []
    for arg in sys.argv[2:]:
        label, _, path = arg.partition("=")
        others.append((label, load(path)[1]))
    cols = "".join(f" {label} | {label} / BLAS |" for label, _ in others)
    print(f"| Benchmark | Unit | BLAS |{cols}")
    print("|---|---|--:|" + "--:|--:|" * len(others))
    for name in order:
        if not any(name in t for _, t in others):
            continue
        f = flops(name)
        unit = "GFLOP/s" if f else "ms"

        def show(ms):
            return f"{f / (ms * 1e6):.2f}" if f else f"{ms:.3f}"

        row = f"| {name} | {unit} | {show(lean[name])} |"
        for _, t in others:
            if name in t:
                row += f" {show(t[name])} | {lean[name] / t[name]:.2f} |"
            else:
                row += " — | — |"
        print(row)


if __name__ == "__main__":
    main()
