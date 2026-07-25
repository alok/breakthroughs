#!/usr/bin/env python3
"""Decode a kissat model for the twisted J(2k,k) instance into a full coloring.

Usage: decode.py <k> <kissat_output_file> <coloring_out.json>

Rebuilds orbits deterministically (same code path as gen.py), reads the model,
extracts base colors, expands to all C(2k,k) vertices, verifies:
  (a) exactly one color per orbit variable block,
  (b) the twist property color(sigma(A)) = color(A) + 1 (mod p) for ALL vertices,
  (c) EVERY edge of J(2k,k) is properly colored (direct enumeration),
then writes JSON {"n":, "k":, "coloring": {mask_str: color}}.
"""
from __future__ import annotations

import json
import sys

from gen import build


def main() -> None:
    k = int(sys.argv[1])
    model_path = sys.argv[2]
    out_path = sys.argv[3]
    n, p, sig, masks, orb, reps, triples, same = build(k)

    lits: set[int] = set()
    sat = False
    with open(model_path) as f:
        for line in f:
            if line.startswith("s "):
                sat = "SATISFIABLE" in line and "UNSAT" not in line
            if line.startswith("v "):
                for tok in line.split()[1:]:
                    v = int(tok)
                    if v > 0:
                        lits.add(v)
    assert sat, "model file does not contain s SATISFIABLE"

    x: list[int] = []
    for o in range(len(reps)):
        cs = [c for c in range(p) if (o * p + c + 1) in lits]
        assert len(cs) == 1, f"orbit {o}: not exactly one color true: {cs}"
        x.append(cs[0])

    col: dict[int, int] = {}
    for o, R in enumerate(reps):
        m = R
        for t in range(p):
            col[m] = (x[o] + t) % p
            m = sig(m)
    assert len(col) == len(masks)

    # twist property
    for A in masks:
        assert col[sig(A)] == (col[A] + 1) % p
    print("twist property verified on all vertices")

    # full direct edge check
    bad = 0
    checked = 0
    for A in masks:
        ca = col[A]
        for i in range(n):
            if not ((A >> i) & 1):
                continue
            Am = A ^ (1 << i)
            for j in range(n):
                if (A >> j) & 1:
                    continue
                B = Am | (1 << j)
                if B > A:
                    checked += 1
                    if col[B] == ca:
                        bad += 1
    print(f"direct edge check: {checked} edges, {bad} monochromatic")
    assert bad == 0

    with open(out_path, "w") as f:
        json.dump({"n": n, "k": k, "base_colors": x,
                   "coloring": {str(m): c for m, c in col.items()}}, f)
    print(f"wrote {out_path} ({len(col)} vertices)")


if __name__ == "__main__":
    main()
