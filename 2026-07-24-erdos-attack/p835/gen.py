#!/usr/bin/env python3
"""
Erdos problem #835 (Erdos-Rosenfeld): chromatic number of Johnson graph J(2k,k).

Equivariant SAT encoding with a C_p regular twist, p = k+1 prime.
Colors = Z/p. sigma = p-cycle (0 1 ... p-1) on elements {0..p-1} of
[n] = {0..n-1} (n = 2k), fixing elements p..n-1.

Ansatz: color(sigma(A)) = color(A) + 1 (mod p).

No k-subset is sigma-invariant (its intersection with the p-cycle support must be
sigma-invariant, hence empty or all p elements; empty forces the subset inside the
(k-1)-element fixed part -- too small; all p is too big).  Since p is prime, every
orbit has size exactly p (asserted below).  One base color x_o in Z/p per orbit,
attached to the canonical representative rep_o (numerically smallest bitmask):

    color(sigma^t(rep_o)) = (x_o + t) mod p.

Edge {A,B} of J(2k,k) (|A cap B| = k-1): A = sigma^a(rep_{o1}), B = sigma^b(rep_{o2}).
 - o1 == o2: proper iff a != b (mod p); always true for an edge (b != a since A != B
   and orbit size p).  Asserted, then skipped (constraint is vacuous).
 - o1 != o2: proper iff x_{o1} + a != x_{o2} + b (mod p),
             i.e.  x_{o1} - x_{o2} != (b - a)  (mod p).
Normalized triple (u, v, d) with u < v means: constraint  x_u - x_v != d (mod p).
Enumerating each edge shifted so one endpoint is a rep (a = 0) covers every
edge-orbit; shifting to either endpoint yields the SAME normalized triple.

CNF: one-hot vars var(o,c) = o*p + c + 1.
Per orbit: ALO clause + pairwise AMO.
Triple (u,v,d): for c in 0..p-1: clause (-var(u,c) OR -var(v, (c-d) mod p))
  [forbids exactly x_u = c and x_v = c - d, i.e. x_u - x_v = d].
"""
from __future__ import annotations

import json
import random
import sys
from itertools import combinations
from math import comb
from typing import Callable


def make_sigma(p: int) -> Callable[[int], int]:
    cyc = (1 << p) - 1

    def sig(m: int) -> int:
        c = m & cyc
        return (((c << 1) | (c >> (p - 1))) & cyc) | (m & ~cyc)

    return sig


def build(k: int):
    n = 2 * k
    p = k + 1
    sig = make_sigma(p)

    masks: list[int] = []
    for cmb in combinations(range(n), k):
        m = 0
        for e in cmb:
            m |= 1 << e
        masks.append(m)
    masks.sort()
    assert len(masks) == comb(n, k)

    orb: dict[int, tuple[int, int]] = {}
    reps: list[int] = []
    for m0 in masks:
        if m0 in orb:
            continue
        oid = len(reps)
        reps.append(m0)
        m = m0
        for t in range(p):
            assert m not in orb, "orbit shorter than p (invariant subset?!)"
            orb[m] = (oid, t)
            m = sig(m)
        assert m == m0, "orbit does not close after p steps"
    assert len(reps) * p == len(masks), "orbit count mismatch"

    triples: set[tuple[int, int, int]] = set()
    same_orbit_incidences = 0
    full = (1 << n) - 1
    for o1, R in enumerate(reps):
        ins = [i for i in range(n) if (R >> i) & 1]
        outs = [j for j in range(n) if not ((R >> j) & 1)]
        for i in ins:
            Rm = R ^ (1 << i)
            for j in outs:
                B = Rm | (1 << j)
                o2, b = orb[B]
                if o2 == o1:
                    assert b % p != 0, "same-orbit edge with delta == 0 (impossible)"
                    same_orbit_incidences += 1
                    continue
                if o1 < o2:
                    triples.add((o1, o2, b % p))
                else:
                    triples.add((o2, o1, (-b) % p))

    return n, p, sig, masks, orb, reps, sorted(triples), same_orbit_incidences


def write_cnf(path: str, norb: int, p: int, triples: list[tuple[int, int, int]],
              symbreak: bool) -> tuple[int, int]:
    nvars = norb * p
    nclauses = norb + norb * p * (p - 1) // 2 + len(triples) * p + (1 if symbreak else 0)
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {nclauses}\n")
        lines: list[str] = []
        if symbreak:
            lines.append("1 0")  # x_0 = 0 (global color shift symmetry)
        for o in range(norb):
            base = o * p
            lines.append(" ".join(str(base + c + 1) for c in range(p)) + " 0")
            for c1 in range(p):
                for c2 in range(c1 + 1, p):
                    lines.append(f"-{base + c1 + 1} -{base + c2 + 1} 0")
            if len(lines) > 1_000_000:
                f.write("\n".join(lines) + "\n")
                lines = []
        for (u, v, d) in triples:
            bu = u * p
            bv = v * p
            for c in range(p):
                lines.append(f"-{bu + c + 1} -{bv + ((c - d) % p) + 1} 0")
            if len(lines) > 1_000_000:
                f.write("\n".join(lines) + "\n")
                lines = []
        if lines:
            f.write("\n".join(lines) + "\n")
    return nvars, nclauses


# ---------- calibration helpers ----------

def expand(x: list[int], reps: list[int], sig, p: int) -> dict[int, int]:
    col: dict[int, int] = {}
    for o, R in enumerate(reps):
        m = R
        for t in range(p):
            col[m] = (x[o] + t) % p
            m = sig(m)
    return col


def is_proper(col: dict[int, int], masks: list[int], n: int) -> bool:
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
                if B > A and col[B] == ca:
                    return False
    return True


def triples_ok(x: list[int], triples: list[tuple[int, int, int]], p: int) -> bool:
    for (u, v, d) in triples:
        if (x[u] - x[v] - d) % p == 0:
            return False
    return True


def dfs_solutions(norb: int, p: int, triples: list[tuple[int, int, int]],
                  count_all: bool) -> tuple[int, list[int] | None]:
    """Exhaustive DFS over base-color assignments with forward pruning.
    Constraint (u,v,d), u<v:  x_v != x_u - d."""
    cons: list[list[tuple[int, int]]] = [[] for _ in range(norb)]
    for (u, v, d) in triples:
        cons[v].append((u, d))
    x = [0] * norb
    count = 0
    witness: list[int] | None = None

    def rec(v: int) -> bool:
        nonlocal count, witness
        if v == norb:
            count += 1
            if witness is None:
                witness = x.copy()
            return not count_all
        forbidden = {(x[u] - d) % p for (u, d) in cons[v]}
        for c in range(p):
            if c in forbidden:
                continue
            x[v] = c
            if rec(v + 1):
                return True
        return False

    rec(0)
    return count, witness


def calibrate() -> None:
    rng = random.Random(835)

    # ---- k = 2, p = 3: J(4,2), chi = 3 = k+1 known -> MUST be satisfiable ----
    n, p, sig, masks, orb, reps, triples, same = build(2)
    print(f"[k=2] n={n} p={p} orbits={len(reps)} triples={triples} same_orbit_inc={same}")
    assert len(reps) == 2
    good_direct = set()
    good_triples = set()
    for x0 in range(p):
        for x1 in range(p):
            x = [x0, x1]
            d_ok = is_proper(expand(x, reps, sig, p), masks, n)
            t_ok = triples_ok(x, triples, p)
            assert d_ok == t_ok, f"encoding mismatch at x={x}: direct={d_ok} triples={t_ok}"
            if d_ok:
                good_direct.add((x0, x1))
            if t_ok:
                good_triples.add((x0, x1))
    assert good_direct == good_triples
    assert len(good_direct) > 0, "k=2 must admit a twisted 3-coloring"
    print(f"[k=2] EXHAUSTIVE equivalence over all {p**2} assignments OK; "
          f"proper twisted colorings: {sorted(good_direct)}")
    cnt, wit = dfs_solutions(len(reps), p, triples, count_all=True)
    print(f"[k=2] DFS solution count = {cnt} (expect {len(good_direct)}), witness = {wit}")
    assert cnt == len(good_direct)

    # decode witness into a full coloring and print it
    col = expand(wit, reps, sig, p)
    assert is_proper(col, masks, n)
    pretty = {tuple(i + 1 for i in range(n) if (m >> i) & 1): c for m, c in sorted(col.items())}
    print(f"[k=2] decoded proper 3-coloring of J(4,2): {pretty}")

    # ---- k = 4, p = 5: J(8,4), known chi > 5 -> MUST be unsatisfiable ----
    n, p, sig, masks, orb, reps, triples, same = build(4)
    print(f"[k=4] n={n} p={p} orbits={len(reps)} #triples={len(triples)} same_orbit_inc={same}")
    assert len(reps) == 14
    # random-sample equivalence of encoding vs direct properness
    for _ in range(20000):
        x = [rng.randrange(p) for _ in range(len(reps))]
        assert triples_ok(x, triples, p) == is_proper(expand(x, reps, sig, p), masks, n)
    print("[k=4] sampled equivalence (20000 random assignments) OK")
    cnt, wit = dfs_solutions(len(reps), p, triples, count_all=True)
    print(f"[k=4] DFS exhaustive count of twisted 5-colorings = {cnt} (expect 0)")
    assert cnt == 0


def generate(k: int, symbreak: bool) -> None:
    base = f"j{2*k}_{k}"
    n, p, sig, masks, orb, reps, triples, same = build(k)
    nvars, ncls = write_cnf(f"{base}.cnf", len(reps), p, triples, symbreak)
    with open(f"{base}_meta.json", "w") as f:
        json.dump({"k": k, "n": n, "p": p, "norb": len(reps), "reps": reps,
                   "num_triples": len(triples), "same_orbit_incidences": same,
                   "symbreak": symbreak, "nvars": nvars, "nclauses": ncls}, f)
    with open(f"{base}_triples.txt", "w") as f:
        f.write("\n".join(f"{u} {v} {d}" for (u, v, d) in triples) + "\n")
    # delta histogram for the record
    hist = [0] * p
    for (_, _, d) in triples:
        hist[d] += 1
    print(f"[k={k}] n={n} p={p} vertices={len(masks)} orbits={len(reps)} "
          f"triples={len(triples)} same_orbit_incidences={same}")
    print(f"[k={k}] CNF: {nvars} vars, {ncls} clauses, symbreak={symbreak} -> {base}.cnf")
    print(f"[k={k}] delta histogram: {hist}")


if __name__ == "__main__":
    if sys.argv[1] == "calibrate":
        calibrate()
    else:
        k = int(sys.argv[1])
        symbreak = "--symbreak" in sys.argv
        generate(k, symbreak)
