#!/usr/bin/env python3
"""Verify and classify all NLC witnesses (n=26, 28, 29) with THREE independent
algorithms, then emit JSON censuses.

Algorithms:
  1. C DP (already produced the lines being checked)
  2. Python iterative leaf-up DP (phase2.indep_poly)
  3. NEW: vertex-deletion recursion I(G) = I(G-v) + x*I(G-N[v]) on raw edge
     sets with component splitting and memoization -- a completely different
     algorithm (no rooted DP, no parent arrays).
Also: structural classifier (strip P2-arms / identify KL shapes) and exact
LC-break data (positions, ratios as exact fractions).
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from functools import lru_cache

sys.path.insert(0, "/private/tmp/claude-502/-Users-alokbeniwal-breakthroughs/52a3fab3-ea00-484f-abaf-94fb7d0723cb/scratchpad/p993")
import phase2 as p

DIR = "/private/tmp/claude-502/-Users-alokbeniwal-breakthroughs/52a3fab3-ea00-484f-abaf-94fb7d0723cb/scratchpad/p993"


def polymul(a: list[int], b: list[int]) -> list[int]:
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def polyadd(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def indep_poly_deletion(edges: frozenset[frozenset[int]],
                        verts: frozenset[int]) -> list[int]:
    """Vertex-deletion recursion with component splitting. Exact ints."""
    @lru_cache(maxsize=None)
    def comps(vs: frozenset, es: frozenset) -> tuple:
        seen: set[int] = set()
        out = []
        adj: dict[int, set[int]] = {v: set() for v in vs}
        for e in es:
            a, b = tuple(e)
            adj[a].add(b)
            adj[b].add(a)
        for v in vs:
            if v in seen:
                continue
            stack, cv = [v], set()
            while stack:
                u = stack.pop()
                if u in cv:
                    continue
                cv.add(u)
                stack.extend(adj[u] - cv)
            seen |= cv
            ce = frozenset(e for e in es if e <= cv)
            out.append((frozenset(cv), ce))
        return tuple(out)

    @lru_cache(maxsize=None)
    def solve(vs: frozenset, es: frozenset) -> tuple:
        if not vs:
            return (1,)
        if not es:
            # k isolated vertices: (1+x)^k
            r = [1]
            for _ in range(len(vs)):
                r = polyadd(r, [0] + r[:])
                # (1+x)*r computed manually
            # simpler: binomials
            from math import comb
            k = len(vs)
            return tuple(comb(k, i) for i in range(k + 1))
        result = [1]
        for cv, ce in comps(vs, es):
            if not ce:
                from math import comb
                k = len(cv)
                cpoly = [comb(k, i) for i in range(k + 1)]
            else:
                # pick max-degree vertex in this component
                deg: dict[int, int] = {}
                for e in ce:
                    for u in e:
                        deg[u] = deg.get(u, 0) + 1
                v = max(deg, key=lambda u: (deg[u], u))
                nb = set()
                for e in ce:
                    if v in e:
                        nb |= set(e)
                # G - v
                vs1 = cv - {v}
                es1 = frozenset(e for e in ce if v not in e)
                # G - N[v]
                vs2 = cv - nb
                es2 = frozenset(e for e in ce if not (e & nb))
                p1 = list(solve(vs1, es1))
                p2 = list(solve(vs2, es2))
                cpoly = polyadd(p1, [0] + p2)
            result = polymul(result, cpoly)
        return tuple(result)

    return list(solve(verts, edges))


def strip_P2_arms(par: list[int], n: int) -> dict:
    """Classify: count pendant P2-arms (path of 2) per attachment vertex,
    pendant leaves, and longer pendant paths; return reduced description."""
    children: dict[int, list[int]] = {i: [] for i in range(1, n + 1)}
    for i in range(2, n + 1):
        children[par[i]].append(i)

    def subtree_shape(v: int) -> tuple | None:
        """If subtree at v is a bare path hanging down, return its length."""
        ln = 0
        cur = v
        while True:
            ch = children[cur]
            if len(ch) == 0:
                return ("path", ln + 1)
            if len(ch) > 1:
                return None
            cur = ch[0]
            ln += 1

    desc: dict[int, list] = {}
    for v in range(1, n + 1):
        arms = []
        for c in children[v]:
            s = subtree_shape(c)
            if s is not None:
                arms.append(s[1])
        if arms:
            desc[v] = sorted(arms)
    return desc


def process(census_file: str, n: int) -> list[dict]:
    rows = []
    for line in open(f"{DIR}/{census_file}"):
        _, par_s, coef_s = line.strip().split("\t")
        par = [0, 0] + [int(x) for x in par_s.split()][1:]  # par[i] for i=1..n
        claimed = [int(x) for x in coef_s.split(",")]
        # build T (0-indexed) for python DP
        t = p.T()
        for i in range(2, n + 1):
            t.add(par[i] - 1)
        c_py = p.indep_poly(t)
        # deletion recursion on raw edges
        edges = frozenset(frozenset((par[i], i)) for i in range(2, n + 1))
        verts = frozenset(range(1, n + 1))
        c_del = indep_poly_deletion(edges, verts)
        ok = (c_py == claimed == c_del)
        # LC break data with exact fractions
        breaks = []
        for b in range(1, len(claimed) - 1):
            if claimed[b] ** 2 < claimed[b - 1] * claimed[b + 1]:
                breaks.append({
                    "k": b,
                    "alpha": len(claimed) - 1,
                    "k_minus_alpha": b - (len(claimed) - 1),
                    "ratio": str(Fraction(claimed[b] ** 2,
                                          claimed[b - 1] * claimed[b + 1])),
                    "ratio_float": float(Fraction(claimed[b] ** 2,
                                                  claimed[b - 1] * claimed[b + 1])),
                })
        viol = p.unimodal_violation(claimed)
        rows.append({
            "n": n,
            "parent_array_1indexed": [0] + [par[i] for i in range(2, n + 1)],
            "edge_list": sorted([par[i], i] for i in range(2, n + 1)),
            "coefficients": claimed,
            "alpha": len(claimed) - 1,
            "lc_breaks": breaks,
            "unimodal": viol is None,
            "verified_by": ["C rooted DP", "Python leaf-up DP",
                            "Python vertex-deletion recursion"] if ok else "MISMATCH",
            "arm_structure_by_vertex": {str(k): v for k, v in
                                        strip_P2_arms(par, n).items()},
        })
        assert ok, f"verification failed for {par_s}"
        assert viol is None
    return rows


def main() -> None:
    out = {}
    for f, n in (("nlc_n26_census.txt", 26), ("nlc_n28_census.txt", 28),
                 ("nlc_n29_census.txt", 29)):
        rows = process(f, n)
        out[n] = rows
        json.dump({"n": n, "count": len(rows),
                   "note": "complete census of non-log-concave trees on "
                           f"{n} vertices from exhaustive sweep; all unimodal; "
                           "each verified by 3 independent implementations",
                   "trees": rows},
                  open(f"{DIR}/nlc_n{n}_census.json", "w"), indent=1)
        print(f"n={n}: {len(rows)} trees, all triple-verified. Break summary:")
        for r in rows:
            print(f"  alpha={r['alpha']} breaks at k={[b['k'] for b in r['lc_breaks']]}"
                  f" (k-alpha={[b['k_minus_alpha'] for b in r['lc_breaks']]})"
                  f" min ratio={min(b['ratio_float'] for b in r['lc_breaks']):.7f}")
    # global min LC ratio at n=28 (compare to Reynolds' 0.8565666)
    r28 = min(b["ratio_float"] for r in out[28] for b in r["lc_breaks"])
    print("min LC ratio at n=28:", f"{r28:.7f}", "(Reynolds reports 0.8565666)")


if __name__ == "__main__":
    main()
