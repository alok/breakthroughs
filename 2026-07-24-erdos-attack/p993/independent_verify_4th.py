#!/usr/bin/env python3
"""4th independent verification of the NLC witness censuses (n=26,28,29).

Recomputes each witness tree's independence polynomial via the vertex-deletion
recurrence I(G) = I(G-v) + x*I(G-N[v]) with max-degree pivoting and memoization
(distinct from the three verifications recorded in the census files), then
checks coefficients, log-concavity break indices, and unimodality."""
import json, sys
sys.setrecursionlimit(100000)
from functools import cache

def indep_poly(edges, n):
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    @cache
    def poly(vs):
        if not vs:
            return (1,)
        v = max(vs, key=lambda w: len(adj[w] & vs))
        a = poly(vs - {v})
        b = poly(vs - {v} - (adj[v] & vs))
        out = list(a) + [0] * (len(b) + 1 - len(a))
        for i, c in enumerate(b):
            out[i + 1] += c
        return tuple(out)
    return list(poly(frozenset(range(n))))

if __name__ == "__main__":
    tot = 0
    for fname in ["nlc_n26_census.json", "nlc_n28_census.json", "nlc_n29_census.json"]:
        d = json.load(open(fname))
        assert d["count"] == len(d["trees"])
        for t in d["trees"]:
            edges = [tuple(e) for e in t["edge_list"]]
            if min(min(e) for e in edges) == 1:
                edges = [(u - 1, v - 1) for u, v in edges]
            coeffs = indep_poly(edges, t["n"])
            assert coeffs == t["coefficients"]
            ks = [k for k in range(1, len(coeffs) - 1)
                  if coeffs[k] ** 2 < coeffs[k - 1] * coeffs[k + 1]]
            assert ks == [b["k"] for b in t["lc_breaks"]]
            peak = coeffs.index(max(coeffs))
            assert all(coeffs[i] <= coeffs[i + 1] for i in range(peak))
            assert all(coeffs[i] >= coeffs[i + 1] for i in range(peak, len(coeffs) - 1))
            tot += 1
        print(f"{fname}: {len(d['trees'])} verified")
    print(f"TOTAL {tot}/28 OK")
