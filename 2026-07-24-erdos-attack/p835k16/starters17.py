#!/usr/bin/env python3
r"""
Erdos #835 frontier case k=16 (p=17): starter-level analysis in Z17.

A *starter* of Z_p (p odd prime here) is a perfect matching of Z_p \ {0}
into (p-1)/2 pairs whose cyclic gaps {min(d, p-d)} hit each of 1..(p-1)/2
exactly once.  A C_p-twisted proper (p)-coloring of J(2(p-1), p-1) forces
(by the k=10 PROOF.md argument, which generalizes verbatim) a partition of
the edge set of K_{p-1} on Z_p \ {0}  (C(p-1,2) edges)  into  p-2  pairwise
edge-disjoint starters.

This script:
  1. enumerates all starters of Z_p (sanity: p=11 -> 25, p=13 -> 133);
  2. computes ratio-class profiles (edge {a,b} ~ class of b*a^{-1} up to
     inversion) and scans for modular counting obstructions of the k=10 kind;
  3. runs Algorithm-X-style exact cover (min-branching edge, bitmask sets)
     to decide whether p-2 pairwise disjoint starters partition all edges;
  4. if no partition, computes the maximum number of pairwise disjoint
     starters by branch and bound.

Edges are indexed 0..C(p-1,2)-1; a starter is stored as a bitmask over edges.
"""
from __future__ import annotations

import json
import sys
import time
from itertools import combinations


def enumerate_starters(p: int) -> list[list[tuple[int, int]]]:
    half = (p - 1) // 2
    out: list[list[tuple[int, int]]] = []
    pairs_by_pt: dict[int, list] = {}

    def gap(a: int, b: int) -> int:
        d = (a - b) % p
        return min(d, p - d)

    def rec(rem: int, pairs: list[tuple[int, int]], used_gaps: int):
        if rem == 0:
            out.append(sorted(pairs))
            return
        a = (rem & -rem).bit_length() - 1  # smallest remaining point
        rem_a = rem ^ (1 << a)
        m = rem_a
        while m:
            bbit = m & -m
            b = bbit.bit_length() - 1
            m ^= bbit
            g = gap(a, b)
            if not (used_gaps >> g) & 1:
                rec(rem_a ^ bbit, pairs + [(a, b)], used_gaps | (1 << g))

    full = ((1 << p) - 1) ^ 1  # points 1..p-1
    rec(full, [], 0)
    return out


def edge_index(p: int):
    idx = {}
    for i, e in enumerate(combinations(range(1, p), 2)):
        idx[frozenset(e)] = i
    return idx


def starter_masks(p: int, starters) -> list[int]:
    idx = edge_index(p)
    masks = []
    for s in starters:
        m = 0
        for a, b in s:
            m |= 1 << idx[frozenset((a, b))]
        masks.append(m)
    return masks


def ratio_classes(p: int):
    """Partition edges of K_{p-1} on Z_p\\{0} by ratio b*a^{-1} mod p, up to
    inversion. Returns (list of class edge-bitmasks, class labels)."""
    idx = edge_index(p)
    classes: dict[frozenset, int] = {}
    labels = []
    cmasks = []
    for r in range(2, p):  # ratio 1 impossible for an edge
        lab = frozenset((r, pow(r, p - 2, p)))
        if lab in classes:
            continue
        classes[lab] = len(labels)
        labels.append(sorted(lab))
        m = 0
        for a in range(1, p):
            b = a * r % p
            if b != a:
                m |= 1 << idx[frozenset((a, b))]
        cmasks.append(m)
    return cmasks, labels


def analyze(p: int, find_all_partitions: bool = False,
            max_partitions: int = 1):
    t0 = time.time()
    starters = enumerate_starters(p)
    n_start = len(starters)
    print(f"[p={p}] starters: {n_start} ({time.time()-t0:.1f}s)", flush=True)

    nedges = (p - 1) * (p - 2) // 2
    need = p - 2
    masks = starter_masks(p, starters)
    full = (1 << nedges) - 1

    # ---- ratio-class profiles ----
    cmasks, labels = ratio_classes(p)
    csizes = [bin(m).count("1") for m in cmasks]
    from collections import Counter
    profs = []
    for m in masks:
        profs.append(tuple(bin(m & cm).count("1") for cm in cmasks))
    print(f"[p={p}] ratio classes {labels} sizes {csizes}")
    per_class_counts = []
    obstructions = []
    for ci, lab in enumerate(labels):
        cnt = Counter(pr[ci] for pr in profs)
        per_class_counts.append(dict(sorted(cnt.items())))
        # k=10-style modular obstruction: all achievable counts divisible by m
        # but class size not divisible by m (for any modulus m up to 12)
        vals = sorted(cnt)
        for mod in range(2, 13):
            if all(v % mod == 0 for v in vals) and csizes[ci] % mod != 0:
                obstructions.append({"class": lab, "modulus": mod,
                                     "counts": vals, "class_size": csizes[ci]})
    print(f"[p={p}] per-class starter-count distributions:")
    for lab, d, sz in zip(labels, per_class_counts, csizes):
        print(f"    class {lab} (size {sz}): {d}")
    if obstructions:
        print(f"[p={p}] MODULAR OBSTRUCTION(S) FOUND: {obstructions}")
    else:
        print(f"[p={p}] no single-class modular obstruction (moduli 2..12)")

    # ---- exact cover: partition into p-2 disjoint starters ----
    idx = edge_index(p)
    inv_idx = {v: k for k, v in idx.items()}
    by_edge: list[list[int]] = [[] for _ in range(nedges)]
    for si, m in enumerate(masks):
        mm = m
        while mm:
            b = mm & -mm
            by_edge[b.bit_length() - 1].append(si)
            mm ^= b
    t0 = time.time()
    sols: list[list[int]] = []
    chosen: list[int] = []
    nodes = 0

    def cover(covered: int) -> bool:
        nonlocal nodes
        if len(chosen) == need:
            assert covered == full
            sols.append(chosen.copy())
            return len(sols) >= max_partitions and not find_all_partitions
        # min-branching uncovered edge (Algorithm X column heuristic)
        best_e, best_c = -1, None
        rem = full & ~covered
        mm = rem
        while mm:
            b = mm & -mm
            e = b.bit_length() - 1
            mm ^= b
            cands = [si for si in by_edge[e] if not (masks[si] & covered)]
            if best_c is None or len(cands) < len(best_c):
                best_e, best_c = e, cands
                if len(cands) <= 1:
                    break
        for si in best_c:
            nodes += 1
            chosen.append(si)
            if cover(covered | masks[si]):
                return True
            chosen.pop()
        return False

    finished = cover(0)
    dt = time.time() - t0
    if sols:
        print(f"[p={p}] PARTITION into {need} disjoint starters: FOUND "
              f"({nodes} nodes, {dt:.1f}s)")
        part = [[tuple(sorted(inv_idx[e.bit_length()-1]))
                 for e in _bits(masks[si])] for si in sols[0]]
        for si in sols[0]:
            print("   ", starters[si])
        result_part = [starters[si] for si in sols[0]]
        maxdisj = need
    else:
        print(f"[p={p}] NO partition into {need} disjoint starters "
              f"(exhausted search: {nodes} nodes, {dt:.1f}s)")
        result_part = None
        # ---- max disjoint set (branch & bound on starters) ----
        maxdisj = max_disjoint(masks, need, by_edge, full, (p - 1) // 2)
        print(f"[p={p}] maximum pairwise-disjoint starters: {maxdisj}")

    return {"p": p, "n_starters": n_start, "ratio_class_labels": labels,
            "ratio_class_sizes": csizes,
            "per_class_count_distributions": per_class_counts,
            "modular_obstructions": obstructions,
            "partition_exists": bool(sols),
            "partition": result_part, "max_disjoint": maxdisj,
            "exact_cover_nodes": nodes, "exact_cover_seconds": round(dt, 2)}


def _bits(m: int):
    while m:
        b = m & -m
        yield b
        m ^= b


def max_disjoint(masks: list[int], cap: int, by_edge, full: int,
                 edges_per_starter: int) -> int:
    """Max pairwise-disjoint starters, branch and bound (greedy start)."""
    best = 0
    n = len(masks)
    t0 = time.time()

    # greedy lower bound (many passes with rotation)
    import random
    rng = random.Random(17)
    for _ in range(2000):
        order = list(range(n))
        rng.shuffle(order)
        cov = 0
        c = 0
        for si in order:
            if not (masks[si] & cov):
                cov |= masks[si]
                c += 1
        best = max(best, c)
    print(f"    greedy lower bound: {best} ({time.time()-t0:.1f}s)")

    # exact branch and bound: order starters by lowest edge; standard
    # max-set-packing on disjointness
    sys.setrecursionlimit(10000)
    nodes = 0
    t0 = time.time()
    order = sorted(range(n), key=lambda si: masks[si] & -masks[si])
    ordmasks = [masks[si] for si in order]

    def bb(i: int, cov: int, size: int):
        nonlocal best, nodes
        nodes += 1
        if size > best:
            best = size
            print(f"    new best {best} ({time.time()-t0:.1f}s, {nodes} nodes)")
        if best >= cap:
            return
        # bound: remaining edges / edges-per-starter
        remaining_capacity = bin(full & ~cov).count("1") // edges_per_starter
        if size + remaining_capacity <= best:
            return
        for j in range(i, len(ordmasks)):
            m = ordmasks[j]
            if not (m & cov):
                bb(j + 1, cov | m, size + 1)

    bb(0, 0, 0)
    print(f"    exact B&B done: {nodes} nodes, {time.time()-t0:.1f}s")
    return best


if __name__ == "__main__":
    ps = [int(a) for a in sys.argv[1:]] or [11, 13, 17]
    results = {}
    for p in ps:
        results[p] = analyze(p)
        print(flush=True)
    json.dump(results, open(f"starters_results_{'_'.join(map(str, ps))}.json",
                            "w"), indent=1)
