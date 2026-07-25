#!/usr/bin/env python3
"""Generate ErdosattackM/Witnesses.lean: RT rose-tree literals for the 28 NLC census trees.

Mirrors the Lean definitions in ErdosattackM/Basic.lean exactly:
  - RT.size / RT.sizeF, RT.edges / RT.edgesF (first list element gets the LAST label block,
    so building children in *decreasing* census order reproduces census preorder labels),
  - dpA/dpB (foldr-style products), indepPolyRT.
Asserts against the census JSONs before emitting anything.
"""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).parent
CENSUS = [HERE.parent / "p993" / f"nlc_n{n}_census.json" for n in (26, 28, 29)]


# ---------- Lean-mirror polynomial ops ----------
def add(p: list[int], q: list[int]) -> list[int]:
    out = [0] * max(len(p), len(q))
    for i, c in enumerate(p):
        out[i] += c
    for i, c in enumerate(q):
        out[i] += c
    return out


def mul(p: list[int], q: list[int]) -> list[int]:
    if not p:
        return []
    a, rest = p[0], p[1:]
    return add([a * b for b in q], [0] + mul(rest, q))


# ---------- rose trees: children lists, Lean order ----------
# RT is a nested list structure: t = list of children.
def size(t: list) -> int:
    return 1 + sum(size(c) for c in t)


def sizeF(cs: list) -> int:
    return sum(size(c) for c in cs)


def edges(t: list) -> list[tuple[int, int]]:
    return edgesF(t)


def edgesF(cs: list) -> list[tuple[int, int]]:
    if not cs:
        return []
    c, rest = cs[0], cs[1:]
    m = sizeF(rest) + 1
    return edgesF(rest) + [(m, 0)] + [(a + m, b + m) for (a, b) in edges(c)]


def dpA(t: list) -> list[int]:
    return dpAF(t)


def dpAF(cs: list) -> list[int]:
    if not cs:
        return [0, 1]
    return mul(dpAF(cs[1:]), dpB(cs[0]))


def dpB(t: list) -> list[int]:
    return dpBF(t)


def dpBF(cs: list) -> list[int]:
    if not cs:
        return [1]
    return mul(dpBF(cs[1:]), add(dpA(cs[0]), dpB(cs[0])))


def indep_poly_rt(t: list) -> list[int]:
    return add(dpA(t), dpB(t))


def rt_literal(t: list) -> str:
    if not t:
        return ".node []"
    return ".node [" + ", ".join(rt_literal(c) for c in t) + "]"


# ---------- build RT from census parent array ----------
def build_rt(par1: list[int]) -> list:
    """par1: 1-indexed parent array, root vertex 1 with parent 0.
    Children in DECREASING census order so that Lean's labeling (first list
    element gets the last block) reproduces the census preorder labels."""
    n = len(par1)
    children: dict[int, list[int]] = {v: [] for v in range(n)}
    for i in range(1, n):
        children[par1[i] - 1].append(i)  # 0-indexed

    def go(v: int) -> list:
        return [go(c) for c in sorted(children[v], reverse=True)]

    return go(0)


def peak_index(coeffs: list[int]) -> int:
    m = coeffs.index(max(coeffs))
    assert all(coeffs[i] <= coeffs[i + 1] for i in range(m))
    assert all(coeffs[i + 1] <= coeffs[i] for i in range(m, len(coeffs) - 1))
    return m


def lc_break(coeffs: list[int]) -> int:
    for k in range(1, len(coeffs) - 1):
        if coeffs[k] * coeffs[k] < coeffs[k - 1] * coeffs[k + 1]:
            return k
    raise AssertionError("no log-concavity break found")


# ---------- generate ----------
defs: list[str] = []
per_order: dict[int, list[tuple[str, str, int, int]]] = {}

for path in CENSUS:
    d = json.loads(path.read_text())
    for idx, tr in enumerate(d["trees"], 1):
        n = tr["n"]
        par1 = tr["parent_array_1indexed"]
        coeffs = tr["coefficients"]
        rt = build_rt(par1)

        # cross-checks against census + core-package edge format
        assert size(rt) == n
        core_edges = [(i, par1[i] - 1) for i in range(n - 1, 0, -1)]
        assert list(reversed(edges(rt))) == core_edges, (path.name, idx)
        assert indep_poly_rt(rt) == coeffs, (path.name, idx)
        kb = lc_break(coeffs)
        pk = peak_index(coeffs)
        assert coeffs[kb] ** 2 < coeffs[kb - 1] * coeffs[kb + 1]

        name = f"t{n}_{idx}"
        cname = f"c{n}_{idx}"
        per_order.setdefault(n, []).append((name, cname, kb, pk))
        clist = ", ".join(map(str, coeffs))
        elist = ", ".join(f"({c}, {p})" for c, p in core_edges)
        fam = tr.get("family_id", "census")
        defs.append(f"""/-- Witness {idx} on {n} vertices ({fam}), as a rose tree. -/
def {name} : RT := {rt_literal(rt)}

/-- Census coefficient list of `{name}`. -/
def {cname} : List Nat := [{clist}]

theorem {name}_poly : indepPolyRT {name} = {cname} := by decide

/-- `{name}` flattens to exactly the (child, parent) edge list certified in the
core (mathlib-free) package `lean/Erdosattack/Witnesses.lean` as `w{n}_{idx}`. -/
theorem {name}_toEdges : {name}.toEdges = ({n}, [{elist}]) := by decide

/-- Semantic count: `{name}` has exactly `{cname}[k]` independent sets of size `k`. -/
theorem {name}_counts (k : Nat) : {name}.indepCount k = {cname}.getD k 0 := by
  rw [← indepPolyRT_correct, {name}_poly]

theorem {name}_nlc : NLCAt {name}.indepCount {kb} := by
  unfold NLCAt; simp only [{name}_counts]; decide

theorem {name}_unimodal : UnimodalAt {name}.indepCount {pk} := by
  rw [funext {name}_counts]
  exact unimodalAt_getD {cname} {pk} (by decide) (by decide)

theorem {name}_good : GoodTree {name} {cname} {kb} {pk} :=
  ⟨{name}_counts, {name}_nlc, {name}_unimodal⟩
""")

headlines: list[str] = []
for n, ws in sorted(per_order.items()):
    conj = " ∧\n    ".join(f"GoodTree {nm} {cn} {kb} {pk}" for nm, cn, kb, pk in ws)
    prf = ", ".join(f"{nm}_good" for nm, _, _, _ in ws)
    headlines.append(f"""/-- **Headline (n = {n}).** Each of the {len(ws)} census trees on {n} vertices has
independence-set counts given exactly by its census coefficient list, and that
counting sequence `k ↦ #{{independent S ⊆ V, |S| = k}}` breaks log-concavity
yet is unimodal. -/
theorem headline_n{n} :
    {conj} :=
  ⟨{prf}⟩
""")

out = f"""import ErdosattackM.Correct
/-!
# The 28 minimal-order non-log-concave trees, certified semantically

Generated by `gen_witnesses_rt.py` from the census files in `../p993/`
(2 trees on 26 vertices, 19 on 28, 7 on 29). Each tree is given as a rose-tree
(`RT`) literal; `decide` recomputes its independence polynomial in the kernel,
and `indepPolyRT_correct` (proved in `ErdosattackM/Correct.lean`) upgrades the
coefficients to actual counts of independent vertex subsets. The `_toEdges`
theorems certify that each rose tree flattens to exactly the edge list used by
the mathlib-free core package (`lean/Erdosattack/Witnesses.lean`).
-/

namespace ErdosattackM

{chr(10).join(defs)}
{chr(10).join(headlines)}
end ErdosattackM
"""
(HERE / "ErdosattackM" / "Witnesses.lean").write_text(out)
print(f"wrote Witnesses.lean: {sum(len(v) for v in per_order.values())} witnesses, orders {sorted(per_order)}")
