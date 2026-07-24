"""Erdos #106 k=3: SLSQP multi-start from feasible structured configurations.
Maximize sum of sides of 10 arbitrarily-oriented squares in the unit square.
After SLSQP: exact repair (shrink to feasibility) then greedy inflate to
recover the softmin safety gap. Reports certified-feasible sums (exact SAT)."""
import numpy as np, json, sys
import a_packing as ap
from a_polish import polish

def pair_pens_exact(p):
    P = p[None, :]
    cx, cy, th, s = ap.unpack(P)
    h = 0.5 * np.abs(s)
    c, sn = np.cos(th), np.sin(th)
    ci, si = c[:, ap.PI], sn[:, ap.PI]; cj, sj = c[:, ap.PJ], sn[:, ap.PJ]
    hi, hj = h[:, ap.PI], h[:, ap.PJ]
    dx = cx[:, ap.PI] - cx[:, ap.PJ]; dy = cy[:, ap.PI] - cy[:, ap.PJ]
    pens = np.empty((1, len(ap.PAIRS), 4))
    for k, (ax, ay) in enumerate([(ci, si), (-si, ci), (cj, sj), (-sj, cj)]):
        ri = hi * (np.abs(ci * ax + si * ay) + np.abs(-si * ax + ci * ay))
        rj = hj * (np.abs(cj * ax + sj * ay) + np.abs(-sj * ax + cj * ay))
        pens[:, :, k] = ri + rj - np.abs(dx * ax + dy * ay)
    return np.min(pens, axis=2)[0]

def feasible(p, tol=0.0):
    _, pen, cont = ap.exact_state(p)
    return pen <= tol and cont <= tol

def greedy_inflate(p, passes=4):
    p = p.copy()
    for _ in range(passes):
        for i in range(ap.NSQ):
            lo_f, hi_f = 1.0, 1.2
            # find max factor for square i keeping feasibility
            q = p.copy()
            q[30 + i] = p[30 + i] * hi_f
            if feasible(q):
                p = q; continue
            for _ in range(40):
                mid = 0.5 * (lo_f + hi_f)
                q[30 + i] = p[30 + i] * mid
                if feasible(q): lo_f = mid
                else: hi_f = mid
            p[30 + i] = p[30 + i] * lo_f
    return p

def start_splitcell(rng, split_cell, tilt_sigma, small_tilt=None):
    third = 1 / 3
    cx = []; cy = []; th = []; s = []
    cells = [(i, j) for i in range(3) for j in range(3)]
    for k, (i, j) in enumerate(cells):
        if k == split_cell:
            for (di, dj) in [(0.25, 0.25), (0.75, 0.75)]:
                cx.append((i + di) * third); cy.append((j + dj) * third)
                th.append(small_tilt if small_tilt is not None else rng.normal(0, tilt_sigma))
                s.append(1 / 6 * 0.995)
        else:
            cx.append((i + 0.5) * third); cy.append((j + 0.5) * third)
            th.append(rng.normal(0, tilt_sigma)); s.append(third * 0.995)
    return np.concatenate([cx, cy, th, s])

def start_diag(rng):
    # diagonal bricks at 45 degrees
    cx = []; cy = []; th = []; s = []
    g = 0.235
    pos = [(0.17, 0.17), (0.5, 0.17), (0.83, 0.17),
           (0.17, 0.5), (0.5, 0.5), (0.83, 0.5),
           (0.17, 0.83), (0.5, 0.83), (0.83, 0.83), (0.5, 0.85)]
    for k, (x, y) in enumerate(pos):
        cx.append(x + rng.normal(0, 0.01)); cy.append(y + rng.normal(0, 0.01))
        th.append(np.pi / 4 + rng.normal(0, 0.05)); s.append(g * rng.uniform(0.7, 1.0))
    return np.concatenate([cx, cy, th, s])

def start_pinwheel(rng):
    cx = [0.5]; cy = [0.5]; th = [rng.uniform(0, 0.3)]; s = [0.3]
    for k in range(4):
        ang = k * np.pi / 2
        cx.append(0.5 + 0.33 * np.cos(ang + np.pi / 4)); cy.append(0.5 + 0.33 * np.sin(ang + np.pi / 4))
        th.append(rng.uniform(0, np.pi / 2)); s.append(0.22)
    for k in range(5):
        ang = k * 2 * np.pi / 5
        cx.append(0.5 + 0.45 * np.cos(ang)); cy.append(0.5 + 0.45 * np.sin(ang))
        th.append(rng.uniform(0, np.pi / 2)); s.append(0.1)
    return np.concatenate([cx, cy, th, s])

if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "a_slsqp_results.jsonl"
    rng = np.random.default_rng(7)
    starts = []
    starts.append(("splitcell-flat", start_splitcell(rng, 8, 0.0, 0.0)))
    for sc in [0, 4, 8]:
        for sig in [0.12, 0.35]:
            starts.append((f"splitcell-{sc}-tilt{sig}", start_splitcell(rng, sc, sig)))
    starts.append(("splitcell-smalldiag", start_splitcell(rng, 4, 0.0, np.pi / 4)))
    for k in range(3):
        starts.append((f"diag{k}", start_diag(rng)))
    for k in range(2):
        starts.append((f"pinwheel{k}", start_pinwheel(rng)))
    # adam best from earlier run, if exists
    try:
        recs = [json.loads(l) for l in open("a_results.jsonl")]
        recs.sort(key=lambda r: -r["best_sum"])
        pm = recs[0]["params"]
        starts.append(("adam-best", np.array(pm["cx"] + pm["cy"] + pm["theta"] + pm["s"])))
    except FileNotFoundError:
        pass
    f = open(out, "a", buffering=1)
    best = None
    for name, p0 in starts:
        pr, ssum, pen, cont, r = polish(p0)
        pr2 = greedy_inflate(pr)
        s2, pen2, cont2 = ap.exact_state(pr2)
        theta_dev = float(np.max(np.abs(np.mod(pr2[20:30] + np.pi / 4, np.pi / 2) - np.pi / 4)))
        rec = dict(start=name, slsqp_sum=ssum, inflated_sum=s2, max_pen=pen2,
                   max_cont=cont2, max_theta_dev_from_axis=theta_dev,
                   params=pr2.tolist())
        f.write(json.dumps(rec) + "\n")
        print(json.dumps({k: rec[k] for k in rec if k != "params"}), flush=True)
        if best is None or s2 > best[0]:
            best = (s2, pr2, pen2, cont2)
    ssum, pr, pen, cont = best
    json.dump(dict(problem="Erdos 106 k=3: 10 tilted squares in unit square",
                   conjectured_max=3.0, achieved_sum=ssum, gap_to_3=3 - ssum,
                   max_SAT_penetration=pen, max_containment_violation=cont,
                   squares=[dict(cx=pr[i], cy=pr[10 + i], theta=pr[20 + i], side=abs(pr[30 + i]))
                            for i in range(10)]),
              open("a_best_packing.json", "w"), indent=1)
    print(json.dumps(dict(final_best=ssum, gap_to_3=3 - ssum)), flush=True)
