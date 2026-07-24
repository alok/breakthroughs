"""General D_m ring-family scanner for Erdos #97 (k=4, global unit distance).

Orbits: ('M0', radius) angle 0 mirror orbit; ('M1', radius) angle pi/m mirror orbit;
        ('R', radius, theta) free orbit of size 2m.
Unknowns: radii + thetas. Schemes = edge lists with integer offsets/signs.
One integer offset per free phase is absorbed (fixed to m//2) since theta ranges
over a full period 2pi/m.

Edge residual forms (unit distance):
  ('MM', p):          a^2+b^2-2ab cos((2p+1)pi/m)-1        [M0-M1]
  ('M0R', i, q):      a^2+f^2-2af cos(t+2pi q/m)-1
  ('M1R', i, r, s):   b^2+f^2-2bf cos(s t+(2r-1)pi/m)-1
  ('RR', i, j, k, sg):f^2+g^2-2fg cos(sg tj - ti + 2pi k/m)-1
  ('LR', i, jj):      2f sin(pi jj/m)-1                    [free-orbit own pair]
  ('LM', i, jj):      2a sin(pi jj/m)-1                    [mirror-orbit own pair]
Brute verification (authoritative): every vertex >=4 unit dists, convex position, distinct.
"""
import numpy as np
import itertools, json, sys
from scipy.optimize import least_squares

def build_points(m, orbits, x):
    base = 2*np.pi*np.arange(m)/m
    pts = []
    xi = 0
    for ob in orbits:
        if ob == 'M0':
            R = x[xi]; xi += 1
            pts.append(np.stack([R*np.cos(base), R*np.sin(base)], 1))
        elif ob == 'M1':
            R = x[xi]; xi += 1
            pts.append(np.stack([R*np.cos(base+np.pi/m), R*np.sin(base+np.pi/m)], 1))
        elif ob == 'R':
            R = x[xi]; t = x[xi+1]; xi += 2
            for sgn in (1, -1):
                ang = sgn*t + base
                pts.append(np.stack([R*np.cos(ang), R*np.sin(ang)], 1))
    return np.concatenate(pts, 0)

def brute_check(P, tol_unit=1e-8):
    D = np.linalg.norm(P[:, None, :] - P[None, :, :], axis=2)
    np.fill_diagonal(D, np.inf)
    min_gap = float(D.min())
    if min_gap < 1e-5:
        return None
    degs = (np.abs(D - 1.0) < tol_unit).sum(1)
    ang = np.arctan2(P[:, 1], P[:, 0])
    Q = P[np.argsort(ang)]
    v1 = np.roll(Q, -1, 0) - Q
    v2 = np.roll(Q, -2, 0) - np.roll(Q, -1, 0)
    cross = v1[:, 0]*v2[:, 1] - v1[:, 1]*v2[:, 0]
    return dict(n=len(P), min_gap=min_gap, min_deg=int(degs.min()), max_deg=int(degs.max()),
                min_cross=float(cross.min()), n_nonconvex=int((cross <= 0).sum()))

def orbit_slots(orbits):
    """index of radius (and theta) in x for each orbit"""
    idx = []
    xi = 0
    for ob in orbits:
        if ob in ('M0', 'M1'):
            idx.append((xi, None)); xi += 1
        else:
            idx.append((xi, xi+1)); xi += 2
    return idx, xi

def make_residual(m, orbits, edges):
    idx, nx = orbit_slots(orbits)
    pi = np.pi
    def res(x):
        out = []
        for e in edges:
            typ = e[0]
            if typ == 'MM':
                _, i, j, p = e
                a = x[idx[i][0]]; b = x[idx[j][0]]
                out.append(a*a+b*b-2*a*b*np.cos((2*p+1)*pi/m)-1)
            elif typ == 'M0R':
                _, i, j, q = e
                a = x[idx[i][0]]; f = x[idx[j][0]]; t = x[idx[j][1]]
                out.append(a*a+f*f-2*a*f*np.cos(t+2*pi*q/m)-1)
            elif typ == 'M1R':
                _, i, j, r, s = e
                b = x[idx[i][0]]; f = x[idx[j][0]]; t = x[idx[j][1]]
                out.append(b*b+f*f-2*b*f*np.cos(s*t+(2*r-1)*pi/m)-1)
            elif typ == 'RR':
                _, i, j, k, sg = e
                f = x[idx[i][0]]; ti = x[idx[i][1]]
                g = x[idx[j][0]]; tj = x[idx[j][1]]
                out.append(f*f+g*g-2*f*g*np.cos(sg*tj-ti+2*pi*k/m)-1)
            elif typ == 'LR':
                _, i, jj = e
                f = x[idx[i][0]]
                out.append(2*f*np.sin(pi*jj/m)-1)
            elif typ == 'LM':
                _, i, jj = e
                a = x[idx[i][0]]
                out.append(2*a*np.sin(pi*jj/m)-1)
        return np.array(out)
    return res

def solve(m, orbits, edges, nstarts, rng, radlo=0.42, radhi=0.80):
    idx, nx = orbit_slots(orbits)
    resfun = make_residual(m, orbits, edges)
    out = []
    for _ in range(nstarts):
        x0 = np.empty(nx)
        for (ri, ti) in idx:
            x0[ri] = rng.uniform(radlo, radhi)
            if ti is not None:
                x0[ti] = rng.uniform(1e-3, 2*np.pi/m - 1e-3)
        try:
            sol = least_squares(resfun, x0, method='lm', xtol=1e-15, ftol=1e-15, max_nfev=300)
        except Exception:
            continue
        if sol.cost > 1e-24:
            continue
        radii = [sol.x[ri] for ri, _ in idx]
        if min(radii) < 1e-3:
            continue
        P = build_points(m, orbits, sol.x)
        chk = brute_check(P)
        if chk is None:
            continue
        out.append((sol.x.copy(), chk))
    return out

def report(tag, m, orbits, edges, x, chk, best_only_neg=False):
    rec = dict(tag=tag, m=m, orbits=list(orbits), edges=[list(e) for e in edges],
               x=list(map(float, x)), **chk)
    print(("HIT!! " if chk['min_deg'] >= 4 and chk['min_cross'] > 0 else "near ")
          + json.dumps(rec), flush=True)
    return rec

# ---------------- families ----------------

def scan_S6a_v2(m, rng, nstarts=6):
    """orbits A=M0(0), B=M1(1), F=R(2), G=R(3); edges AF,AG,BF,BG,FG,FG'. qF=qG=m//2 absorbed."""
    orbits = ['M0', 'M1', 'R', 'R']
    h2 = m//2
    hits, best = [], None
    rwin = range(h2-1, h2+3)
    kwin = range(h2-1, h2+3)
    for rF, sF in itertools.product(rwin, (1, -1)):
        for rG, sG in itertools.product(rwin, (1, -1)):
            fg_opts = [(k, sg) for k in kwin for sg in (1, -1)]
            for e1, e2 in itertools.combinations(fg_opts, 2):
                edges = [('M0R', 0, 2, h2), ('M0R', 0, 3, h2),
                         ('M1R', 1, 2, rF, sF), ('M1R', 1, 3, rG, sG),
                         ('RR', 2, 3, e1[0], e1[1]), ('RR', 2, 3, e2[0], e2[1])]
                for x, chk in solve(m, orbits, edges, nstarts, rng):
                    if best is None or (chk['min_deg'] >= 4 and chk['min_cross'] > best[1]['min_cross']):
                        best = (x, chk, edges)
                    if chk['min_deg'] >= 4 and chk['min_cross'] > 0:
                        hits.append(report('S6a', m, orbits, edges, x, chk))
    if best is not None:
        chk = best[1]
        print(f"m={m} S6a_v2 best: deg={chk['min_deg']} min_cross={chk['min_cross']:+.3e} "
              f"nonconv={chk['n_nonconvex']}/{chk['n']}", flush=True)
    return hits

def scan_S7(m, rng, nstarts=5):
    """orbits A=M0(0), F=R(1), G=R(2), H=R(3); edges A-F, A-G, F-G, F-H x2? no:
       F: A,G,H,H? earlier derivation: A-F, A-G, F-G, F-Hx2, G-Hx2 = 7 edges.
       Wait that's F: A+G+H+H = 4 ok, G: A+F+H+H = 4 ok, H: F,F?? recount:
       F-Hx2 gives H two F-singles; G-Hx2 gives H two G-singles => H: 4 ok. yes."""
    orbits = ['M0', 'R', 'R', 'R']
    h2 = m//2
    hits, best = [], None
    kwin = range(h2-1, h2+3)
    fh_opts = [(k, sg) for k in kwin for sg in (1, -1)]
    e1 = (h2, 1)  # first F-H edge absorbed into tH
    for kFG, sFG in [(k, s) for k in kwin for s in (1, -1)]:
        for e2 in [e for e in fh_opts if e != e1]:
            for e3, e4 in itertools.combinations(fh_opts, 2):
                edges = [('M0R', 0, 1, h2), ('M0R', 0, 2, h2),
                         ('RR', 1, 2, kFG, sFG),
                         ('RR', 1, 3, e1[0], e1[1]),
                         ('RR', 1, 3, e2[0], e2[1]),
                         ('RR', 2, 3, e3[0], e3[1]),
                         ('RR', 2, 3, e4[0], e4[1])]
                for x, chk in solve(m, orbits, edges, nstarts, rng):
                    if best is None or (chk['min_deg'] >= 4 and chk['min_cross'] > best[1]['min_cross']):
                        best = (x, chk, edges)
                    if chk['min_deg'] >= 4 and chk['min_cross'] > 0:
                        hits.append(report('S7', m, orbits, edges, x, chk))
    if best is not None:
        chk = best[1]
        print(f"m={m} S7 best: deg={chk['min_deg']} min_cross={chk['min_cross']:+.3e} "
              f"nonconv={chk['n_nonconvex']}/{chk['n']}", flush=True)
    return hits

def _worker_S6a(args):
    m, edges, seed = args
    rng = np.random.default_rng(seed)
    orbits = ['M0', 'M1', 'R', 'R']
    out = []
    for x, chk in solve(m, orbits, edges, 6, rng):
        out.append((list(map(float, x)), chk, edges))
    return out

def scan_S6a_mp(m, pool):
    orbits = ['M0', 'M1', 'R', 'R']
    h2 = m//2
    rwin = range(h2-1, h2+3)
    kwin = range(h2-1, h2+3)
    jobs = []
    seed = 1000*m
    for rF, sF in itertools.product(rwin, (1, -1)):
        for rG, sG in itertools.product(rwin, (1, -1)):
            fg_opts = [(k, sg) for k in kwin for sg in (1, -1)]
            for e1, e2 in itertools.combinations(fg_opts, 2):
                edges = [('M0R', 0, 2, h2), ('M0R', 0, 3, h2),
                         ('M1R', 1, 2, rF, sF), ('M1R', 1, 3, rG, sG),
                         ('RR', 2, 3, e1[0], e1[1]), ('RR', 2, 3, e2[0], e2[1])]
                seed += 1
                jobs.append((m, edges, seed))
    hits, best = [], None
    for res in pool.imap_unordered(_worker_S6a, jobs, chunksize=32):
        for x, chk, edges in res:
            if chk['min_deg'] >= 4:
                if best is None or chk['min_cross'] > best[1]['min_cross']:
                    best = (x, chk, edges)
                if chk['min_cross'] > 0:
                    hits.append(report('S6a', m, orbits, edges, x, chk))
    if best is not None:
        chk = best[1]
        print(f"m={m} S6a best: deg={chk['min_deg']} min_cross={chk['min_cross']:+.3e} "
              f"nonconv={chk['n_nonconvex']}/{chk['n']} x={['%.4f' % v for v in best[0]]} "
              f"edges={best[2]}", flush=True)
    return hits

def _worker_S7(args):
    m, edges, seed = args
    rng = np.random.default_rng(seed)
    orbits = ['M0', 'R', 'R', 'R']
    out = []
    for x, chk in solve(m, orbits, edges, 5, rng):
        out.append((list(map(float, x)), chk, edges))
    return out

def scan_S7_mp(m, pool):
    orbits = ['M0', 'R', 'R', 'R']
    h2 = m//2
    kwin = range(h2-1, h2+3)
    fh_opts = [(k, sg) for k in kwin for sg in (1, -1)]
    e1 = (h2, 1)
    jobs = []
    seed = 5000*m
    for kFG, sFG in [(k, s) for k in kwin for s in (1, -1)]:
        for e2 in [e for e in fh_opts if e != e1]:
            for e3, e4 in itertools.combinations(fh_opts, 2):
                edges = [('M0R', 0, 1, h2), ('M0R', 0, 2, h2),
                         ('RR', 1, 2, kFG, sFG),
                         ('RR', 1, 3, e1[0], e1[1]),
                         ('RR', 1, 3, e2[0], e2[1]),
                         ('RR', 2, 3, e3[0], e3[1]),
                         ('RR', 2, 3, e4[0], e4[1])]
                seed += 1
                jobs.append((m, edges, seed))
    hits, best = [], None
    for res in pool.imap_unordered(_worker_S7, jobs, chunksize=32):
        for x, chk, edges in res:
            if chk['min_deg'] >= 4:
                if best is None or chk['min_cross'] > best[1]['min_cross']:
                    best = (x, chk, edges)
                if chk['min_cross'] > 0:
                    hits.append(report('S7', m, orbits, edges, x, chk))
    if best is not None:
        chk = best[1]
        print(f"m={m} S7 best: deg={chk['min_deg']} min_cross={chk['min_cross']:+.3e} "
              f"nonconv={chk['n_nonconvex']}/{chk['n']} x={['%.4f' % v for v in best[0]]} "
              f"edges={best[2]}", flush=True)
    return hits

if __name__ == "__main__":
    import multiprocessing as mp
    fam = sys.argv[1]
    lo, hi = int(sys.argv[2]), int(sys.argv[3])
    allhits = []
    with mp.Pool(8) as pool:
        for m in range(lo, hi+1):
            if fam == 'S8':
                allhits += scan_S8_mp(m, pool)
            elif fam == 'S6a':
                allhits += scan_S6a_mp(m, pool)
            elif fam == 'S7':
                allhits += scan_S7_mp(m, pool)
            print(f"== m={m} done ({fam}), total hits {len(allhits)}", flush=True)
    with open(f"hits_{fam}_{lo}_{hi}.json", "w") as fh:
        json.dump(allhits, fh, indent=1)

def _worker_S8(args):
    m, edges, seed = args
    rng = np.random.default_rng(seed)
    orbits = ['M0', 'M1', 'R', 'R', 'R']
    out = []
    for x, chk in solve(m, orbits, edges, 4, rng):
        out.append((list(map(float, x)), chk, edges))
    return out

def scan_S8_mp(m, pool):
    orbits = ['M0', 'M1', 'R', 'R', 'R']
    h2 = m//2
    win = range(h2-1, h2+2)
    gh_opts = [(k, sg) for k in win for sg in (1, -1)]
    jobs = []
    seed = 9000*m
    for rF, sF in itertools.product(win, (1, -1)):
        for rH, sH in itertools.product(win, (1, -1)):
            for kFG, sgFG in itertools.product(win, (1, -1)):
                for sgFH in (1, -1):
                    for e1, e2 in itertools.combinations(gh_opts, 2):
                        edges = [('M0R', 0, 2, h2), ('M0R', 0, 3, h2),
                                 ('M1R', 1, 2, rF, sF), ('M1R', 1, 4, rH, sH),
                                 ('RR', 2, 3, kFG, sgFG), ('RR', 2, 4, h2, sgFH),
                                 ('RR', 3, 4, e1[0], e1[1]), ('RR', 3, 4, e2[0], e2[1])]
                        seed += 1
                        jobs.append((m, edges, seed))
    hits, best = [], None
    for res in pool.imap_unordered(_worker_S8, jobs, chunksize=64):
        for x, chk, edges in res:
            if chk['min_deg'] >= 4:
                if best is None or chk['min_cross'] > best[1]['min_cross']:
                    best = (x, chk, edges)
                if chk['min_cross'] > 0:
                    hits.append(report('S8', m, orbits, edges, x, chk))
    if best is not None:
        chk = best[1]
        print(f"m={m} S8 best: deg={chk['min_deg']} min_cross={chk['min_cross']:+.3e} "
              f"nonconv={chk['n_nonconvex']}/{chk['n']} x={['%.4f' % v for v in best[0]]} "
              f"edges={best[2]}", flush=True)
    return hits
