"""Erdos #97 attack: search for convex n-gon (n=4m) with D_m symmetry where EVERY
vertex has exactly 4 other vertices at (global) unit distance.

Structure: D_m symmetry, mirror axis = x-axis.
  Orbit A: radius a, phases 2*pi*i/m            (on mirrors)
  Orbit B: radius b, phases (2i+1)*pi/m         (on mirrors)
  Orbit F: radius f, phases +-theta + 2*pi*i/m  (free orbit, size 2m)

Scheme (integers j, p, q, r, sign s):
  E4 (F own pair):  |F0+ - Fj+| = 1   => f = 1/(2 sin(pi j/m))   [rigid]
  E1 (A-B pair)  :  a^2 + b^2 - 2ab cos((2p+1)pi/m) = 1
  E2 (A-F pair)  :  a^2 + f^2 - 2af cos(theta + 2pi q/m) = 1
  E3 (B-F pair)  :  b^2 + f^2 - 2bf cos(s*theta + (2r-1)pi/m) = 1

Every vertex then has exactly 4 unit-distance neighbours:
  A0: B_p, B_{-p-1}, F^+_q, F^-_{-q}
  B0: A_{-p}, A_{p+1}, F^s_r, F^{-s}_{1-r}
  F^+_0: F^+_j, F^+_{-j}, A_{-q}, B_x
Given theta, E2/E3 are quadratics in a/b; E1 becomes g(theta)=0 -> complete 1D scan.
"""
import numpy as np
import json, sys, math

def build_points(m, a, b, f, theta):
    ang_A = 2*np.pi*np.arange(m)/m
    ang_B = (2*np.arange(m)+1)*np.pi/m
    ang_Fp = theta + 2*np.pi*np.arange(m)/m
    ang_Fm = -theta + 2*np.pi*np.arange(m)/m
    pts = []
    for ang, R in ((ang_A, a), (ang_B, b), (ang_Fp, f), (ang_Fm, f)):
        pts.append(np.stack([R*np.cos(ang), R*np.sin(ang)], axis=1))
    return np.concatenate(pts, axis=0)

def check_candidate(m, a, b, f, theta, tol_unit=1e-9, tol_conv=1e-12):
    """Full brute-force verification. Returns dict or None."""
    P = build_points(m, a, b, f, theta)
    n = len(P)
    # distinctness
    D = np.linalg.norm(P[:, None, :] - P[None, :, :], axis=2)
    np.fill_diagonal(D, np.inf)
    min_gap = D.min()
    if min_gap < 1e-5:
        return None
    # unit degrees
    U = np.abs(D - 1.0) < tol_unit
    degs = U.sum(axis=1)
    if degs.min() < 4:
        return None
    # convex position: sort by angle, all cross products positive
    ang = np.arctan2(P[:, 1], P[:, 0])
    order = np.argsort(ang)
    Q = P[order]
    v1 = np.roll(Q, -1, axis=0) - Q
    v2 = np.roll(Q, -2, axis=0) - np.roll(Q, -1, axis=0)
    cross = v1[:, 0]*v2[:, 1] - v1[:, 1]*v2[:, 0]
    min_cross = cross.min()
    if min_cross <= tol_conv:
        return None
    # distinct rays (no two points on same ray through origin)
    angs = np.sort(ang)
    ray_gap = np.diff(np.concatenate([angs, [angs[0] + 2*np.pi]])).min()
    return dict(n=n, min_gap=float(min_gap), min_deg=int(degs.min()),
                max_deg=int(degs.max()), min_cross=float(min_cross),
                ray_gap=float(ray_gap))

def scan_m(m, ntheta=600, verbose=False):
    hits = []
    jmax = (m - 1)//2
    js = [j for j in range(max(1, jmax-3), jmax+1)]
    # 2p+1 odd, near m (near-diametral), != 0 mod m
    vs = [v for v in range(m-7, m) if v % 2 == 1 and v % m != 0 and v > 0]
    qs = list(range(max(0, m//2 - 3), min(m, m//2 + 4)))
    rs = list(range(max(0, m//2 - 3), min(m, m//2 + 4)))
    eps = 1e-6
    thetas = np.linspace(eps, np.pi/m - eps, ntheta)
    for j in js:
        f = 1.0/(2*np.sin(np.pi*j/m))
        disc_base = 1.0 - f*f
        for q in qs:
            c2 = np.cos(thetas + 2*np.pi*q/m)
            d2 = f*f*c2*c2 + disc_base
            ok2 = d2 > 0
            sq2 = np.sqrt(np.clip(d2, 0, None))
            for sa in (1.0, -1.0):
                A = f*c2 + sa*sq2
                if ((A <= 1e-9) | ~ok2).all():
                    continue
                for r in rs:
                    for s in (1.0, -1.0):
                        c3 = np.cos(s*thetas + (2*r-1)*np.pi/m)
                        d3 = f*f*c3*c3 + disc_base
                        ok3 = d3 > 0
                        sq3 = np.sqrt(np.clip(d3, 0, None))
                        for sb in (1.0, -1.0):
                            B = f*c3 + sb*sq3
                            if ((B <= 1e-9) | ~ok3).all():
                                continue
                            for v in vs:
                                C1 = np.cos(v*np.pi/m)
                                G = A*A + B*B - 2*A*B*C1 - 1.0
                                # sign changes where a,b valid
                                valid = (A > 1e-9) & (B > 1e-9) & ok2 & ok3
                                for i in range(len(thetas)-1):
                                    if not (valid[i] and valid[i+1]):
                                        continue
                                    if G[i] == 0 or G[i]*G[i+1] < 0:
                                        # bisect
                                        lo, hi = thetas[i], thetas[i+1]
                                        for _ in range(80):
                                            mid = 0.5*(lo+hi)
                                            cm2 = np.cos(mid + 2*np.pi*q/m)
                                            am = f*cm2 + sa*np.sqrt(f*f*cm2*cm2 + disc_base)
                                            cm3 = np.cos(s*mid + (2*r-1)*np.pi/m)
                                            bm = f*cm3 + sb*np.sqrt(f*f*cm3*cm3 + disc_base)
                                            gm = am*am + bm*bm - 2*am*bm*C1 - 1.0
                                            glo_c2 = np.cos(lo + 2*np.pi*q/m)
                                            alo = f*glo_c2 + sa*np.sqrt(f*f*glo_c2*glo_c2 + disc_base)
                                            glo_c3 = np.cos(s*lo + (2*r-1)*np.pi/m)
                                            blo = f*glo_c3 + sb*np.sqrt(f*f*glo_c3*glo_c3 + disc_base)
                                            glo = alo*alo + blo*blo - 2*alo*blo*C1 - 1.0
                                            if glo*gm <= 0:
                                                hi = mid
                                            else:
                                                lo = mid
                                        theta0 = 0.5*(lo+hi)
                                        ct2 = np.cos(theta0 + 2*np.pi*q/m)
                                        a0 = f*ct2 + sa*np.sqrt(f*f*ct2*ct2 + disc_base)
                                        ct3 = np.cos(s*theta0 + (2*r-1)*np.pi/m)
                                        b0 = f*ct3 + sb*np.sqrt(f*f*ct3*ct3 + disc_base)
                                        if a0 <= 0 or b0 <= 0:
                                            continue
                                        res = check_candidate(m, a0, b0, f, theta0)
                                        if res is not None:
                                            p = (v-1)//2
                                            hit = dict(m=m, j=j, p=p, q=q, r=r,
                                                       s=int(s), sa=int(sa), sb=int(sb),
                                                       a=a0, b=b0, f=f, theta=theta0, **res)
                                            hits.append(hit)
                                            print("HIT!", json.dumps(hit), flush=True)
    return hits

if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    all_hits = []
    for m in range(lo, hi+1):
        h = scan_m(m)
        print(f"m={m}: {len(h)} hits", flush=True)
        all_hits += h
    with open(f"hits4m_{lo}_{hi}.json", "w") as fh:
        json.dump(all_hits, fh, indent=1)
    print("total hits:", len(all_hits))
