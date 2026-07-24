"""Erdos #488 experiments.

Statement (confirmed from erdosproblems.com/488):
  A finite set of positive integers, B = {n>=1 : a|n for some a in A},
  conjecture: for every m > n >= max(A),  |B cap [1,m]|/m < 2 |B cap [1,n]|/n.

We search for large values of  R(A) = sup_{m>n>=max(A)} f(m)/f(n), f(x)=|B cap [1,x]|/x.
R(A) > 2 would disprove the conjecture. Singleton {a} gives 2 - 1/a.
Asymptotic regime (m -> infinity): f(m) -> delta(A) exactly (B is periodic mod lcm(A)),
so R_asym(A) = delta(A) / min_{n>=max(A)} f(n) is a genuine lower bound for the sup
(any value > 2 here is a genuine counterexample).
"""
import numpy as np
import json, math, sys, time, itertools

OUT = open(sys.argv[1] if len(sys.argv) > 1 else "b_results.jsonl", "a", buffering=1)

def log(obj):
    OUT.write(json.dumps(obj) + "\n")
    print(json.dumps(obj), flush=True)

def primes_upto(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if s[p]: s[p*p::p] = False
    return np.nonzero(s)[0]

def ratio_scan(A, X, return_f=False):
    """Best finite ratio f(m)/f(n) over m>n>=max(A), all within [1,X]."""
    A = sorted(set(int(a) for a in A))
    mA = A[-1]
    assert mA < X
    b = np.zeros(X + 1, dtype=bool)
    for a in A:
        b[a::a] = True
    cnt = np.cumsum(b, dtype=np.int64)  # cnt[v] = |B cap [1,v]|
    v = np.arange(mA, X + 1, dtype=np.float64)
    f = cnt[mA:] / v  # f at values mA..X
    prefmin = np.minimum.accumulate(f)
    ratios = f[1:] / prefmin[:-1]      # ratio at m=mA+1+i using n<m
    i = int(np.argmax(ratios))
    m = mA + 1 + i
    j = int(np.argmin(f[:i + 1]))
    n = mA + j
    out = dict(ratio=float(ratios[i]), n=n, m=m,
               fn=float(f[j]), fm=float(f[i + 1]),
               cnt_n=int(cnt[n]), cnt_m=int(cnt[m]),
               min_f=float(prefmin[-1]), argmin_f=mA + int(np.argmin(f)))
    if return_f:
        out["_f"] = f; out["_cnt"] = cnt
    return out

def delta_exact(A):
    """Exact density of B by inclusion-exclusion over subsets (|A| small)."""
    A = sorted(set(int(a) for a in A))
    t = len(A)
    if t > 22: return None
    total = 0.0
    from math import gcd
    for mask in range(1, 1 << t):
        l = 1
        for i in range(t):
            if mask >> i & 1:
                l = l // gcd(l, A[i]) * A[i]
                if l > 10**18: break
        total += (-1) ** (bin(mask).count("1") + 1) / l
    return total

def delta_primes(P):
    """delta for a set of distinct primes: 1 - prod(1-1/p)."""
    s = np.sum(np.log1p(-1.0 / np.asarray(P, dtype=np.float64)))
    return 1.0 - math.exp(s)

# ---------------- Phase 1: singleton baseline sanity ----------------
def phase1():
    for a in [5, 50, 500, 5000, 500000, 49999999]:
        r = ratio_scan([a], 2 * a + 10)
        r.update(phase=1, A=f"singleton {a}", pred=2 - 1 / a)
        log(r)

# ---------------- Phase 2: exhaustive small subsets ----------------
def phase2(hi=16, X=100000):
    t0 = time.time()
    elems = list(range(2, hi + 1))
    best = []  # (ratio, A)
    best_norm = []  # ((2-ratio)*maxA, ratio, A)
    n_sub = 0
    for r_sz in range(1, len(elems) + 1):
        for A in itertools.combinations(elems, r_sz):
            # skip non-primitive (some a divides another): equivalent to subset
            ok = True
            for i in range(len(A)):
                for j in range(i + 1, len(A)):
                    if A[j] % A[i] == 0: ok = False; break
                if not ok: break
            if not ok: continue
            n_sub += 1
            res = ratio_scan(A, X)
            best.append((res["ratio"], A, res["n"], res["m"]))
            best_norm.append(((2 - res["ratio"]) * max(A), res["ratio"], A))
            if len(best) > 4000:
                best.sort(reverse=True); best = best[:50]
                best_norm.sort(); best_norm = best_norm[:50]
    best.sort(reverse=True); best_norm.sort()
    log(dict(phase=2, n_subsets=n_sub, secs=time.time() - t0,
             top_ratio=[dict(ratio=b[0], A=list(b[1]), n=b[2], m=b[3]) for b in best[:15]],
             top_normalized_excess=[dict(excess_times_maxA=b[0], ratio=b[1], A=list(b[2])) for b in best_norm[:15]]))

# ---------------- Phase 3: hill-climb over subsets, medium scale ----------------
def phase3(lo=2, hi=400, X=500000, iters=1200, seeds=3):
    rng = np.random.default_rng(0)
    global_best = (0, None)
    for seed in range(seeds):
        # different starts
        if seed == 0:
            A = {hi}
        elif seed == 1:
            P = [p for p in primes_upto(hi) if p > hi // 2]
            A = set(P)
        else:
            A = set(rng.integers(lo, hi + 1, size=6).tolist())
        cur = ratio_scan(A, X)["ratio"]
        for it in range(iters):
            B = set(A)
            move = rng.integers(0, 3)
            if move == 0 or not B:
                B.add(int(rng.integers(lo, hi + 1)))
            elif move == 1 and len(B) > 1:
                B.discard(int(rng.choice(list(B))))
            else:
                x = int(rng.choice(list(B))); B.discard(x)
                B.add(max(lo, min(hi, x + int(rng.integers(-10, 11)))))
            if not B: continue
            r = ratio_scan(B, X)["ratio"]
            if r >= cur:
                A, cur = B, r
        res = ratio_scan(A, X)
        res.update(phase=3, seed=seed, A=sorted(A))
        log(res)
        if cur > global_best[0]: global_best = (cur, sorted(A))
    log(dict(phase=3, summary="best", ratio=global_best[0], A=global_best[1]))

# ---------------- Phase 4: structured families, large sieve ----------------
def phase4():
    # (a) primes in (x, 2x]
    P = primes_upto(4000)
    for x in [50, 200, 1000]:
        A = [int(p) for p in P if x < p <= 2 * x]
        res = ratio_scan(A, 10**7)
        res.update(phase=4, family=f"primes ({x},{2*x}]", size=len(A),
                   delta=delta_primes(A))
        res["ratio_asym"] = res.pop("delta") / res["min_f"]
        log(res)
    # (b) Chojecki-failure family (known to fail only below max(A)) at n>=max(A)
    for a in [3, 10, 50]:
        b_ = 5 * a + 1
        T = [t for t in range(5 * a + 2, 10 * a + 2) if t % a != 0]
        A = [a, b_] + T
        res = ratio_scan(A, 10**6)
        res.update(phase=4, family=f"chojecki a={a}", size=len(A))
        log(res)
    # (c) big singleton in a 1e8 sieve
    a = 49999999
    res = ratio_scan([a], 10**8)
    res.update(phase=4, family=f"singleton {a} X=1e8", pred=2 - 1 / a)
    log(res)

# ---------------- Phase 5: asymptotic regime (Tao) ----------------
def model_ratio(P, lnN, order3=True):
    """Model: f(n) ~ S1 - S2 + S3 (truncated at products <= n), delta exact.
    P: array of primes (window selection), lnN = ln n."""
    lp = np.log(P.astype(np.float64))
    inv = 1.0 / P
    S1 = inv.sum()
    # pairs with p1*p2 <= n  i.e. lp1+lp2 <= lnN, p1<p2
    idx = np.argsort(lp)
    lps, invs = lp[idx], inv[idx]
    csum_inv = np.cumsum(invs)
    S2 = 0.0
    for i in range(len(lps)):
        # partners j>i with lps[j] <= lnN - lps[i]
        lim = lnN - lps[i]
        j = np.searchsorted(lps, lim, side="right") - 1
        if j > i:
            S2 += invs[i] * (csum_inv[j] - csum_inv[i])
    S3 = 0.0
    if order3 and lps[0] * 3 <= lnN:
        for i in range(len(lps)):
            if 3 * lps[i] > lnN: break
            for j in range(i + 1, len(lps)):
                lim = lnN - lps[i] - lps[j]
                if lps[j] > lim: break
                k = np.searchsorted(lps, lim, side="right") - 1
                if k > j:
                    S3 += invs[i] * invs[j] * (csum_inv[k] - csum_inv[j])
    f = S1 - S2 + S3
    d = delta_primes(P)
    return d / f, f, d, S1, S2, S3

def phase5_model():
    """Optimize window(s) in u = ln p / ln n space using the truncated model."""
    N = 10**8; lnN = math.log(N)
    P = primes_upto(int(N ** 0.5) + 1).astype(np.int64)
    lpu = np.log(P) / lnN
    results = []
    # single window (alpha, beta)
    for alpha in np.arange(0.16, 0.47, 0.02):
        for beta in np.arange(alpha + 0.03, 0.51, 0.02):
            sel = P[(lpu > alpha) & (lpu <= beta)]
            if len(sel) < 5: continue
            r, f, d, *_ = model_ratio(sel, lnN)
            results.append((r, ("win", round(float(alpha), 3), round(float(beta), 3)), f, d, len(sel)))
    results.sort(reverse=True)
    log(dict(phase=5, stage="model-single-window",
             top=[dict(ratio=r[0], cfg=r[1], f=r[2], delta=r[3], nprimes=r[4]) for r in results[:10]]))
    # refine around best
    best = results[0]
    a0, b0 = best[1][1], best[1][2]
    fine = []
    for alpha in np.arange(max(0.13, a0 - 0.04), a0 + 0.045, 0.01):
        for beta in np.arange(b0 - 0.04, min(0.52, b0 + 0.045), 0.01):
            if beta <= alpha + 0.02: continue
            sel = P[(lpu > alpha) & (lpu <= beta)]
            if len(sel) < 5: continue
            r, f, d, *_ = model_ratio(sel, lnN)
            fine.append((r, (round(float(alpha), 3), round(float(beta), 3)), f, d))
    fine.sort(reverse=True)
    log(dict(phase=5, stage="model-single-window-fine",
             top=[dict(ratio=r[0], cfg=r[1], f=r[2], delta=r[3]) for r in fine[:8]]))
    # two windows
    two = []
    for a1 in np.arange(0.16, 0.40, 0.04):
        for b1 in np.arange(a1 + 0.04, 0.48, 0.04):
            for a2 in np.arange(b1 + 0.02, 0.48, 0.04):
                for b2 in np.arange(a2 + 0.04, 0.52, 0.04):
                    sel = P[((lpu > a1) & (lpu <= b1)) | ((lpu > a2) & (lpu <= b2))]
                    if len(sel) < 5: continue
                    r, f, d, *_ = model_ratio(sel, lnN)
                    two.append((r, (round(float(a1), 3), round(float(b1), 3), round(float(a2), 3), round(float(b2), 3))))
    two.sort(reverse=True)
    log(dict(phase=5, stage="model-two-windows", top=[dict(ratio=r[0], cfg=r[1]) for r in two[:8]]))
    return fine[:3], two[:3]

def phase5_verify(cfgs_single, cfgs_two):
    """Exact sieve verification at X = 1e8 of the best model configs."""
    N = 10**8; lnN = math.log(N)
    P = primes_upto(int(N ** 0.5) + 1).astype(np.int64)
    lpu = np.log(P) / lnN
    def verify(sel, name):
        sel = sel[sel >= 2]
        A = [int(p) for p in sel]
        t0 = time.time()
        res = ratio_scan(A, N)
        d = delta_primes(sel)
        res.update(phase=5, stage="sieve-verify", cfg=name, nprimes=len(A),
                   maxA=max(A), delta=d, ratio_asym=d / res["min_f"], secs=time.time() - t0)
        log(res)
        return res
    out = []
    for r, cfg, f, d in cfgs_single:
        alpha, beta = cfg
        sel = P[(lpu > alpha) & (lpu <= beta)]
        out.append(verify(sel, ("win",) + tuple(cfg)))
    for r, cfg in cfgs_two:
        a1, b1, a2, b2 = cfg
        sel = P[((lpu > a1) & (lpu <= b1)) | ((lpu > a2) & (lpu <= b2))]
        out.append(verify(sel, ("2win",) + tuple(cfg)))
    return out

def phase4b():
    """Half-window family primes (X^b/2, X^b] at various scales b, exact sieve."""
    N = 10**8
    P = primes_upto(int(N ** 0.5) + 1).astype(np.int64)
    for beta in [0.2, 0.3, 0.4, 0.5]:
        hi = N ** beta
        sel = P[(P > hi / 2) & (P <= hi)]
        if len(sel) < 3: continue
        A = [int(p) for p in sel]
        res = ratio_scan(A, N)
        d = delta_primes(sel)
        res.update(phase="4b", family=f"primes (X^{beta}/2, X^{beta}]", size=len(A),
                   maxA=max(A), delta=d, ratio_asym=d / res["min_f"])
        log(res)

if __name__ == "__main__":
    t0 = time.time()
    only5 = "--phase5" in sys.argv
    if not only5:
        phase1()
        phase2()
        phase3()
        phase4()
    s, t = phase5_model()
    phase5_verify(s, t)
    phase4b()
    log(dict(done=True, total_secs=time.time() - t0))
