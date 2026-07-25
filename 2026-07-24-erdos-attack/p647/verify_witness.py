# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Exact standalone verification that a claimed witness n satisfies
max_{m<n}(m + tau(m)) <= n + 2.

Usage: uv run verify_witness.py N

Method (fully independent of the C sieve):
  - For m <= n - W (W = 10^7): m + tau(m) <= m + 2*sqrt(m) < n - W + 2*sqrt(n)
    < n <= n+2 whenever 2*sqrt(n) < W, i.e. n < 2.5e13.  (tau(m) <= 2*sqrt(m)
    because divisors pair (d, m/d) with min(d, m/d) <= sqrt(m).)
  - For m in (n - W, n): exact tau via a numpy divisor-pair counting sieve
    (count d <= sqrt(m) dividing m; each such d contributes 2, minus 1 if
    d*d == m), then check m + tau(m) <= n + 2.
  - Second opinion: sympy.divisor_count on the 200 largest m and 200 random m.
"""
import sys
import math
import random

import numpy as np
import sympy

def tau_window(A: int, B: int) -> np.ndarray:
    """tau(m) for m in [A, B) via divisor-pair counting."""
    ln = B - A
    tau = np.zeros(ln, dtype=np.int64)
    sq = math.isqrt(B - 1)
    for d in range(1, sq + 1):
        first = ((A + d - 1) // d) * d
        idx = np.arange(first - A, ln, d, dtype=np.int64)
        vals = idx + A
        # pairs (d, m/d): contributes 2 when d < m/d i.e. d*d < m; 1 when d*d == m
        contrib = np.where(vals == d * d, 1, np.where(vals > d * d, 2, 0))
        np.add.at(tau, idx, contrib)
    return tau

def main() -> None:
    n = int(sys.argv[1])
    W = 10**7
    assert n < 2.5e13, "trivial-bound window too small for this n"
    A = max(1, n - W)
    tau = tau_window(A, n)
    vals = np.arange(A, n, dtype=np.int64) + tau
    bad = np.nonzero(vals > n + 2)[0]
    if len(bad):
        m = int(bad[0]) + A
        print(f"NOT a witness: m={m}, tau={int(tau[bad[0]])}, m+tau={int(vals[bad[0]])} > {n+2}")
        sys.exit(1)
    # spot-check tau against sympy
    rng = random.Random(1)
    k = min(200, len(tau))
    idxs = list(range(len(tau) - k, len(tau))) + rng.sample(range(len(tau)), k)
    for i in idxs:
        m = A + i
        assert int(tau[i]) == sympy.divisor_count(m), f"tau({m}) mismatch"
    print(f"VERIFIED: n={n} satisfies max_(m<n)(m+tau(m)) <= n+2")
    print(f"  window [{A}, {n}) checked exactly; m < {A} covered by trivial bound")
    print(f"  max m+tau(m) in window = {int(vals.max())} at m = {A + int(vals.argmax())} (n+2 = {n+2})")

if __name__ == "__main__":
    main()
