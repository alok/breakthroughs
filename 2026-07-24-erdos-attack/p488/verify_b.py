"""Independent verification pass for Erdos #488 witnesses.

Uses exact inclusion-exclusion with Python bignums (no numpy, no sieve):
|B cap [1,x]| = sum over nonempty S subset A of (-1)^(|S|+1) floor(x / lcm(S)).
Only feasible for |A| <= ~20.
"""
from math import gcd
from fractions import Fraction
import json, sys

def count_B(A, x):
    A = sorted(set(A))
    t = len(A)
    assert t <= 22
    total = 0
    for mask in range(1, 1 << t):
        l = 1
        bits = 0
        for i in range(t):
            if mask >> i & 1:
                bits += 1
                l = l // gcd(l, A[i]) * A[i]
                if l > x: break
        if l > x:
            continue
        total += (-1) ** (bits + 1) * (x // l)
    return total

def check(A, n, m, claimed_ratio):
    cn, cm = count_B(A, n), count_B(A, m)
    ratio = Fraction(cm, m) / Fraction(cn, n)
    ok_conj = Fraction(cm, m) < 2 * Fraction(cn, n)
    print(json.dumps(dict(A=A if len(A) < 15 else f"{len(A)} elements max {max(A)}",
                          n=n, m=m, cnt_n=cn, cnt_m=cm,
                          exact_ratio=str(ratio), float_ratio=float(ratio),
                          claimed=claimed_ratio, conjecture_holds_here=bool(ok_conj))))

if __name__ == "__main__":
    # singleton big
    check([49999999], 99999997, 99999998, 1.9999999799999997)
    # primes (50,100]
    P = [53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    check(P, 117, 2774, 1.4915448646522906)
    # exhaustive-phase best pair
    check([15, 16], 29, 225, 1.8688888888888888)
