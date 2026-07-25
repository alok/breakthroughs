# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Independent verification for sieve647.

1. Brute-force divisor-count sieve (numpy add-at-multiples -- algorithmically
   independent of the SPF/inverse-mul C sieve) over [1, N]: list ALL n with
   max_{m<n}(m+tau(m)) <= n+2, print max value, compare with C output.
2. sympy spot-check of tau(m) against C --dump output for random m in a
   high range.
"""
import subprocess
import random
import sys

import numpy as np
import sympy

SIEVE = "/private/tmp/claude-502/-Users-alokbeniwal-breakthroughs/52a3fab3-ea00-484f-abaf-94fb7d0723cb/scratchpad/p647/sieve647"

# ---- part 1: brute force over [1, N] ----
N = 20_000_000
tau = np.zeros(N + 1, dtype=np.int32)
for d in range(1, N + 1):
    tau[d::d] += 1
vals = np.arange(N + 1, dtype=np.int64) + tau
vals[0] = 0
# running max of m+tau(m) over m < n
prefmax = np.maximum.accumulate(vals)
sols = [n for n in range(1, N + 1) if prefmax[n - 1] <= n + 2]
print("brute-force solutions (all n with R(n)<=n+2) up to", N, ":", sols)
eq = [n for n in sols if prefmax[n - 1] == n + 2]
print("equality solutions (A087280 candidates):", eq)
assert eq == [5, 8, 10, 12, 24], "A087280 mismatch!"
assert all(s <= 24 for s in sols), "unexpected witness in brute force!"
print("global max m+tau(m) for m <=", N, "=", int(prefmax[N]), "at m =", int(np.argmax(vals)))

# C sieve over same range for comparison
out = subprocess.run([SIEVE, "1", str(N + 1), "8"], capture_output=True, text=True)
c_sols = []
for line in out.stdout.splitlines():
    if line.startswith(("small solution n=", "WITNESS n=")):
        c_sols.append(int(line.split("n=")[1].split()[0]))
    if line.startswith("# global max"):
        c_max = int(line.split("=")[1].split()[0].strip())
print("C sieve solutions:", sorted(c_sols))
assert sorted(c_sols) == sols, f"solution list mismatch: {c_sols} vs {sols}"
assert c_max == int(prefmax[N]), f"max mismatch {c_max} vs {int(prefmax[N])}"
print("PART 1 OK: C sieve matches brute force on [1, %d] (solutions + global max)" % N)

# ---- part 2: sympy spot-checks of tau in high ranges ----
rng = random.Random(647)
for base in [10**9, 10**11, 10**12 - 5 * 10**6, 3 * 10**12]:
    lo = base + rng.randrange(10**6)
    hi = lo + 3000
    out = subprocess.run([SIEVE, str(lo), str(hi), "1", "--dump"],
                         capture_output=True, text=True)
    got = {}
    for line in out.stdout.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0].isdigit():
            got[int(parts[0])] = int(parts[1])
    # dump includes warmup region; check only [lo, hi)
    sample = rng.sample(range(lo, hi), 40)
    for m in sample:
        expect = sympy.divisor_count(m)
        assert got[m] == expect, f"tau({m}): C={got[m]} sympy={expect}"
    print(f"PART 2 OK: 40 random tau values match sympy in [{lo}, {hi})")

print("ALL VERIFICATION PASSED")
