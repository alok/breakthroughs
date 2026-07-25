#!/usr/bin/env python3
"""k=16 analogue of the k=12 AGL refutation: explicit hand-checkable witness.

Claim: no proper 17-coloring of J(32,16) is equivariant under any group H with
C17 < H <= AGL(1,17) (acting on the 17-cycle support C = {0..16} of [32],
identity on F = {17..31}, colors transforming by the same affine map).

Reason: Z17* is cyclic of order 16 = 2^4, so every nontrivial subgroup of the
multiplier quotient H/C17 contains the unique order-2 element a = -1; hence H
contains an affine involution x -> -x + b on C. WLOG b = 0 (conjugate by a
translation). Equivariance forces color(X) = -color(X) i.e. color(X) = 0 for
every g-invariant vertex X. The two g-invariant vertices below are adjacent.
"""
C = set(range(17)); F = set(range(17, 32))
S = {0, 1, 16}                      # symmetric under x -> -x
A = S | set(range(19, 32))          # 3 + 13 = 16 elements
B = S | {18} | set(range(20, 32))   # 3 + 1 + 12 = 16 elements
assert len(A) == len(B) == 16 and A != B
assert len(A & B) == 15             # adjacent in J(32,16)
g = lambda x: (-x) % 17 if x < 17 else x
assert {g(x) for x in A} == A and {g(x) for x in B} == B
print("verified: adjacent g-invariant pair; equivariance forces both to color 0")
