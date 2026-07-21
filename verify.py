"""Checks the arithmetic and small computations in note.pdf.  Stdlib only.

    python3 verify.py
"""
import itertools
from math import comb, log2

# Section 1: Luczak-Schoen Theorem 2 at Q = 2
# Hypothesis: Q < log2 p / (2 log2 (gamma_p log2 p)), with gamma_p <= 2.

def q_bound(log2p, gamma=2.0):
    return log2p / (2 * log2(gamma * log2p))

assert q_bound(21) < 2 <= q_bound(22), "Q = 2 becomes admissible at p = 2^22"
for log2p in (22, 64, 1024):
    assert q_bound(log2p) > 2
print("Section 1: Q = 2 admissible for p >= 2^22.")

# Section 2: the first binomial in Proposition 1 is redundant
# |Sigma(Z)| <= #{dissociated I} <= sum_{j<=d} binom(n,j),  versus
# Bedert's |Sigma(Z)| <= binom(n,d) binom(n+d,d).

def zero(z):
    return tuple(0 for _ in z) if isinstance(z, tuple) else 0

def add(a, b):
    return tuple(x + y for x, y in zip(a, b)) if isinstance(a, tuple) else a + b

def profile(Z):
    """(|Sigma(Z)|, #dissociated index sets, dim(Z)) by exhaustive search."""
    n, z0 = len(Z), zero(Z[0])
    sigma, dissoc, dim = set(), 0, 0
    for k in range(n + 1):
        for I in itertools.combinations(range(n), k):
            sums = set()
            for m in range(k + 1):
                for J in itertools.combinations(I, m):
                    s = z0
                    for j in J:
                        s = add(s, Z[j])
                    sums.add(s)
            sigma |= sums
            if len(sums) == 2 ** k:
                dissoc, dim = dissoc + 1, max(dim, k)
    return len(sigma), dissoc, dim

def extremal(k, d):
    """Bedert p.6: k copies of each of d basis vectors in Z^d."""
    return [tuple(1 if c == i else 0 for c in range(d))
            for i in range(d) for _ in range(k)]

families = [[1, 2, 4, 8], [1, 1, 1, 1], [1, 2, 3, 6], [5, 5, 7, 7],
            [0, 1, 2, 3], [2, 3, 5, 7, 11], extremal(3, 2), extremal(2, 3)]

for Z in families:
    sigma, dissoc, d = profile(Z)
    n = len(Z)
    ours = sum(comb(n, j) for j in range(d + 1))
    bedert = comb(n, d) * comb(n + d, d)
    assert sigma <= dissoc <= ours <= bedert

# The Vandermonde step of the Proposition, which the Lean development does not cover.
for n in range(1, 30):
    for d in range(n + 1):
        assert sum(comb(n, j) for j in range(d + 1)) <= comb(n + d, d)

for k, d in ((3, 2), (4, 2), (2, 3)):
    sigma, dissoc, _ = profile(extremal(k, d))
    assert sigma == dissoc == (k + 1) ** d, "equality on Bedert's extremal"

print(f"Section 2: chain holds and is at least as tight on {len(families)} families;")
print("          Vandermonde step holds for all n <= 29;")
print("          both sides equal (k+1)^d on Bedert's extremal.")


# Observations: growth bound for the GAP container
# A translate step prepends a side of length 2; a cube step maps L -> 3L - 2.
# Claim: log2(product of sides) <= 0.4 j^2 + j for every schedule of length j.

def sides_after(schedule):
    sides = []
    for step in schedule:
        sides = [2] + sides if step == "t" else [3 * L - 2 for L in sides]
    return sides

for j in range(1, 15):
    for bits in range(2 ** j):
        schedule = ["tc"[bits >> i & 1] for i in range(j)]
        prod = 1
        for L in sides_after(schedule):
            prod *= L
        assert log2(max(prod, 1)) <= 0.4 * j * j + j + 1e-9
print("Observations: growth bound holds for all schedules with j <= 14.")

# Observations: the two-rate budget is worth exactly 3^(1/4)
L23 = log2(3)
for L in (64.0, 2.0 ** 20, 2.0 ** 64):
    gain = (L / (L23 / 12)) ** 0.25 / (L / (L23 / 4)) ** 0.25
    assert abs(gain - 3 ** 0.25) < 1e-12
print("Observations: two-rate budget multiplies the constant by 3^(1/4) = %.4f." % 3 ** 0.25)

# Observations: the conversion damping and crossover
import math
f = lambda x: x / (2 * (2 + log2(x)))            # [B]'s conversion, eq (16)
M = 2.0 ** 64
w1_B = math.sqrt(math.log(M) / math.log(3)) / 6
w1_new = math.sqrt(math.sqrt(2.5 * M) - 1.25) / 6
assert round(w1_B / f(w1_B), 1) == 4.2 and round(w1_new / f(w1_new), 1) == 31.5
ratio = lambda u: u ** 0.25 * math.log(math.log(u)) / math.log(u) ** 1.5
lo, hi = 1e2, 1e12
for _ in range(200):
    mid = (lo * hi) ** 0.5
    lo, hi = (mid, hi) if ratio(mid) < 1 else (lo, mid)
assert 4e4 < lo < 6e4
print("Observations: loss factors 4.2 vs 31.5 at M = 2^64; omega crossover near log log p = 5e4.")

# Observations: the set counterexample
def gadget(h):
    d = 2 * h
    Z = []
    for i in range(h):
        for mask in range(1 << h):
            v = [0] * d
            v[i] = 1
            for j in range(h):
                if mask >> j & 1:
                    v[h + j] = 1
            Z.append(tuple(v))
    return Z, d

for h in (2, 3):
    Z, d = gadget(h)
    assert len(Z) == len(set(Z)), "must be a genuine set"
    S = {tuple([0] * d)}
    for z in Z:
        S |= {tuple(a + b for a, b in zip(s, z)) for s in S}
    assert log2(len(S)) >= d * d / 4
# dim bound: 2^|D| distinct subset sums inside {0..|D|}^d forces 2^m <= (m+1)^d
for d in (32, 512, 4096):
    m = 1
    while 2 ** m <= (m + 1) ** d:
        m += 1
    assert (d * d / 4) / (m - 1) >= {32: 1.0, 512: 10, 4096: 60}[d]
print("Observations: counterexample verified; separation ratio grows (>= 1, 10, 60 at d = 32, 512, 4096).")

# Observations: m(p) for small p, independent brute force
def m_of(p):
    for k in range(2, p + 1):
        for A in itertools.combinations(range(p), k):
            counts = {}
            for a in A:
                for b in A:
                    s = (a + b) % p
                    counts[s] = counts.get(s, 0) + 1
            if all(v >= 3 for v in counts.values()):
                return k

expected = {3: 3, 5: 4, 7: 5, 11: 7, 13: 7, 17: 8, 19: 9}
for p, want in expected.items():
    assert m_of(p) == want, (p, want)
print("Observations: m(p) reproduced for p <= 19:", expected)

# Observations: minimum balanced-set sizes ([B] Definition 6) for small p
def bal_of(p):
    def balanced(B):
        return all(any((b1 + b2) % p == (2 * b) % p
                       for b1 in B for b2 in B if b1 != b2) for b in B)
    for k in range(2, p + 1):
        for B in itertools.combinations(range(p), k):
            if balanced(B):
                return k

expected_bal = {3: 3, 5: 4, 7: 5, 11: 5, 13: 6, 17: 6, 19: 6}
for p, want in expected_bal.items():
    got = bal_of(p)
    assert got == want, (p, got, want)
    c = math.ceil(log2(p) + 1)
    assert got in (c, c + 1)
print("Observations: balanced-set minima reproduced for p <= 19:", expected_bal)
