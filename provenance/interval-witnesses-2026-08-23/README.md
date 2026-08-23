# Interval witnesses, p = 53, 59, 61, 67, 71, 73

Machine-found and independently verified unique-sum-free (USF) witness sets, one per
realized size, for six primes. A set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ is USF if
$|A| \ge 2$ and every element of $A+A$ has at least two unordered representations
$a+a'$ (diagonal pairs $a+a$ allowed, unordered: swapping the two entries is not a
second representation). $m(p)$ is the minimum size of a USF set.

## What is claimed

For each prime $p$ and each size $k$ that appears as a key in that prime's JSON file,
an explicit USF set of size $k$ exists in $\mathbb{Z}/p\mathbb{Z}$: **every listed size
is realized.** That is the entire claim. Each witness was found by a SAT solver
(kissat) against a pinned CNF encoding and then independently re-checked by a
completely separate code path, a plain multiplicity-counting verifier with no SAT
machinery. All 239 witnesses across the six files were re-verified once more before
publication.

**Not claimed:**
- That the listed sizes are the *complete* set of realized sizes at any prime. For
  p = 53 and p = 59 the listed range (14-52 and 15-58 respectively) is combined with
  a separate exhaustive zero-count for every size below the minimum, so those two
  ranges are gap-free between the minimum and the top of the range. For
  p = 61, 67, 71, 73 no such below-minimum zero-count was run in this repository:
  $m(p)$ for those four primes is an externally attributed, search-only value (see
  Credit below), not re-derived or certified here.
- That the general statement "for every prime $p$, the sizes of USF sets in
  $\mathbb{Z}/p\mathbb{Z}$ form an interval" holds. That question is open. This
  directory adds finite evidence at six primes; it does not settle the general
  question either way.
- That $k = p$ (the full residue group, trivially USF) is or is not part of any
  interval. It was not tested at any of the six primes; every range here tops out at
  $p - 1$.

## Credit

Pawel Kwaczynski observed, in his own data for $p \le 47$, that the sizes of USF sets
form an interval, and flagged it as a precaution rather than a claim: unique-sum-freeness
is not known to be monotone in $k$, so an exact minimum needs every smaller $k$
separately refuted, not merely $k - 1$. That observation prompted this witness sweep.

$m(61) = 15$ and $m(67) = m(71) = m(73) = 16$ are his values, computed first in
`https://github.com/pawelkwaczynski/unique-sum-free-cert`
(DOI `10.5281/zenodo.22067683`), where they are tagged EXTERNAL / search-only per that
repository's own tier language (two independent search programs agree and the witness
is checked, but no proof object is retained). They are cited here as given, not
re-derived or certified in this repository.

## Method

- Encoder: `usf_encode_pinned.py`'s `encode(p, k)` (pins the normalization $0, 1 \in A$
  for $k \ge 2$; unchanged from prior work in this repository).
- Solver: kissat 4.0.4, default heuristics, no problem-specific tuning.
- Decode: the SAT variable for membership of residue $i$ is $i + 1$;
  $A = \{i : \text{variable } i+1 \text{ true in the model}\}$.
- Independent verification: a separate multiplicity-counting implementation (not the
  encoder's CNF construction) confirms every element of $A + A$ has at least two
  unordered representations.
- Per-instance wall-clock cap: 600s for the p = 53, 59 sweep; 300s for the
  p = 61, 67, 71, 73 sweep. No instance in either sweep hit its cap; every probed
  size returned SAT with a verified witness.

## Files

- `p53.json`, `p59.json`, `p61.json`, `p67.json`, `p71.json`, `p73.json`: one JSON
  object per prime, keys are sizes `k` as strings, values are the sorted witness
  residue lists.
- `SHA256SUMS`: checksums of every file in this directory.

## Per-prime range

| p | m(p) | range witnessed | top of range | below-minimum coverage |
|---|---|---|---|---|
| 53 | 14 | 14-52 | p-1 | exhaustive zero-count, sizes 2-13 |
| 59 | 15 | 15-58 | p-1 | exhaustive zero-count, sizes 2-14 |
| 61 | 15 | 15-60 | p-1 | none in this repository (external m(p)) |
| 67 | 16 | 16-66 | p-1 | none in this repository (external m(p)) |
| 71 | 16 | 16-70 | p-1 | none in this repository (external m(p)) |
| 73 | 16 | 16-72 | p-1 | none in this repository (external m(p)) |

All six ranges are internally gap-free: every integer from the listed minimum through
p-1 is a key in that prime's JSON file.
