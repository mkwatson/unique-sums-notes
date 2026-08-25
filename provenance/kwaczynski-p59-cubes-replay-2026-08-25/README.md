# Replay of Kwaczynski's p = 59 position cubes on the pinned encoder

Pawel Kwaczynski's certification repository (https://doi.org/10.5281/zenodo.22067683) partitions the
p = 59, k = 14 search into 1,596 position cubes. This directory replays every one of those cubes on
this repository's pinned encoder (`usf_encode_pinned.py 59 14`, base CNF sha256
`fa985c9d2c2cf1aaa72b0418e83f22e8c1ef10f6376bd6e29b6fdeb93af093ac`) and records a checked UNSAT
certificate for each. It is the full-scale version of the 300-cube spot check he ran first.

## What is claimed

All 1,596 cubes are UNSAT on the pinned encoding, each certified by at least one of three chains:

- 1,548 cubes: kissat, then drat-trim, then cake_lpr.
- 28 cubes: CaDiCaL 3.0.1 writing LRAT natively, checked by cake_lpr (no drat-trim in this chain).
  11 of these are also certified by the split chain.
- 20 cubes: depth-3 cube splitting (8 children per cube), every child by kissat, drat-trim and cake_lpr,
  plus a cover certificate in the Szeider/Kwaczynski pattern: the base CNF, the parent cube, and the
  negation of every child is refuted by kissat and checked by drat-trim and cake_lpr.

Zero SAT answers. `audit.py` recomputes these counts from the ledgers in `ledgers/`; `audit-output.txt`
is its output; `SHA256SUMS` covers the script and every ledger. Ledger rows carry solver return codes,
checker verdicts, proof hashes and the base CNF hash. Rows that do not meet a chain's criterion (20 rows
whose checker was killed in one run, 3 split parents with a failed child) are present in the ledgers
and excluded by the script; every such cube is certified elsewhere in the set.

## Not claimed

Nothing beyond the 1,596 cubes as given. Proof files were checked at generation and not retained.
This directory does not re-derive m(59); that value's own certificates are in `m59-exact-2026-07-27`
and `cover-certificates-2026-08-23`.
