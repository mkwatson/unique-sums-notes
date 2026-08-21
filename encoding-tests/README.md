# Encoding tests

Two independent test harnesses for the CNF encoding, plus the pinned production
encoder itself (`usf_encode_pinned.py`, SHA-256
`2eeec8ec926f80ee0d9db55a4f396acc3fe92110cc9bfc78908260a53b1c9003`).

`encodediff.py` compares a direct CNF encoder and an independent CP-SAT encoder
with a solver-free oracle, then applies six fixed semantic mutations. Run it with
`python3 encodediff.py --limit 13 --kissat <path> --verifier <path> --output out.json`;
OR-Tools and `kissat` must be installed.

`mutation_harness.py` targets the production encoder directly. For every odd prime
$p \le 13$ and every $2 \le k \le p$ it fixes all $2^p$ membership assignments,
solves the auxiliary variables, and compares the projected satisfying-assignment
set against a brute-force oracle, using Minisat22 and CaDiCaL independently. It
then applies 34 source-level mutations (clause deletions, literal flips, bound
off-by-ones, comparator swaps). Run `python3 mutation_harness.py` (requires
`python-sat`). Result: 30 of 34 mutants caught; 4 survive, and each survivor is
traced in `mutation-harness-results.json` to a clause provably redundant under
the encoder's pinned semantics. The harness refuses to run unless the unmutated
clone matches the production encoder clause-for-clause on every test case.

**TESTED, NOT PROVED:** these are exhaustive finite tests at $p \le 13$. They do
not prove encoding faithfulness at larger primes and do not connect the Lean
specification to DIMACS bytes; that connection is the subject of `witness-kernel/`,
which states exactly which parts of it are certified.

`roundtrip_control.py` checks a different property from either harness above:
that this repository's own DIMACS parser and printer agree with themselves
(parse -> print -> reparse), which neither `encodediff.py` nor
`mutation_harness.py` tests and which the Lean scanner theorems in
`witness-kernel/` do not cover either (they prove the parser matches a
reference scan and that a tampered literal is detected, not that print/reparse
is idempotent). Run `python3 roundtrip_control.py`. Result: **PASS**: the
positive control round-trips exactly on 29 of 29 `(p, k)` pairs spanning
$p\in\{3,5,7,11,13\}$, and the negative control (a header clause count
corrupted to disagree with the clause body, body left untouched) is correctly
refused rather than silently accepted.
