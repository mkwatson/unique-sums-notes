# Public-note computational reproduction

From the repository root, run exactly:

```text
./repro/run.sh
```

Typical runtime is a few minutes, dominated by the bundled `support/verify.py` brute-force
suite. The command uses Python 3 and the standard library.
It is deterministic and writes only `last-run.json` beside the runner.

The ordered-count trap is always the first row. The deliberately perturbed expected value is the
second row and must print `EXPECTED-FAIL`; the summary must say
`failing_control_firing_count=1`. Any other failure, or failure of that control to fire, makes the
command exit nonzero.

## What the existing verifier covers

`support/verify.py` checks: the $Q=2$ numerical threshold; sample subset-sum profiles and the
Vandermonde inequality through $n=29$; several auxiliary growth/crossover examples; the $C_{12}$
representation table and midpoint failures; $m(p)$ by brute force through $p=19$; balanced minima
through $p=19$; the displayed $p=41,43,47,53,59$ upper witnesses; small finite-group minima; and the
$C_2 \times C_{11}$ projection counterexample. This package invokes that file unchanged and hashes both the
file and its output. It does not copy its algorithms.

## What this package adds

It checks the ordered-count trap before anything else, demonstrates a real comparison failure,
checks the published Census-52 manifest hash and all 114 formula rows, directly recounts all 113
stored upper witnesses, checks all 114 stored `proof_verified` flags, checks the exact one-log
crossover, and independently checks that the displayed $p=127$ selector obstruction has no compatible
linear order under the exact betweenness criterion and that its normalized seven-subset denominator
is $\binom{125}{5} = 234531275$. Every executed row prints canonical SHA-256 hashes of its inputs and
output.

A `PASS` means only that this run reproduced the stated finite calculation or checked the retained
artifact at the stated scope. It is not a proof certification and does not upgrade any verification
tier. In particular, checking a manifest's `proof_verified` flags is not replaying DRAT. The
Census-52 and parity-localization lower bounds require their retained CNF/DRAT certificates and
checker logs, which are kept privately and are not distributed with this package; this package
points to their existence but neither copies nor re-solves them.

The complete inventory and cost classifications are in `INVENTORY.md`.

This package is **TESTED, not PROVED**. It does not establish the mathematical claims whose
certificates or Lean proofs lie outside this directory.
