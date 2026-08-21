# Inventory of computational claims in `deliverable/note.tex`

| Note claim | Classification | Reproduction treatment |
|---|---|---|
| Ordered-count interpretation, with `{0,1,2,4,7}` rejected in C11 | RE-DERIVABLE CHEAPLY | First runner row, exact ordered counts. |
| C12 unordered count vector, lack of unique sum, and midpoint failures at 0 and 6 | RE-DERIVABLE CHEAPLY | Existing verifier, exhaustive exact recount. |
| Even-cyclic boundary below 12 | NOT RE-DERIVABLE by this numeric package | Kernel-certified in `CycEven.lean`; the runner does not build Lean. C12 is numerically rechecked. |
| Q=2 becomes admissible at the displayed threshold | RE-DERIVABLE CHEAPLY | Existing verifier. Its legacy implementation uses floating logarithms, so this is not promoted beyond the note's arithmetic check. |
| Vandermonde step and displayed sample/extremal subset-sum profiles | RE-DERIVABLE CHEAPLY | Existing verifier through its published finite scope. |
| Census-52: 88 contiguous plus 26 stress groups, formula match, 113 upper witnesses | RE-DERIVABLE CHEAPLY for manifest/formula/witness recount; NOT RE-DERIVABLE for lower certifications | Runner verifies the published manifest hash, 114 formula rows, and 113 witnesses. DRAT files/checker logs are retained in the private evidence line and not distributed with the note, so the DRAT claim cannot be replayed from the public package. This agrees with NUMAUDIT's evidence-backed classification. |
| Double-cyclic parity localization for p=3,5,7,11,13,17,19,23 | NOT RE-DERIVABLE from the public note package | DRAT-tier claim; requires retained certificates. The existing verifier checks only small group minima and the projection counterexample, not parity localization. |
| C2 x C11 full-double-lift counterexample | RE-DERIVABLE CHEAPLY | Existing verifier exhaustively recounts it. |
| Arithmetic-hypothesis satisfiability model for the one-log theorem | NOT RE-DERIVABLE by this package | The note does not publish the model/producer; the theorem itself is kernel-certified, outside this numeric runner. |
| `p > 2^(2^404)` numerical-vacuity threshold | RE-DERIVABLE CHEAPLY | Runner checks the exact symbolic crossover at M=404; this does not certify the surrounding theorem. |
| Selector threshold over 29 primes and 234,531,275 seven-subsets at p=127 | RE-DERIVABLE AT COST | Durable C/Python producers survive under `kernel-artifacts/simulrect-sharp-2026-07-27/`. Full replay is solver-scale and was classified UNCHECKED by NUMAUDIT; skipped here as `SKIPPED-COST` (no measured end-to-end runtime survives). The runner cheaply checks the explicit p=127 failing 8-set by exact betweenness enumeration. |
| Exact m(p) values for p=3..19 | RE-DERIVABLE CHEAPLY | Existing verifier exhaustively recomputes them. |
| Exact m(p) values p=23,29,31,37 | RE-DERIVABLE AT COST | Exact solver enumeration; skipped `SKIPPED-COST`. Retained artifacts support the published values, but no cheap public one-command producer covers these four. |
| m(41), m(43), m(47) lower bounds | RE-DERIVABLE AT COST | Retained DRAT replay times include 125 s, 222 s, and 510 s; skipped `SKIPPED-COST`. Existing verifier checks only the upper witnesses. |
| m(53)=14 lower bound | RE-DERIVABLE AT COST | Exact exhaustion over billions of nodes, many hours; skipped `SKIPPED-COST`. Existing verifier checks only the upper witness. No DRAT certificate. |
| m(59)=15 lower bound | RE-DERIVABLE AT COST | Measured 27,226 s (7 h 33 m 46 s), pruned size-14 run; skipped `SKIPPED-COST`. This exactly preserves REPROAUDIT's classification and scope. Existing verifier checks only the upper witness. |

`SKIPPED-COST` rows are inventory outcomes, not runtime failures. No expensive computation is
launched by the one-command runner.
