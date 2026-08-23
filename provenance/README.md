# Exact-run provenance

These directories preserve the retained outputs and witness rechecks for the July 25
$m(53)$ run, the July 27 $m(59)$ run, and the six published witnesses checked on August 18.

The files document the recorded computations at their stated scopes. They do not turn the
uncertified exhaustive runs into DRAT proofs, and witness rechecks do not establish
minimality.

For both p = 53 and p = 59, coverage is exhaustive for every k from 3 up to m(p) - 1, not
only the last one or two sizes: `m53-exact-2026-07-25/` ships `counts_53_3.txt` through
`counts_53_13.txt`, and `m59-exact-2026-07-27/` ships `counts_59_3.txt` through
`counts_59_12.txt` plus the k = 13 leg at `m59-noprune-2026-07-27/` and the k = 14 leg in
`m59-exact-2026-07-27/enum59_14.out`. Neither m(53) = 14 nor m(59) = 15 relies on
unique-sum-freeness being monotone in k.
