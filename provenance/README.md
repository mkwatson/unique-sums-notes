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

`cover-certificates-2026-08-23/` adds a machine-checked SAT certificate, on top of the
per-cube UNSAT proofs, that the retained 16,384-cube partitions for m(53) k=13 and
m(59) k=14 are complete covers of their search spaces, following a pattern by Pawel
Kwaczynski.

`interval-witnesses-2026-08-23/` ships explicit, independently verified USF witness
sets, one per realized size, at p = 53, 59, 61, 67, 71, 73, prompted by Kwaczynski's
observation that the sizes of USF sets appear to form an interval for p <= 47. See its
own README for exactly what is and is not claimed; the general interval statement
across all primes remains open.
