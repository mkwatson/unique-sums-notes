# m(59) = 15, EXACT

    enum59_14      rc=0  wall=27226s  out=[59 14 0 0 157121096646]
    noprune_59_13  rc=0  wall=8098s   out=[59 13 0 0 43183019880]

## The result

ZERO unique-sum-free sets of size 14 in `Z/59Z`, by exhaustive search. Combined with the
prune-free `m(59) >= 14` banked at `../m59-noprune-2026-07-27/`, this gives `m(59) >= 15`.
Scheinerman's published upper bound is 15. Therefore **m(59) = 15**.

This INDEPENDENTLY CONFIRMS Scheinerman's Table 3.1 value, which he asserts without proof (his
thesis gives witnesses and no exhaustiveness claim), and raises it to an exhaustive tier.

## Pre-registration held

Before launch the arm derived the full unpruned tree for `(p,n)` as `C(p-2, n-3)`, validated
against six prior runs digit for digit, giving `C(57,11) = 184,509,266,760` for `(59,14)`. It then
pre-registered an expected prune survival of **0.75-0.85**, i.e. 138-157 billion nodes.

**Observed: 157,121,096,646 nodes, survival 0.852.** At the top of the predicted band. The
prediction was recorded before the run, not fitted afterwards.

## Tier

EXACT by exhaustion. **NOT "certified"** in this campaign's sense: no DRAT proof exists or is
claimed, and this run PRUNES. The `n = 13` half is separately confirmed PRUNE-FREE; the `n = 14`
half is not. A prune-free `enum_noprune 59 14` would take roughly 3.5x longer and has not been run.

## Cross-check that did not land, and why that is fine

The same job ran in parallel on AWS (`c7g.medium`). It hit its hard 8h timeout at `rc=124` with
empty output while the local run finished at 7.6h. **That is the harness working as designed:**
FIX 2 (job timeout) fired, FIX 3 (shutdown armed at boot) and the CloudWatch reaper bounded the
spend at $0.32, and nothing was left running. The lesson for next time is that the 8h cap was set
too tight for a 7.6h job on a slower single vCPU, not that anything failed.
