# Banked corroboration evidence: m(53) and m(59) solver-free runs

Banked 2026-07-27 by the main Claude session, copied here from a local, untracked
working directory that was never part of any repository.

## Why this exists

These files are the evidence that DISCHARGES the standing withdrawal commitment on
`m(53) = 14`. Until this banking they lived only in that untracked working directory,
unbacked by version control, while the sha256-locked copy at
`m53-shape-census-2026-07-25/verification/RESULTS.txt` stops at `noprune_53_12` and
contains none of the five discharging lines. A single deletion of that working
directory would have left the internal tracking record asserting a discharge with no
artifact behind it, violating this campaign's
own rule that a verified proof leaving no artifact is indistinguishable from one that
was never run.

## What is here

Verbatim copy (`cp -Rp`, timestamps preserved) of the run directory, plus the three C
sources the runs were built from: `enum.c`, `enum_noprune.c`, `enum_shard.c`.
`SHA256SUMS` covers every file except itself; `shasum -a 256 -c SHA256SUMS` returned
64 of 64 OK at banking time.

## The five pre-registered results, as recorded in RESULTS.txt

    slow_43_13            rc=0 wall=1525s   out=[43 13 3588 23 1121099408]
    noprune_53_13         rc=0 wall=7798s   out=[53 13 0 0 12777711870]
    shard59_13            wall=3620s ALL_SHARDS_COMPLETE, usf_sets=0, 6 shards
    usf_cert_prove_53_14  rc=0 wall=9338s   optimality=true
    usf_cert_prove_59_14  rc=0 wall=12891s  optimality=true

`noprune_53_13` matches the pre-registration in `m53-solver-free.md` exactly.

## Limits of this artifact, stated so they travel with it

- This is a COPY of scratch output, not a re-run. It inherits whatever the original runs
  established and nothing more.
- The pre-registration in `m53-solver-free.md` carries no timestamps, so that the
  "expected" column was written BEFORE the runs is assumed here, not verified.
- `usf_cert prove <p> <claimed_m>` enumerates sizes 2 through `claimed_m - 1`
  (`usf_cert.c:347`). `prove 59 14` therefore settles `m(59) >= 14` and says nothing
  about size 14 at p = 59, which has never been run in any spelling.
- Every p = 59 arm here PRUNES. `enum`, `enum_shard` and `usf_cert` all prune, and no
  prune-free run exists at p = 59. `m(59) >= 14` currently rests on a pruning heuristic
  whose only machine-checked corroboration is the drat-verified ladder at p <= 43.
- `m(53) = 14` remains EXACT-by-exhaustion, NOT certified. No DRAT proof exists or is
  claimed. Nothing here is affected by the separate lost cloud verification.
