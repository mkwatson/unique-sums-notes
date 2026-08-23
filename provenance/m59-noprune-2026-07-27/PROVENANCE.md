# m(59) >= 14, PRUNE-FREE. Pre-registered node count matched digit for digit.

## Result

    noprune_59_13 rc=0 wall=8098s out=[59 13 0 0 43183019880]

Zero USF sets of size 13 in Z/59Z, by EXHAUSTIVE PRUNE-FREE search. 8098 s wall.

## Why this matters

Before this run, `m(59) >= 14` rested ENTIRELY on pruning heuristics: every prior arm at p=59
(`enum`, `enum_shard` x6, `usf_cert`) prunes, and no prune-free run existed at that prime. Its
only machine-checked corroboration was the drat-verified ladder at p <= 43, where the prune is
exercised far less hard. That soft spot is now closed.

## The pre-registration, which is the point

The expected output `59 13 0 0 43183019880` was DERIVED A PRIORI from the program's own
combinatorial recurrence BEFORE launch, not estimated: `rec()` increments `nodes` once per call,
and solving `f(m,r) = 1 + sum_{m'=r-1}^{m-1} f(m',r-1)` with `f(m,1)=1` gives `f(m,r) = C(m,r-1)`,
so the full unpruned tree at `(p,n)` is `C(p-2, n-3)`. For `(59,13)`: `C(57,10) = 43,183,019,880`.
The derivation was validated against six known prior runs, digit for digit, before use.

**The observed node count equals the derived count exactly.** A bare "0 0" check could not have
distinguished a complete traversal from a silently truncated one; this can. That distinction is
not hypothetical here: this repo has a documented case of a run declaring `|G| <= 64`, stopping
at 36, and being reported as complete.

## Limits

- Establishes `m(59) >= 14` only. `m(59) <= 15` is Scheinerman's; whether `m(59)` is 14 or 15
  is decided by `enum 59 14`, running locally and in parallel on AWS at time of writing.
- The binary was rebuilt from `enum_noprune.c` with `/usr/bin/cc -O3` and cross-validated against
  three independent prior results before use, because `cc` was shadowed by a shell function on
  this machine. Source banked alongside.
