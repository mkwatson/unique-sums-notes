# Changes from v1 to staged v2

- Replaced the broad “Further observations” section with three signal-first
  items: the 2-torsion proof-scope issue, the empty-set convention, and the
  updated $m(p)$ table.
- Dropped all four v1 proof-mechanics subsections: shift-set growth, branch
  increments, the $\omega_1$ conversion discussion, and the limiting
  construction. They are outside the five-item boundary for this revision.
- Added the complete $C_{12}$ representation table and stated explicitly
  that the example does not dispute the general lower-bound theorem itself.
- Added the sharp cyclic even-order boundary and its machine-checked proof.
- Tightened the Łuczak--Schoen and Proposition 1 sections to record the
  author's confirmations without quoting private correspondence.
- Added the empty-set issue in the balanced-set definition and proposition.
- Extended the exact-value table through $p=59$. The table now separates
  certified values from exact-by-exhaustion values and avoids v1's flattened
  “certified optimal” description.
- Carried over `SubsetSums.lean`; added standalone `CycEven.lean` and the
  concrete `C12Witness.lean`.
- Extended `verify.py` with the full $C_{12}$ table check and frontier
  witness checks while retaining every v1 check that remains relevant.

# Changes from v3 to staged v4 draft

- **Correction to the published v3 text.** In "A one-log improvement," v3
  (`deliverable/note.tex`) said the crossover inequality was "numerically
  vacuous at every computable prime" while displaying the crossover condition
  as $p>2^{2^{404}}$. Those two statements contradict each other: the free
  bound $K(A)\geq1$ dominates the displayed inequality $K(A)>\sqrt{M/404}$
  exactly when $M\leq404$, i.e. $p\leq2^{2^{404}}$, the opposite direction
  from what v3 printed, and the direction actually consistent with "vacuous
  at every computable prime." Staged v4 reverses the printed inequality to
  $p<2^{2^{404}}$, matching the vacuity claim. The theorem's statement, tier,
  and Lean artifact are unchanged; only the printed direction of this
  crossover inequality is corrected. Recorded here as a correction to the
  record, per this note's own "corrections to the record are kept, not
  overwritten" method.
- Added a source-grounded acknowledgement of Cao and Yuan's unrefereed
  preprint, arXiv:2608.06728, stating their theorem in their vocabulary.
- Recorded the adjudicated comparison exactly: the displayed theorems are
  overlapping and incomparable, while the Cao--Yuan asymptotic lower bound
  strictly dominates the derived role of our theorem in bounding $m(p)$.
  No theorem in the note is described as refuted.
- Replaced the internal theorem's shortened ``unconditional'' label with its
  current exact tier: kernel-certified per the recorded original elaboration,
  unconditional only with respect to removal of `hBLR`, and not freshly
  re-verifiable on the present 16 GiB host.
- Marked the one-log theorem as superseded in asymptotic $m(p)$ role while
  preserving its exact statement, formal artifact, and verification tier.
- Preserved $m(53)=14$ and $m(59)=15$ as exact by exhaustion with verified
  witnesses and explicitly not DRAT-certified.
- Updated the DRAT-certified double-cyclic localization evidence through
  $p=29$.
- Added the already-staged Green, Nedev, and Scheinerman citations, including
  inline credit for the double-cyclic conjecture, its projection example, the
  exact-value table, and the cyclic conjecture tested by Census-52.
- Added explicit non-kernel and source-grounded tier labels where the earlier
  prose could be read too broadly.
- Updated the note date and bibliography without altering the frozen v3 tree.

# 2026-08-21: certified tier upgrade for m(53) and m(59); a closure replay

- **Certified tier upgrade for $m(53)=14$ and $m(59)=15$.** Each value moves
  from "exact by exhaustion, not DRAT-certified" to a solver-certified
  tier.
  New DRAT/LRAT certificates close the previously uncertified exclusion
  legs: the size-13 exclusion at $p=53$ and the size-14 exclusion at
  $p=59$, each via an exhaustive cube partition, every cube UNSAT, every
  per-cube proof generated and checked at generation time, and a hash-bound
  LRAT retained and independently re-checked. The raw DRAT was generated
  and checked but discarded rather than kept; the LRAT is the retained,
  re-checked artifact. `note.tex`'s exact-value table and the top-level
  verification-tier section state this precisely. The original
  exact-by-exhaustion evidence in `provenance/` is unaffected and stands as
  its own, separate confirmation channel. Only the verification tier
  changes; the values themselves stay the same.
- **A fresh replay of the one-log theorem's 19-module closure.** The
  closure was previously recorded only at the tier "recorded original
  elaboration," because it exceeds the memory of the 16 GiB host it was
  written on. An independent replay of the full closure on a documented 64
  GiB host has since completed: the target elaboration finished in 14
  seconds with a measured peak resident set size of about 7.3 GiB, all
  three required declarations printed exactly `[propext, Classical.choice,
  Quot.sound]`, an independent positive control (`WitnessKernel.lean`)
  passed, and a doctored negative control was correctly rejected by Lean.
  The top-level readme states this measured replay directly; the full
  host, command sequence, and control record is in `repro/BIGREPLAY.md`.
  The theorem's statement and axioms are unchanged; what is new is the
  independent re-verification of the recorded original elaboration.

# 2026-08-21: parse-level byte-tamper theorem, checked on cloud

- **A new theorem in the SAT-encoding verification chain.**
  `tampered_production117_parse_fails` (`ChainCloseTamper.lean`) shows a
  single flipped literal in the production DIMACS bytes is caught by
  parsing rather than silently accepted. It is checked at a new tier,
  kernel-checked-on-cloud: checked on a documented cloud host (region
  `us-east-1`, instance type `r8g.16xlarge`), not yet independently
  replayed on this note's own local machine, so it is not described as
  kernel-certified. Direct elaboration of the target measured 32 seconds at
  a peak of about 8.0 GiB; an earlier apparent reading near 40 GiB was later
  attributed to a one-time build of a separate dependency, not the target
  theorem's own cost. `README.md`'s "Verification tiers" section and
  `statement-audit.md`'s new Part III give the exact tier definition, the
  formal statement, and its scope.

# 2026-08-21: census extension, and the audit items this release closes

This entry covers the whole of this release: the byte-tamper theorem recorded
in the block above, the census extension, and the presentation fixes.

- **36 further certified groups, in orders 54 to 72.** A census extension run
  on 2026-08-21 solved and certified 36 Abelian groups above the contiguous
  range, listed with their CNF, DRAT, and LRAT hashes in the new
  `mg-census-extension-2026-08-21.json`. Every one matches the
  minimum-over-prime-divisors formula and none contradicts it. Each lower
  bound was replayed by `drat-trim` and again by the verified checker
  `cake_lpr`. Fifteen of the 36 are published here for the first time; the
  other 21 were already among the 26 stress groups of
  `mg-census-through-52.json`, and the rerun reproduced their CNF and DRAT
  hashes byte for byte.
- **What the extension does not do.** It does not extend contiguity. The
  contiguous certified census still stops at order 52 and $C_{53}$ is still
  the first gap, unchanged by this run.
- **Which groups of orders 53 to 100 were left unresolved, and why.** The bare
  prime orders 61, 67, 71, 73, 79, 83, 89 and 97 were excluded from the run by
  design. Of the rest, $C_{62}$ reached the checker and exceeded its
  3600-second replay limit, $C_{74}$ was interrupted by the run's own
  300-minute time cap, and the remainder were never attempted. All 58 are
  listed in the new file with no certification tier, and no predicted value
  among them is stated as measured.
- **Single-toolchain trust basis stated in the tier vocabulary.** The
  kernel-certified entry in `README.md`'s "Verification tiers" section now
  says plainly that these statements are checked by one Lean toolchain and
  re-checked by `lean4checker`, with no second, independently implemented
  proof assistant cross-verifying them.
- **A consequence line per claim.** `statement-audit.md` gains a "What each
  claim changes" table: one line per claim saying what it changes for a
  reader, in one of four categories (witness only, scope repair, reusable
  mechanism, theory change). The audit tables said what each claim is and
  what its check covers; they did not say what it is for.
- **Still open: the second checker.** The external replay of the
  `witness-kernel/` modules through a second, independently implemented proof
  checker has not been run. The tier vocabulary now states that gap where a
  reader will meet it.
- **Still open: the two census predicates.** Neither census manifest is
  accepted by `census-schema/validator.py`. That validator implements the
  ordered representation count; both manifests record the unordered count,
  and the two are different predicates, as `census-schema/SCHEMA.md` states
  in its opening and again in its section 7. The manifests were left in the
  predicate their certificates were produced under.

<!-- The "Changes from v1 to staged v2" and "Changes from published v2 to
     staged v3" blocks are not repeated here: the repository's root
     `CHANGES.md` already carries the v1-to-v2 history, and `CHANGES-v3.md`
     already carries the v2-to-v3 history. This file contributes only the
     new v3-to-v4 block above; an earlier draft of this file duplicated the
     v1-to-v2 block, which the public-preview build then appended a second
     time on top of the copy already in root `CHANGES.md`. Trimmed here so
     the append is not a duplicate. -->
