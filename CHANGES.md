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

<!-- The "Changes from v1 to staged v2" and "Changes from published v2 to
     staged v3" blocks are not repeated here: the repository's root
     `CHANGES.md` already carries the v1-to-v2 history, and `CHANGES-v3.md`
     already carries the v2-to-v3 history. This file contributes only the
     new v3-to-v4 block above; an earlier draft of this file duplicated the
     v1-to-v2 block, which the public-preview build then appended a second
     time on top of the copy already in root `CHANGES.md`. Trimmed here so
     the append is not a duplicate. -->
