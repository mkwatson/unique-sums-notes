/-
# Object layer, O6: iteration and composition

FROZEN 2026-07-24 by the Claude freeze arm — fill sorries only; BLOCKED if
unprovable as written. Statements changed at freeze: NONE (all fourteen
theorem statements are byte-identical to the Sol proposal; only this status
header and two docstring notes were updated).

## Freeze record (2026-07-24, Claude freeze arm)

Checklist run (reference/claim-checklists.md, counting-lemma + pricing-chain
items; verification-battery freeze-gate addendum):

* Seam audit against the certified `SqrtChain.lean`, byte-level:
  - `htelescope_from_object_banks_proposed`'s conclusion is
    `sqrt_improvement.htelescope` under `cT := (outward.card : ℝ)`,
    `fI := (inward.card : ℝ)`, `d := (D.card : ℝ)`, `n := (A.card : ℝ)`.
  - `hgrowth_from_object_steps_proposed`'s conclusion is
    `sqrt_improvement.hgrowth` under the same counters, with
    `terminalSize := ((S j).card : ℝ)`; its fill route is
    `one_bit_growth` with `size i := (S i).card` and
    `j = outward.card + inward.card` from the partition.
  - `object_iteration_termination_proposed`'s two terminal conjuncts are
    exactly `sqrt_improvement.hterminalSize` and
    `sqrt_improvement.hcapFailure` (same `min`, same `^ ((1:ℝ)/4)`, same
    strict `<` direction); `FourthPowerCap` (O4Star:221-223) is the
    already-raised fourth-power form of the same cap.
  - The conclusions of `small_dim_sqrt_improvement_proposed` and
    `sqrt_improvement'` are character-identical to the certified
    `sqrt_improvement` conclusion transported by `p := (p : ℝ)`,
    `K := (KA A : ℝ)`; the constant enters ONLY through the shared
    `sqrtChainDenominator = 404` definition (no re-literalized numeral, so
    no MAJOR-1-style constant drift is possible at this seam). Matches the
    note-v3 headline (4.13) `K > sqrt(M/404)` with `M = log₂ log₂ p`.
  - `hscale` conclusions match O5's flag-10 convention
    `(A.card : ℝ) = K * (D.card : ℝ)` byte-for-byte with
    `K := (KA A : ℝ)`.
  - `one_bit_iteration_step_from_O5_proposed`'s `houtwardBank` /
    `hinwardBank` are byte-identical to the hypotheses of the frozen
    `one_bit_branch_dichotomy_from_objects_proposed`; the O5 outward bank's
    extra shift-identity conjunct `t = center a + sel (center a) - a` is
    dropped by conjunction-weakening on the SUPPLY side only (documented in
    the docstring), so O5's conclusions still discharge these hypotheses.
* Quantifier audit: `hstep` in the termination theorem and in
  `sqrt_improvement'` is universally quantified over the CURRENT state
  (and, in the headline, over the chosen `D`), with both cap premises
  re-entered per invocation; it cannot be discharged from one fixed
  O4/O5 witness tuple, because `IsOrientedRepresentationChoice` and the
  `starFibres` thresholds are `S`-dependent. Not a B-S3-style trap: the
  universal sits in a hypothesis (strongest form for the consumer), the
  per-`S` existential is inside it.
* Floor/ceiling directions: outward bank non-strict `≤`, inward bank
  strict `<` per step, weakened to non-strict only at the telescoped
  conclusion — matching the certified `htelescope` comment in SqrtChain
  ("strict gains are weakened to this non-strict telescoping interface")
  and note-v3 (4.2)/(3.11).
* Derivability line-check (per statement, on paper): S1 via
  `Finset.le_sup` on the filtered powerset; S2 sup-attainment (the filter
  always contains `∅`, so the image is nonempty); S3-S6 field arithmetic
  under `hdim`; S7 from the frozen O5 dichotomy plus `0 ∈ S`; S8 by
  time-disjointness of the new-point banks (monotone `D + S i` chain) and
  `Σ|N_i| ≤ |A|` — no `hK` needed, the per-step bounds are supplied
  directly; S9 from `one_bit_growth` + partition cardinality; S10 by
  strict growth of `|A ∩ (D + S i)|` (each bank forces ≥ 1 new point via
  `d/(36K) > 0` from `hDnonempty`+`hK`), bounded by `|A.card|`, with the
  cap-failure translation `¬FourthPowerCap → ratio^(1/4) < |S|` using
  `hC` for `ratio ≥ 0`; S11 `ZMod.card` + `Nat.Prime.minFac`; S12 per
  main.tex:282-341 (see the guard note below); S13 per note-v3 (4.14)
  with `2^M = log₂ p` from `hthr`; S14 composes S2, S13, S4, S6, S12,
  S10, S8, S9 into the certified `sqrt_improvement` exactly as its
  docstring's steps 1-6 prescribe.
* Junk-value audit: every statement whose conclusion or premise mentions
  `KA A` carries `hdim : 0 < dimA A` (S3, S4, S5, S6, S12, S13, S14);
  `sqrtChainDenominator = 404 ≠ 0`; the rpow base `d^6/(C·n^5)` is
  nonneg under `hC : 1 ≤ C` (and Lean-junk-safe at `n = 0` since
  `x/0 = 0`); no ℕ subtraction or ℕ division in any statement. S12's
  `hdim` is additionally LOAD-BEARING as a nonemptiness repair: the empty
  set is vacuously USF and vacuously balanced, and Bedert's Corollary
  balancedG silently assumes two distinct elements; `0 < dimA A` forces a
  nonzero element of `A`, restoring the corollary's regime.
* Vacuity audit: S7's bank hypotheses are the frozen O5 conclusions and
  are non-vacuous (an empty `starFibres` makes `hinwardBank`'s premise
  vacuously true, so its conclusion must genuinely be supplied); S8/S9
  hold non-vacuously at `j = 0` (`0 ≤ n`, `log₂ 1 = 0`); S10's `hstep`
  is satisfiable (vacuously when the cap fails at `{0}`, matching the
  immediate-failure terminal case) and the conclusion then holds with
  `j = 0`; S14's `hstep` premise set is satisfiable at `S = {0}` for
  large `p`.
* Non-load-bearing hypotheses noted (kept deliberately, no deletion,
  O5-freeze precedent): `object_iteration_termination_proposed`'s
  `hDsubA` and `hscale` are not consumed by the termination derivation
  sketched above (the budget arithmetic that needs `hscale` lives in
  SqrtChain); they document the interface and are freely available to the
  composing fill. `sqrt_improvement'`'s `hC : 1 ≤ C` is implied by
  `hC_object : 129024 ≤ C` but is kept under the exact certified
  SqrtChain name and shape (flag-12 discipline). `hthr` is kept even
  though derivable from `hp : p.Prime` (flag 12, log|x| guard; any
  discharge lemma is a later, separate statement).

All twelve ambiguity flags below were adjudicated at freeze and are
honored by the statements as written; none required a change. Individual
adjudications: (1) honored — see quantifier audit; (2) honored — the
pointwise `S + {0,t}` form is used everywhere, byte-consistent with O5
flag 11 and note-v3 (4.5), no union form appears; (3) honored — both cap
premises are re-entered inside `hstep` at every invocation; (4) honored —
`D` is a fixed parameter of S8/S10, and the headline's `hstep`
quantification over `D` is instantiated once by the fill (docstring step
1), scale identity per O5 flag 10; (5) honored — see junk-value audit;
(6) honored — disjoint finsets with union `range j` are bookkeeping for
the exact counters, no ordering imposed; (7) honored — see
floor/ceiling audit; (8) ADJUDICATED: `Nat.minFac (Fintype.card G)` is
accepted as the `p(G)` model for the prime cyclic entry (equals the
least prime factor of `|G|`, hence `p` for `ZMod p`); naming a general
invariant is deferred beyond O6; (9) ADJUDICATED: the direct seam is
chosen — NO persistent `Balanced` predicate is introduced (a new frozen
definition would be a new trust boundary outside O6's charter, and the
direct inequality is exactly the seam `sqrt_improvement.hbalanced`
consumes); (10) honored — see seam audit, no scalar collapse; (11)
honored — `j = 0` immediate failure is terminal exactly as
note-v3-draft.md:721-723; (12) ADJUDICATED: `hthr` is KEPT as written
(project log|x| guard, third-incident precedent; discharge from
`hp.Prime` may later be a separate lemma, never an edit to this frozen
statement).

Composition status note (tier discipline): after fills, `sqrt_improvement'`
certifies `IsUSF A` + the explicit `hstep` re-entry interface (+ scalar
regime hypotheses) → `sqrt(M/404) < KA A`. The reconstruction of `hstep`'s
witnesses (`G2`, `sel`, `center`, `ρ`, `retained`, `hyDistinct`,
`HasSecondRemovalBound`, `IsOrientedRepresentationChoice`) from `IsUSF`
alone has NO skeleton in O1-O6 (O5 flags 2, 13, 14 record it as the
upstream obligation); the headline claim for the composed theorem is
therefore "kernel-certified from objects MODULO the stated one-bit step
interface", never an unconditional object-level certification.

Statement skeletons only. Every theorem body is `sorry`.

Charter: `candidates/bedert-omega/object-layer-charter.md:46-48`.
This file proposes the object-level seams for:

* the O1/O5 identification of `dimA A`, a chosen largest dissociated `D`,
  and the real scalar corresponding to `KA A`;
* one O5 one-bit bank becoming an actual next iterate;
* termination, the exact `htelescope` seam of
  `SqrtChain.one_bit_budget_steps` / `SqrtChain.sqrt_improvement`, and the
  exact `hgrowth` seam of `SqrtChain.one_bit_growth` /
  `SqrtChain.sqrt_improvement`;
* the `dimA A < 10` branch;
* the specialization `p = p(G)` for `G = ZMod p`;
* the object-level theorem `sqrt_improvement'`.

## Ambiguity flags (adjudicated at freeze; dispositions in the record above)

1. **State evolution between one-bit steps.** O5 proves one conditional step
   for supplied `G2`, `ρ`, `retained`, and the two bank conclusions. It does
   not construct those witnesses again for the next `S`. The universal
   `hstep` premise below exposes that reconstruction obligation. It must not be
   inferred from one fixed collection of O4/O5 witnesses.
2. **Where `S` grows.** The proposed state update is literally
   `Snext = S + {0,t}`, the pointwise form used by both O5 banks and
   note-v3 (4.5). An API using `S ∪ (S.image (· + t))` is propositionally
   equivalent when written with the same sign convention, but is not silently
   substituted here.
3. **Anchored-cap re-entry.** At every step, `hstep` is called only after both
   the rectification cap `(S.card : ℝ) ≤ log₂ p` and
   `FourthPowerCap A D S C` have been rechecked for the current `S`.
   O5's anchored data are therefore rebuilt under the current cap; they are
   not transported automatically from the previous step.
4. **Fixed versus evolving `D`.** The iteration keeps one largest
   dissociated `D ⊆ A` fixed. Allowing `D` to change would alter the scale
   identity and invalidate the stated telescope without additional
   bookkeeping.
5. **Junk values.** Every identification with `KA A` assumes
   `0 < dimA A`, exactly as required by the O1 junk-value note. No statement
   identifies the value `KA A = 0` in the zero-dimensional case with a
   positive scalar.
6. **Branch counters.** Outward and inward times are represented by disjoint
   finsets whose union is `range j`. This is only bookkeeping for the exact
   real counters `cT` and `fI`; it does not impose an ordering on branch
   choices beyond the iterate index.
7. **Strict inward gain.** O5's inward bank remains strict at each step. The
   telescope weakens it only at the final summation, matching
   `one_bit_budget_steps.htelescope`.
8. **The meaning of `p(G)`.** For the prime cyclic specialization it is
   proposed as `Nat.minFac (Fintype.card G)`. The theorem
   `p_eq_pG_zmod_proposed` records the entry `p = p(G)`. A later
   general-finite-Abelian-group API should name this invariant rather than
   duplicating the expression.
9. **Balancedness.** O1 has no `Balanced` predicate. The weak bound
   `log₂ p ≤ |A|` is therefore proposed directly from `IsUSF A` for `ZMod p`,
   citing Bedert's balancedness argument. Introducing a persistent
   object-level `Balanced` definition is a freeze-arm choice.
10. **O5 wall visibility.** The outward premise below is the conclusion of
    `outward_bank_from_objects_proposed`; the inward premise is the conclusion
    of `inward_bank_from_interfaces_proposed`, whose `hmass` route consumes
    `inward_mass_bound_from_objects_proposed` and the O5Multiplicity adapter.
    O6 does not collapse these into an unexplained scalar step.
11. **Immediate failure.** Termination permits `j = 0`. Then both counter
    finsets are empty, `S 0 = {0}`, and cap failure is already terminal, as in
    note-v3-draft.md:721-723.
12. **Prime positivity guard.** The final statement keeps `hthr` with exactly
    the `SqrtChain.sqrt_improvement` name and shape even though it should be
    derivable from `hp : p.Prime`. This preserves the project guard against
    Mathlib's `log |x|` convention until the freeze arm decides whether to
    discharge it in a separate lemma.
-/
import BedertLab.ObjectLayer.O5Banks

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## O1/O5 identification seam -/

/-- A dissociated subset of `A` has cardinality at most `dimA A`.

Charter: `object-layer-charter.md:22-26,46-48`.
Definition source: O1 `dimA`, which is the supremum of the cardinalities in
the filtered powerset. This is the upper-bound half of identifying a chosen
largest `D`; it discharges the maximality side deferred by O5 ambiguity flag
10. -/
theorem dissociated_card_le_dimA_proposed
    (A D : Finset G)
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D) :
    D.card ≤ dimA A := by
  unfold dimA
  exact Finset.le_sup (f := id) (Finset.mem_image.mpr
    ⟨D, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hDsubA, hD⟩, rfl⟩)

/-- The maximum in O1's finite definition of `dimA A` is attained.

Charter: `object-layer-charter.md:22-26,46-48`.
Definition source: O1 `dimA`.
Downstream: supplies the fixed `D` used by the O6 iteration and by the scale
identification below. -/
theorem exists_maximal_dissociated_proposed
    (A : Finset G) :
    ∃ D : Finset G,
      D ⊆ A ∧
        DissociatedF D ∧
          D.card = dimA A := by
  let candidates :=
    (A.powerset.filter fun D => DissociatedF D).image Finset.card
  have hcandidates : candidates.Nonempty := by
    refine ⟨0, ?_⟩
    simp [candidates, DissociatedF]
  obtain ⟨n, hn, hsup⟩ :=
    Finset.exists_mem_eq_sup candidates hcandidates id
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hn
  have hD' := Finset.mem_filter.mp hD
  exact ⟨D, Finset.mem_powerset.mp hD'.1, hD'.2, by
    simpa [dimA, candidates] using hsup.symm⟩

/-- The rational O1 definition of `KA` agrees, after coercion, with the real
cardinality ratio used by `SqrtChain`.

Charter: `object-layer-charter.md:46-48`.
O1 junk-value guard consumed: `hdim`.
Downstream: identifies the scalar called `K` in O5 and
`SqrtChain.sqrt_improvement`. -/
theorem ka_eq_card_div_dimA_proposed
    (A : Finset G)
    (hdim : 0 < dimA A) :
    (KA A : ℝ) = (A.card : ℝ) / (dimA A : ℝ) := by
  simp [KA, Rat.cast_div, Rat.cast_natCast]

/-- A largest dissociated `D` gives the exact O5/SqrtChain scale identity
with `K = KA A`.

Charter: `object-layer-charter.md:46-48`.
Source display: Bedert author LaTeX `main.tex:497-498`,
`|D| = dim(A) = |A| / K(A)`.
Shared seam: this conclusion is exactly `hscale` in
`outward_bank_from_objects_proposed`,
`inward_bank_from_interfaces_proposed`, and
`SqrtChain.sqrt_improvement`. -/
theorem ka_scale_from_maximal_dissociated_proposed
    (A D : Finset G)
    (hDcard : D.card = dimA A)
    (hdim : 0 < dimA A) :
    (A.card : ℝ) = (KA A : ℝ) * (D.card : ℝ) := by
  rw [ka_eq_card_div_dimA_proposed A hdim, hDcard]
  field_simp

/-- Conversely, the real scalar in an O5 scale identity is forced to be the
coercion of `KA A` when `D` realizes `dimA A`.

Charter: `object-layer-charter.md:46-48`.
O5 ambiguity flag 10 consumed: `hscale`.
O1 junk-value guard consumed: `hdim`. -/
theorem ka_identification_from_scale_proposed
    (A D : Finset G) {K : ℝ}
    (hDcard : D.card = dimA A)
    (hdim : 0 < dimA A)
    (hscale : (A.card : ℝ) = K * (D.card : ℝ)) :
    K = (KA A : ℝ) := by
  have hDpos : (0 : ℝ) < D.card := by
    exact_mod_cast (hDcard.trans_gt hdim)
  have hKA :=
    ka_scale_from_maximal_dissociated_proposed A D hDcard hdim
  nlinarith

/-- The chosen largest dissociated subset gives the exact lower guard
`hK : 1 ≤ K` required by both O5 banks and `SqrtChain.sqrt_improvement`.

Charter: `object-layer-charter.md:46-48`.
The proof uses `hDsubA`, `hDcard`, and the guarded KA identification; it does
not assign meaning to the O1 junk value. -/
theorem one_le_ka_of_maximal_dissociated_proposed
    (A D : Finset G)
    (hDsubA : D ⊆ A)
    (hDcard : D.card = dimA A)
    (hdim : 0 < dimA A) :
    (1 : ℝ) ≤ (KA A : ℝ) := by
  rw [ka_eq_card_div_dimA_proposed A hdim]
  apply (one_le_div₀ (by exact_mod_cast hdim)).mpr
  exact_mod_cast hDcard ▸ Finset.card_le_card hDsubA

/-! ## One O5 bank becomes the next object state -/

/-- Compose the exact final O5 dichotomy into a next iterate.

Charter: `object-layer-charter.md:42-48`.
Source displays:

* outward shift, size, and gain: Bedert author LaTeX
  `main.tex:707-713`;
* inward equations: `main.tex:716-724`, with the repaired one-bit bank stated
  in note-v3-draft.md (3.6)-(3.11).

O5 hypotheses consumed:

* `houtwardBank` is exactly the conclusion of
  `outward_bank_from_objects_proposed`, after retaining the nonzero shift,
  one-bit size bound, and `d/(36K)` new-point bank;
* `hinwardBank` is exactly the conclusion of
  `inward_bank_from_interfaces_proposed`, whose interfaces are discharged by
  `inward_label_nonzero_from_objects_proposed`,
  `inward_successful_transfer_from_objects_proposed`,
  `inward_target_budget_from_objects_proposed`, and
  `inward_mass_bound_from_objects_proposed`.

The fill must invoke
`one_bit_branch_dichotomy_from_objects_proposed`. The output explicitly
creates `Snext`, preserves `0`, records `S ⊆ Snext`, and retains which of the
two exact banks was consumed. -/
theorem one_bit_iteration_step_from_O5_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G)) {K : ℝ}
    (h0 : (0 : G) ∈ S)
    (houtwardBank :
      ∀ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card →
        ∃ t : G,
          t ≠ 0 ∧
            (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
              (D.card : ℝ) / (36 * K) ≤
                ((((A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)).card :
                  ℕ) : ℝ))
    (hinwardBank :
      (∀ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card) →
        ∃ t : G,
          t ≠ 0 ∧
            (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
              (D.card : ℝ) / (49 * K) <
                ((((A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)).card :
                  ℕ) : ℝ)) :
    ∃ (t : G) (Snext : Finset G),
      t ≠ 0 ∧
        Snext = S + ({0, t} : Finset G) ∧
          (0 : G) ∈ Snext ∧
            S ⊆ Snext ∧
              Snext.card ≤ 2 * S.card ∧
                ((D.card : ℝ) / (36 * K) ≤
                    ((((A ∩ (D + Snext)) \ (D + S)).card : ℕ) : ℝ) ∨
                  (D.card : ℝ) / (49 * K) <
                    ((((A ∩ (D + Snext)) \ (D + S)).card : ℕ) : ℝ)) := by
  rcases one_bit_branch_dichotomy_from_objects_proposed
      A D S G2 ρ retained houtwardBank hinwardBank with hout | hin
  · obtain ⟨t, ht, hcard, hgain⟩ := hout
    have hsubset : S ⊆ S + ({0, t} : Finset G) :=
      Finset.subset_add_left S (by simp)
    exact ⟨t, S + ({0, t} : Finset G), ht, rfl,
      hsubset h0, hsubset, hcard, Or.inl hgain⟩
  · obtain ⟨t, ht, hcard, hgain⟩ := hin
    have hsubset : S ⊆ S + ({0, t} : Finset G) :=
      Finset.subset_add_left S (by simp)
    exact ⟨t, S + ({0, t} : Finset G), ht, rfl,
      hsubset h0, hsubset, hcard, Or.inr hgain⟩

/-! ## Object-level telescope and one-bit growth -/

/-- Disjoint new-point banks telescope to the exact scalar `htelescope`.

Charter: `object-layer-charter.md:46-48`.
Source display: note-v3-draft.md (4.2), lines 601-608.
Shared seam: the conclusion is byte-for-byte the mathematical shape of
`one_bit_budget_steps.htelescope` and `sqrt_improvement.htelescope`, with
`cT = outward.card`, `fI = inward.card`, `d = D.card`, and `n = A.card`.

O5 conclusions consumed by hypotheses:

* `houtward` consumes the `d/(36K)` new-point conclusion of the outward bank;
* `hinward` consumes the strict `d/(49K)` new-point conclusion of the inward
  bank;
* `hstep` consumes the common `Snext = S + {0,t}` conclusion, which makes
  banks from different times disjoint. -/
theorem htelescope_from_object_banks_proposed
    (A D : Finset G) {K : ℝ} {j : ℕ}
    (S : ℕ → Finset G) (shift : ℕ → G)
    (outward inward : Finset ℕ)
    (hpartition :
      Disjoint outward inward ∧
        outward ∪ inward = Finset.range j)
    (hstep :
      ∀ i < j,
        S (i + 1) = S i + ({0, shift i} : Finset G))
    (houtward :
      ∀ i ∈ outward,
        (D.card : ℝ) / (36 * K) ≤
          ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ))
    (hinward :
      ∀ i ∈ inward,
        (D.card : ℝ) / (49 * K) <
          ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ)) :
    (outward.card : ℝ) * ((D.card : ℝ) / (36 * K)) +
        (inward.card : ℝ) * ((D.card : ℝ) / (49 * K)) ≤
      (A.card : ℝ) := by
  let T : ℕ → Finset G := fun i => A ∩ (D + S i)
  let bank : ℕ → ℝ := fun i =>
    ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ)
  have hSmono (i : ℕ) (hi : i < j) : S i ⊆ S (i + 1) := by
    rw [hstep i hi]
    exact Finset.subset_add_left (S i) (by simp)
  have hTmono (i : ℕ) (hi : i < j) : T i ⊆ T (i + 1) := by
    exact Finset.inter_subset_inter (fun _ ha => ha)
      (Finset.add_subset_add_left (hSmono i hi))
  have hbank (i : ℕ) (hi : i < j) :
      bank i = (T (i + 1)).card - (T i).card := by
    have heq :
        (A ∩ (D + S (i + 1))) \ (D + S i) =
          T (i + 1) \ T i := by
      ext x
      simp only [T, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hcard :
        (T i).card ≤ (T (i + 1)).card :=
      Finset.card_le_card (hTmono i hi)
    simp only [bank, heq, Finset.card_sdiff_of_subset (hTmono i hi)]
    exact Nat.cast_sub hcard
  have hsum :
      ∑ i ∈ Finset.range j, bank i ≤ (A.card : ℝ) := by
    calc
      ∑ i ∈ Finset.range j, bank i =
          ∑ i ∈ Finset.range j,
            (((T (i + 1)).card : ℝ) - (T i).card) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hbank i (Finset.mem_range.mp hi)
      _ = ((T j).card : ℝ) - (T 0).card :=
        Finset.sum_range_sub (fun i => ((T i).card : ℝ)) j
      _ ≤ (A.card : ℝ) := by
        have hTA : (T j).card ≤ A.card :=
          Finset.card_le_card Finset.inter_subset_left
        have hTA' : ((T j).card : ℝ) ≤ A.card := by
          exact_mod_cast hTA
        have hT0 : (0 : ℝ) ≤ (T 0).card := by positivity
        linarith
  have houtsum :
      (outward.card : ℝ) * ((D.card : ℝ) / (36 * K)) ≤
        ∑ i ∈ outward, bank i := by
    calc
      (outward.card : ℝ) * ((D.card : ℝ) / (36 * K)) =
          ∑ _i ∈ outward, (D.card : ℝ) / (36 * K) := by simp
      _ ≤ ∑ i ∈ outward, bank i := by
        apply Finset.sum_le_sum
        intro i hi
        exact houtward i hi
  have hinsum :
      (inward.card : ℝ) * ((D.card : ℝ) / (49 * K)) ≤
        ∑ i ∈ inward, bank i := by
    calc
      (inward.card : ℝ) * ((D.card : ℝ) / (49 * K)) =
          ∑ _i ∈ inward, (D.card : ℝ) / (49 * K) := by simp
      _ ≤ ∑ i ∈ inward, bank i := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (hinward i hi)
  calc
    (outward.card : ℝ) * ((D.card : ℝ) / (36 * K)) +
        (inward.card : ℝ) * ((D.card : ℝ) / (49 * K)) ≤
      (∑ i ∈ outward, bank i) + ∑ i ∈ inward, bank i :=
        add_le_add houtsum hinsum
    _ = ∑ i ∈ outward ∪ inward, bank i :=
      (Finset.sum_union hpartition.1).symm
    _ = ∑ i ∈ Finset.range j, bank i := by rw [hpartition.2]
    _ ≤ (A.card : ℝ) := hsum

/-- The actual object iterates supply the exact one-bit `hgrowth` seam.

Charter: `object-layer-charter.md:46-48`.
Source display: note-v3-draft.md (4.5), lines 625-630.
Shared seam: this conclusion has exactly the shape of
`sqrt_improvement.hgrowth`; its proof must invoke
`SqrtChain.one_bit_growth` with `size i = (S i).card`.

O5 conclusion consumed: `hsize` is the common
`(S + {0,t}).card ≤ 2 * S.card` output of both banks. -/
theorem hgrowth_from_object_steps_proposed
    {j : ℕ} (S : ℕ → Finset G)
    (outward inward : Finset ℕ)
    (hstart : S 0 = {0})
    (hpartition :
      Disjoint outward inward ∧
        outward ∪ inward = Finset.range j)
    (hsize :
      ∀ i < j, (S (i + 1)).card ≤ 2 * (S i).card) :
    Real.logb 2 ((S j).card : ℝ) ≤
      (outward.card : ℝ) + (inward.card : ℝ) := by
  have hgrowth :
      Real.logb 2 ((S j).card : ℝ) ≤ (j : ℝ) :=
    one_bit_growth
      (size := fun i => (S i).card)
      (j := j)
      (by simp [hstart])
      hsize
  have hcard : outward.card + inward.card = j := by
    rw [← Finset.card_union_of_disjoint hpartition.1,
      hpartition.2, Finset.card_range]
  calc
    Real.logb 2 ((S j).card : ℝ) ≤ (j : ℝ) := hgrowth
    _ = (outward.card : ℝ) + (inward.card : ℝ) := by
      exact_mod_cast hcard.symm

/-! ## Termination under the re-entered object cap -/

/-- Starting at `{0}`, repeated object one-bit steps terminate at the first
failure of the original two-term cap and retain all data needed by the
telescope and growth lemmas.

Charter: `object-layer-charter.md:46-48`.
Source displays:

* cap and `d ≥ 10`: Bedert author LaTeX `main.tex:479-484`;
* start, iterative exhaustion, and first cap failure:
  `main.tex:497-503`;
* streamlined one-bit termination and disjoint new banks:
  note-v3-draft.md:601-648.

`hstep` is deliberately an explicit, universally quantified re-entry seam.
For each current `S`, its fill must reconstruct the O4/O5 data and invoke
`one_bit_iteration_step_from_O5_proposed`. It consumes the two O5 bank
conclusions at that current state. This is AMBIGUITY FLAGS 1 and 3, not an
assumption that one anchored witness persists forever.

The terminal `hcapFailure` conclusion exactly matches
`SqrtChain.sqrt_improvement.hcapFailure`.

Freeze note: `hDsubA` and `hscale` are not consumed by the termination
derivation itself (the budget arithmetic needing `hscale` lives in
SqrtChain); they are kept deliberately as interface documentation, per the
O5 freeze precedent on non-load-bearing hypotheses. -/
theorem object_iteration_termination_proposed
    [Fintype G]
    (A D : Finset G) {p K C : ℝ}
    (hDsubA : D ⊆ A)
    (hDnonempty : D.Nonempty)
    (hK : 1 ≤ K)
    (hC : 1 ≤ C)
    (hscale : (A.card : ℝ) = K * (D.card : ℝ))
    (hstep :
      ∀ S : Finset G,
        (0 : G) ∈ S →
          (S.card : ℝ) ≤ Real.logb 2 p →
            FourthPowerCap A D S C →
              ∃ t : G,
                t ≠ 0 ∧
                  (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
                    ((D.card : ℝ) / (36 * K) ≤
                        ((((A ∩ (D + (S + ({0, t} : Finset G)))) \
                          (D + S)).card : ℕ) : ℝ) ∨
                      (D.card : ℝ) / (49 * K) <
                        ((((A ∩ (D + (S + ({0, t} : Finset G)))) \
                          (D + S)).card : ℕ) : ℝ))) :
    ∃ (j : ℕ) (S : ℕ → Finset G) (shift : ℕ → G)
        (outward inward : Finset ℕ),
      S 0 = {0} ∧
        (Disjoint outward inward ∧
          outward ∪ inward = Finset.range j) ∧
        (∀ i < j,
          shift i ≠ 0 ∧
            S (i + 1) = S i + ({0, shift i} : Finset G) ∧
              (S (i + 1)).card ≤ 2 * (S i).card) ∧
        (∀ i ∈ outward,
          (D.card : ℝ) / (36 * K) ≤
            ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ)) ∧
        (∀ i ∈ inward,
          (D.card : ℝ) / (49 * K) <
            ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ)) ∧
        (0 : ℝ) < (S j).card ∧
        min
            (Real.logb 2 p)
            (((D.card : ℝ) ^ 6 /
              (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4)) <
          (S j).card := by
  classical
  let good : Finset G → Prop := fun S =>
    (S.card : ℝ) ≤ Real.logb 2 p ∧ FourthPowerCap A D S C
  let stepResult : Finset G → G → Prop := fun S₀ t =>
    t ≠ 0 ∧
      (S₀ + ({0, t} : Finset G)).card ≤ 2 * S₀.card ∧
        ((D.card : ℝ) / (36 * K) ≤
            ((((A ∩ (D + (S₀ + ({0, t} : Finset G)))) \
              (D + S₀)).card : ℕ) : ℝ) ∨
          (D.card : ℝ) / (49 * K) <
            ((((A ∩ (D + (S₀ + ({0, t} : Finset G)))) \
              (D + S₀)).card : ℕ) : ℝ))
  have hexistsShift (S₀ : Finset G) :
      ∃ t : G, ((0 : G) ∈ S₀ ∧ good S₀) → stepResult S₀ t := by
    by_cases h : (0 : G) ∈ S₀ ∧ good S₀
    · obtain ⟨t, ht⟩ := hstep S₀ h.1 h.2.1 h.2.2
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  let shiftOf : Finset G → G := fun S₀ =>
    Classical.choose (hexistsShift S₀)
  have hshiftOf (S₀ : Finset G) (h0 : (0 : G) ∈ S₀)
      (hgood : good S₀) : stepResult S₀ (shiftOf S₀) := by
    exact Classical.choose_spec (hexistsShift S₀) ⟨h0, hgood⟩
  let S : ℕ → Finset G := fun n =>
    Nat.rec ({0} : Finset G)
      (fun _ current =>
        current + ({0, shiftOf current} : Finset G)) n
  let shift : ℕ → G := fun i => shiftOf (S i)
  have hSstep (i : ℕ) :
      S (i + 1) = S i + ({0, shift i} : Finset G) := by
    simp [S, shift]
  have hzero (i : ℕ) : (0 : G) ∈ S i := by
    induction i with
    | zero =>
        simp [S]
    | succ i ih =>
        rw [hSstep i]
        exact (Finset.subset_add_left (S i) (by simp)) ih
  have hstepData (i : ℕ) (hgood : good (S i)) :
      shift i ≠ 0 ∧
        (S (i + 1)).card ≤ 2 * (S i).card ∧
          ((D.card : ℝ) / (36 * K) ≤
              ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ) ∨
            (D.card : ℝ) / (49 * K) <
              ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ)) := by
    have hi := hshiftOf (S i) (hzero i) hgood
    dsimp only [stepResult] at hi
    rw [← hSstep i] at hi
    simpa only [shift] using hi
  let T : ℕ → Finset G := fun i => A ∩ (D + S i)
  have hSmono (i : ℕ) : S i ⊆ S (i + 1) := by
    rw [hSstep i]
    exact Finset.subset_add_left (S i) (by simp)
  have hTmono (i : ℕ) : T i ⊆ T (i + 1) := by
    exact Finset.inter_subset_inter (fun _ ha => ha)
      (Finset.add_subset_add_left (hSmono i))
  have hDpos : (0 : ℝ) < D.card := by
    exact_mod_cast hDnonempty.card_pos
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hstrict (i : ℕ) (hgood : good (S i)) :
      (T i).card < (T (i + 1)).card := by
    have hgain := (hstepData i hgood).2.2
    have hbankpos :
        (0 : ℝ) <
          ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ) := by
      rcases hgain with hout | hin
      · exact lt_of_lt_of_le
          (div_pos hDpos (mul_pos (by norm_num) hKpos)) hout
      · exact lt_trans
          (div_pos hDpos (mul_pos (by norm_num) hKpos)) hin
    have heq :
        (A ∩ (D + S (i + 1))) \ (D + S i) =
          T (i + 1) \ T i := by
      ext x
      simp only [T, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hbankposNat : 0 < (T (i + 1) \ T i).card := by
      rw [heq] at hbankpos
      exact_mod_cast hbankpos
    rw [Finset.card_sdiff_of_subset (hTmono i)] at hbankposNat
    omega
  have hfailure :
      ∃ j : ℕ, j ≤ A.card ∧ ¬ good (S j) := by
    by_contra hnone
    push_neg at hnone
    have hmeasure :
        ∀ i : ℕ, i ≤ A.card + 1 → i ≤ (T i).card := by
      intro i hi
      induction i with
      | zero =>
          exact Nat.zero_le _
      | succ i ih =>
          have hiA : i ≤ A.card := by omega
          have hprev : i ≤ (T i).card := ih (by omega)
          have hinc : (T i).card < (T (i + 1)).card :=
            hstrict i (hnone i hiA)
          omega
    have hlarge : A.card + 1 ≤ (T (A.card + 1)).card :=
      hmeasure (A.card + 1) le_rfl
    have hbound : (T (A.card + 1)).card ≤ A.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  let j : ℕ := Nat.find hfailure
  have hj : j ≤ A.card ∧ ¬ good (S j) := by
    simpa only [j] using Nat.find_spec hfailure
  have hjgood (i : ℕ) (hi : i < j) : good (S i) := by
    by_contra hnot
    have hiA : i ≤ A.card := le_trans (Nat.le_of_lt hi) hj.1
    have hmin : ¬(i ≤ A.card ∧ ¬ good (S i)) := by
      apply Nat.find_min hfailure
      simpa only [j] using hi
    exact hmin ⟨hiA, hnot⟩
  let Out : ℕ → Prop := fun i =>
    (D.card : ℝ) / (36 * K) ≤
      ((((A ∩ (D + S (i + 1))) \ (D + S i)).card : ℕ) : ℝ)
  let outward : Finset ℕ := (Finset.range j).filter Out
  let inward : Finset ℕ := (Finset.range j).filter fun i => ¬Out i
  have hpartition :
      Disjoint outward inward ∧
        outward ∪ inward = Finset.range j := by
    constructor
    · rw [Finset.disjoint_left]
      intro i hiout hiin
      exact (Finset.mem_filter.mp hiin).2 (Finset.mem_filter.mp hiout).2
    · ext i
      simp only [outward, inward, Finset.mem_union, Finset.mem_filter,
        Finset.mem_range]
      tauto
  have hterminalSize : (0 : ℝ) < (S j).card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨0, hzero j⟩)
  have hcapFailure :
      min
          (Real.logb 2 p)
          (((D.card : ℝ) ^ 6 /
            (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4)) <
        (S j).card := by
    set_option maxHeartbeats 600000 in
    by_cases hrect : (S j).card ≤ Real.logb 2 p
    · have hfourthFail : ¬FourthPowerCap A D (S j) C :=
        fun hfourth => hj.2 ⟨hrect, hfourth⟩
      let ratio : ℝ :=
        (D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)
      have hratio_nonneg : 0 ≤ ratio := by
        dsimp [ratio]
        have hDcast : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
        have hAcast : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
        exact div_nonneg (pow_nonneg hDcast 6)
          (mul_nonneg (le_trans zero_le_one hC) (pow_nonneg hAcast 5))
      have hfourth :
          ratio < ((S j).card : ℝ) ^ 4 := by
        apply lt_of_not_ge
        intro hge
        apply hfourthFail
        exact hge
      have hrootpow :
          (ratio ^ ((1 : ℝ) / 4)) ^ 4 = ratio := by
        have hexponent :
            (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
        rw [hexponent]
        exact Real.rpow_inv_natCast_pow hratio_nonneg (by norm_num)
      have hroot :
          ratio ^ ((1 : ℝ) / 4) < (S j).card := by
        by_contra hnot
        have hsize_le :
            ((S j).card : ℝ) ≤ ratio ^ ((1 : ℝ) / 4) :=
          le_of_not_gt hnot
        have hpow_le :
            ((S j).card : ℝ) ^ 4 ≤
              (ratio ^ ((1 : ℝ) / 4)) ^ 4 :=
          pow_le_pow_left₀ (le_of_lt hterminalSize) hsize_le 4
        rw [hrootpow] at hpow_le
        exact (not_lt_of_ge hpow_le) hfourth
      exact min_lt_of_right_lt (by simpa only [ratio] using hroot)
    · exact min_lt_of_left_lt (lt_of_not_ge hrect)
  refine ⟨j, S, shift, outward, inward, ?_, hpartition, ?_, ?_, ?_,
    hterminalSize, hcapFailure⟩
  · simp [S]
  · intro i hi
    have hdata := hstepData i (hjgood i hi)
    exact ⟨hdata.1, hSstep i, hdata.2.1⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    have hinNot : ¬Out i := (Finset.mem_filter.mp hi).2
    rcases (hstepData i
      (hjgood i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))).2.2 with
      hout | hin
    · exact (hinNot hout).elim
    · exact hin

/-! ## The easy dimension branch and the prime-cyclic entry -/

/-- For a prime cyclic group, the natural-number model of `p(G)` is exactly
the prime modulus.

Charter: `object-layer-charter.md:46-48`.
Source line: Bedert author LaTeX `main.tex:498`, `p = p(G)`.
Here `p(G)` is proposed as the least prime factor of the finite group order,
`Nat.minFac (Fintype.card G)`. -/
theorem p_eq_pG_zmod_proposed
    {p : ℕ} [NeZero p] (hp : p.Prime) :
    Nat.minFac (Fintype.card (ZMod p)) = p := by
  rw [ZMod.card]
  exact hp.minFac_eq

/-- The weak balancedness input needed by the scalar chain, derived directly
from the O1 predicate `IsUSF` in the prime cyclic specialization.

Charter: `object-layer-charter.md:46-48`.
Source: Bedert author LaTeX `main.tex:282-303,337-341` proves that USF implies
balanced and that a balanced set in `ZMod p` has size at least
`log₂ p + 1`; `main.tex:506-512` consumes the weaker displayed inequality.
Shared seam: the conclusion is exactly `SqrtChain.sqrt_improvement.hbalanced`.

AMBIGUITY FLAG 9 adjudicated at freeze: the direct seam is chosen; no
persistent `Balanced` predicate is introduced.

Freeze note: `hdim` is load-bearing here beyond junk-value discipline. The
empty set is vacuously USF and vacuously balanced, and the source corollary
(`main.tex:337-341`) silently uses that a balanced set has two distinct
elements; `0 < dimA A` forces a nonzero element of `A` (a dissociated
singleton `{a}` requires `a ≠ 0`), which restores the corollary's regime. -/
theorem hbalanced_from_usf_zmod_proposed
    {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hUSF : IsUSF A)
    (hdim : 0 < dimA A) :
    Real.logb 2 (p : ℝ) ≤ (A.card : ℝ) := by
  classical
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨D, hDsubA, _, hDcard⟩ :=
      exists_maximal_dissociated_proposed A
    have hApos : 0 < A.card := by
      have hDpos : 0 < D.card := hDcard.trans_gt hdim
      exact lt_of_lt_of_le hDpos (Finset.card_le_card hDsubA)
    have hAone : (1 : ℝ) ≤ A.card := by exact_mod_cast hApos
    simpa using hAone
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpdvd : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdvd
    exact hp2 (Nat.le_antisymm hple hp.two_le)
  let Balanced : Finset (ZMod p) → Prop := fun B =>
    ∀ b ∈ B,
      ∃ c ∈ B, ∃ d ∈ B, c ≠ d ∧ c + d = b + b
  have hBalancedA : Balanced A := by
    intro a ha
    by_contra hnone
    have hunique : HasUniqueSum A (a + a) := by
      refine ⟨a, ha, a, ha, rfl, ?_⟩
      intro c hc d hd hsum
      have hcd : c = d := by
        by_contra hne
        exact hnone ⟨c, hc, d, hd, hne, hsum⟩
      have hca : c = a := by
        apply mul_left_cancel₀ htwo
        simpa only [two_mul, hcd] using hsum
      subst c
      subst d
      exact Or.inl ⟨rfl, rfl⟩
    exact hUSF (a + a) hunique
  obtain ⟨D, hDsubA, _, hDcard⟩ :=
    exists_maximal_dissociated_proposed A
  have hAnonempty : A.Nonempty := by
    have hDnonempty : D.Nonempty :=
      Finset.card_pos.mp (hDcard.trans_gt hdim)
    exact hDnonempty.mono hDsubA
  let cores : Finset (Finset (ZMod p)) :=
    A.powerset.filter fun B => B.Nonempty ∧ Balanced B
  have hcores : cores.Nonempty := by
    refine ⟨A, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (fun _ h => h), hAnonempty, hBalancedA⟩
  obtain ⟨B, hBcores, hBmin⟩ :=
    Finset.exists_min_image cores Finset.card hcores
  have hBdata := Finset.mem_filter.mp hBcores
  have hBsubA : B ⊆ A := Finset.mem_powerset.mp hBdata.1
  have hBnonempty : B.Nonempty := hBdata.2.1
  have hBalancedB : Balanced B := hBdata.2.2
  have hminimal (R : Finset (ZMod p))
      (hRnonempty : R.Nonempty) (hRbalanced : Balanced R)
      (hRsubB : R ⊆ B) :
      B.card ≤ R.card := by
    apply hBmin R
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hRsubB.trans hBsubA),
        hRnonempty, hRbalanced⟩
  let RelationData : ZMod p → ZMod p × ZMod p → Prop := fun b pair =>
    pair.1 ∈ B ∧ pair.2 ∈ B ∧ pair.1 ≠ pair.2 ∧
      pair.1 + pair.2 = b + b
  have hexistsRelation (b : ZMod p) :
      ∃ pair : ZMod p × ZMod p,
        b ∈ B → RelationData b pair := by
    by_cases hb : b ∈ B
    · obtain ⟨c, hc, d, hd, hcd, hsum⟩ := hBalancedB b hb
      exact ⟨(c, d), fun _ => ⟨hc, hd, hcd, hsum⟩⟩
    · exact ⟨(b, b), fun hb' => (hb hb').elim⟩
  let relationPair : ZMod p → ZMod p × ZMod p := fun b =>
    Classical.choose (hexistsRelation b)
  have hrelationPair (b : ZMod p) (hb : b ∈ B) :
      RelationData b (relationPair b) :=
    Classical.choose_spec (hexistsRelation b) hb
  let edge : ZMod p → ZMod p → Prop := fun b c =>
    b ∈ B ∧ (c = (relationPair b).1 ∨ c = (relationPair b).2)
  have hedge_left (b : ZMod p) (hb : b ∈ B) :
      edge b (relationPair b).1 := ⟨hb, Or.inl rfl⟩
  have hedge_right (b : ZMod p) (hb : b ∈ B) :
      edge b (relationPair b).2 := ⟨hb, Or.inr rfl⟩
  have hedge_mem {b c : ZMod p} (hbc : edge b c) : c ∈ B := by
    rcases hbc.2 with rfl | rfl
    · exact (hrelationPair b hbc.1).1
    · exact (hrelationPair b hbc.1).2.1
  let reachable (b : ZMod p) : Finset (ZMod p) :=
    B.filter fun c => Relation.ReflTransGen edge b c
  have hreachable_eq (b : ZMod p) (hb : b ∈ B) :
      reachable b = B := by
    have hbmem : b ∈ reachable b :=
      Finset.mem_filter.mpr ⟨hb, Relation.ReflTransGen.refl⟩
    have hreachBalanced : Balanced (reachable b) := by
      intro c hc
      have hc' := Finset.mem_filter.mp hc
      refine ⟨(relationPair c).1, ?_,
        (relationPair c).2, ?_, (hrelationPair c hc'.1).2.2.1,
        (hrelationPair c hc'.1).2.2.2⟩
      · exact Finset.mem_filter.mpr
          ⟨(hrelationPair c hc'.1).1,
            hc'.2.tail (hedge_left c hc'.1)⟩
      · exact Finset.mem_filter.mpr
          ⟨(hrelationPair c hc'.1).2.1,
            hc'.2.tail (hedge_right c hc'.1)⟩
    have hreachSub : reachable b ⊆ B := Finset.filter_subset _ _
    have hle : B.card ≤ (reachable b).card :=
      hminimal (reachable b) ⟨b, hbmem⟩ hreachBalanced hreachSub
    exact Finset.eq_of_subset_of_card_le hreachSub hle
  obtain ⟨root, hroot⟩ := hBnonempty
  have hreaches (b : ZMod p) (hb : b ∈ B) :
      Relation.ReflTransGen edge b root := by
    have hr : root ∈ reachable b := by
      rw [hreachable_eq b hb]
      exact hroot
    exact (Finset.mem_filter.mp hr).2
  let PathLen : ZMod p → ℕ → Prop := fun b n =>
    (b ∉ B ∧ n = 0) ∨
      ∃ l : List (ZMod p),
        l.length = n ∧
          List.IsChain edge (b :: l) ∧
            (b :: l).getLast? = some root
  have hexistsPathLen (b : ZMod p) : ∃ n, PathLen b n := by
    by_cases hb : b ∈ B
    · obtain ⟨l, hchain, hlast⟩ :=
        List.exists_isChain_cons_of_relationReflTransGen (hreaches b hb)
      refine ⟨l.length, Or.inr ⟨l, rfl, hchain, ?_⟩⟩
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil b l)]
      exact congrArg some hlast
    · exact ⟨0, Or.inl ⟨hb, rfl⟩⟩
  let dist : ZMod p → ℕ := fun b => Nat.find (hexistsPathLen b)
  have hdist_spec (b : ZMod p) (hb : b ∈ B) :
      ∃ l : List (ZMod p),
        l.length = dist b ∧
          List.IsChain edge (b :: l) ∧
            (b :: l).getLast? = some root := by
    have hspec := Nat.find_spec (hexistsPathLen b)
    change PathLen b (dist b) at hspec
    rcases hspec with houtside | hpath
    · exact (houtside.1 hb).elim
    · exact hpath
  have hdescend (b : ZMod p) (hb : b ∈ B) (hbr : b ≠ root) :
      ∃ c : ZMod p, edge b c ∧ dist c < dist b := by
    obtain ⟨l, hlen, hchain, hlast⟩ := hdist_spec b hb
    cases l with
    | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        exact (hbr hlast).elim
    | cons c tail =>
        have hchain' := List.isChain_cons_cons.mp hchain
        have hcB : c ∈ B := hedge_mem hchain'.1
        have hcpath : PathLen c tail.length := by
          right
          refine ⟨tail, rfl, hchain'.2, ?_⟩
          simpa only [List.getLast?_cons_cons] using hlast
        have hdist_le :
            dist c ≤ tail.length :=
          Nat.find_min' (hexistsPathLen c) hcpath
        refine ⟨c, hchain'.1, ?_⟩
        change (c :: tail).length = dist b at hlen
        simp only [List.length_cons] at hlen
        omega
  let M : ℕ := B.sup dist
  have hdist_le_M (b : ZMod p) (hb : b ∈ B) : dist b ≤ M := by
    exact Finset.le_sup (f := dist) hb
  let weight : ZMod p → ℕ := fun b => 2 ^ (M - dist b)
  have hweight_pos (b : ZMod p) : 0 < weight b := by
    exact pow_pos (by norm_num) _
  have hweight_gain (b : ZMod p) (hb : b ∈ B) (hbr : b ≠ root) :
      ∃ c : ZMod p, edge b c ∧
        2 * weight b ≤ weight c := by
    obtain ⟨c, hbc, hdist⟩ := hdescend b hb hbr
    have hcB : c ∈ B := hedge_mem hbc
    have hexponent :
        M - dist b + 1 ≤ M - dist c := by
      have hbM := hdist_le_M b hb
      have hcM := hdist_le_M c hcB
      omega
    have hpow :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hexponent
    refine ⟨c, hbc, ?_⟩
    simpa only [weight, pow_succ'] using hpow
  have hedge_relation {b c : ZMod p} (hbc : edge b c) :
      ∃ d ∈ B,
        c ≠ d ∧ c ≠ b ∧ d ≠ b ∧
          (c - root) + (d - root) =
            (b - root) + (b - root) := by
    have hpair := hrelationPair b hbc.1
    rcases hbc.2 with hc | hc
    · subst c
      refine ⟨(relationPair b).2, hpair.2.1, hpair.2.2.1, ?_, ?_, ?_⟩
      · intro hleft
        have hright : (relationPair b).2 = b := by
          apply add_left_cancel
          simpa only [hleft] using hpair.2.2.2
        exact hpair.2.2.1 (hleft.trans hright.symm)
      · intro hright
        have hleft : (relationPair b).1 = b := by
          apply add_right_cancel
          simpa only [hright] using hpair.2.2.2
        exact hpair.2.2.1 (hleft.trans hright.symm)
      · calc
          (relationPair b).1 - root + ((relationPair b).2 - root) =
              (relationPair b).1 + (relationPair b).2 -
                (root + root) := by abel
          _ = b + b - (root + root) := by rw [hpair.2.2.2]
          _ = b - root + (b - root) := by abel
    · subst c
      refine ⟨(relationPair b).1, hpair.1, hpair.2.2.1.symm, ?_, ?_, ?_⟩
      · intro hright
        have hleft : (relationPair b).1 = b := by
          apply add_right_cancel
          simpa only [hright] using hpair.2.2.2
        exact hpair.2.2.1 (hleft.trans hright.symm)
      · intro hleft
        have hright : (relationPair b).2 = b := by
          apply add_left_cancel
          simpa only [hleft] using hpair.2.2.2
        exact hpair.2.2.1 (hleft.trans hright.symm)
      · calc
          (relationPair b).2 - root + ((relationPair b).1 - root) =
              (relationPair b).1 + (relationPair b).2 -
                (root + root) := by abel
          _ = b + b - (root + root) := by rw [hpair.2.2.2]
          _ = b - root + (b - root) := by abel
  have hexistsOther : ∃ b ∈ B, b ≠ root := by
    obtain ⟨c, hc, d, hd, hcd, _⟩ := hBalancedB root hroot
    by_cases hcr : c = root
    · exact ⟨d, hd, fun hdr => hcd (hcr.trans hdr.symm)⟩
    · exact ⟨c, hc, hcr⟩
  obtain ⟨b₀, hb₀, hb₀root⟩ := hexistsOther
  have hu : b₀ - root ≠ 0 := sub_ne_zero.mpr hb₀root
  have hspan (y : ZMod p) :
      ∃ T ∈ B.powerset,
        ∑ x ∈ T, (x - root) = y := by
    let N : ℕ := (y / (b₀ - root)).val
    let Value : (ZMod p → Fin (N + 1)) → ZMod p := fun k =>
      ∑ b ∈ B, (k b).val • (b - root)
    let Mass : (ZMod p → Fin (N + 1)) → ℕ := fun k =>
      ∑ b ∈ B, (k b).val
    let Score : (ZMod p → Fin (N + 1)) → ℕ := fun k =>
      ∑ b ∈ B, (k b).val * weight b
    let Valid : (ZMod p → Fin (N + 1)) → Prop := fun k =>
      Value k = y ∧ Mass k = N
    let initial : ZMod p → Fin (N + 1) := fun b =>
      if b = b₀ then ⟨N, Nat.lt_succ_self N⟩ else 0
    have hinitial (b : ZMod p) :
        (initial b).val = if b = b₀ then N else 0 := by
      by_cases h : b = b₀ <;> simp [initial, h]
    have hNvalue : N • (b₀ - root) = y := by
      rw [nsmul_eq_mul]
      change
        (((y / (b₀ - root)).val : ℕ) : ZMod p) *
          (b₀ - root) = y
      rw [ZMod.natCast_zmod_val]
      exact div_mul_cancel₀ y hu
    have hinitialValue : Value initial = y := by
      simp_rw [Value, hinitial]
      simpa only [ite_smul, zero_nsmul, Finset.sum_ite_eq',
        if_pos hb₀] using hNvalue
    have hinitialMass : Mass initial = N := by
      simp_rw [Mass, hinitial]
      simp only [Finset.sum_ite_eq', if_pos hb₀]
    let vectors : Finset (ZMod p → Fin (N + 1)) :=
      Finset.univ.filter Valid
    have hvectors : vectors.Nonempty := by
      refine ⟨initial, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hinitialValue, hinitialMass⟩
    obtain ⟨k, hk, hmax⟩ :=
      Finset.exists_max_image vectors Score hvectors
    have hkvalid : Valid k := (Finset.mem_filter.mp hk).2
    change Value k = y ∧ Mass k = N at hkvalid
    let coeff : ZMod p → ℕ := fun b => (k b).val
    have hmass : ∑ b ∈ B, coeff b = N := by
      exact hkvalid.2
    have hkBinary (b : ZMod p) (hb : b ∈ B) (hbr : b ≠ root) :
        coeff b ≤ 1 := by
      by_contra hnot
      have hkb : 2 ≤ coeff b := by omega
      obtain ⟨c, hbc, hgain⟩ := hweight_gain b hb hbr
      have hcB : c ∈ B := hedge_mem hbc
      obtain ⟨d, hdB, hcd, hcb, hdb, htranslate⟩ :=
        hedge_relation hbc
      have hcb' : c ≠ b := hcb
      have hdb' : d ≠ b := hdb
      have hbc' : b ≠ c := hcb.symm
      have hbd' : b ≠ d := hdb.symm
      have hdc : d ≠ c := hcd.symm
      have hcBound : coeff c + 1 ≤ N := by
        have hle :
            coeff b + coeff c ≤ ∑ x ∈ B, coeff x := by
          calc
            coeff b + coeff c =
                ∑ x ∈ ({b, c} : Finset (ZMod p)), coeff x := by
                  simp [hbc']
            _ ≤ ∑ x ∈ B, coeff x :=
              Finset.sum_le_sum_of_subset (by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact hb
                · exact hcB)
        rw [hmass] at hle
        omega
      have hdBound : coeff d + 1 ≤ N := by
        have hle :
            coeff b + coeff d ≤ ∑ x ∈ B, coeff x := by
          calc
            coeff b + coeff d =
                ∑ x ∈ ({b, d} : Finset (ZMod p)), coeff x := by
                  simp [hbd']
            _ ≤ ∑ x ∈ B, coeff x :=
              Finset.sum_le_sum_of_subset (by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact hb
                · exact hdB)
        rw [hmass] at hle
        omega
      let coeff' : ZMod p → ℕ :=
        Function.update
          (Function.update
            (Function.update coeff b (coeff b - 2))
            c (coeff c + 1))
          d (coeff d + 1)
      have hcoeff'b : coeff' b = coeff b - 2 := by
        simp [coeff', hbd', hbc']
      have hcoeff'c : coeff' c = coeff c + 1 := by
        simp [coeff', hcd]
      have hcoeff'd : coeff' d = coeff d + 1 := by
        simp [coeff']
      have hcoeff'other (x : ZMod p)
          (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) :
          coeff' x = coeff x := by
        simp [coeff', hxb, hxc, hxd]
      have hcoeff'Bound (x : ZMod p) : coeff' x < N + 1 := by
        by_cases hxd : x = d
        · subst x
          rw [hcoeff'd]
          omega
        by_cases hxc : x = c
        · subst x
          rw [hcoeff'c]
          omega
        by_cases hxb : x = b
        · subst x
          rw [hcoeff'b]
          have hklt := (k b).isLt
          change coeff b < N + 1 at hklt
          omega
        · rw [hcoeff'other x hxb hxc hxd]
          exact (k x).isLt
      let k' : ZMod p → Fin (N + 1) := fun x =>
        ⟨coeff' x, hcoeff'Bound x⟩
      have hk'val (x : ZMod p) : (k' x).val = coeff' x := rfl
      let rest : Finset (ZMod p) := B \ {b, c, d}
      have hBdecomp :
          B = insert b (insert c (insert d rest)) := by
        ext x
        by_cases hxb : x = b
        · subst x
          simp [rest, hb]
        by_cases hxc : x = c
        · subst x
          simp [rest, hcB]
        by_cases hxd : x = d
        · subst x
          simp [rest, hdB]
        simp [rest, hxb, hxc, hxd]
      have hbRest : b ∉ rest := by
        intro hmem
        exact (Finset.mem_sdiff.mp hmem).2 (by simp)
      have hcRest : c ∉ rest := by
        intro hmem
        exact (Finset.mem_sdiff.mp hmem).2 (by simp)
      have hdRest : d ∉ rest := by
        intro hmem
        exact (Finset.mem_sdiff.mp hmem).2 (by simp)
      have hcTail : c ∉ insert d rest := by
        simp [hcd, hcRest]
      have hbTail : b ∉ insert c (insert d rest) := by
        simp [hbc', hbd', hbRest]
      have hcoeff'Rest :
          ∀ x ∈ rest, coeff' x = coeff x := by
        intro x hx
        have hx' := Finset.mem_sdiff.mp hx
        have hxnot : x ∉ ({b, c, d} : Finset (ZMod p)) := hx'.2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
        exact hcoeff'other x hxnot.1 hxnot.2.1 hxnot.2.2
      have hmass' : ∑ x ∈ B, coeff' x = N := by
        have hmass0 := hmass
        rw [hBdecomp] at hmass0 ⊢
        rw [Finset.sum_insert hbTail, Finset.sum_insert hcTail,
          Finset.sum_insert hdRest] at hmass0 ⊢
        rw [hcoeff'b, hcoeff'c, hcoeff'd]
        have hrest :
            ∑ x ∈ rest, coeff' x = ∑ x ∈ rest, coeff x := by
          apply Finset.sum_congr rfl
          exact hcoeff'Rest
        rw [hrest]
        omega
      have hreplaceValue :
          (coeff b - 2) • (b - root) +
                (coeff c + 1) • (c - root) +
              (coeff d + 1) • (d - root) =
            coeff b • (b - root) +
                coeff c • (c - root) +
              coeff d • (d - root) := by
        have hkbeq : coeff b = coeff b - 2 + 2 :=
          (Nat.sub_add_cancel hkb).symm
        have hsplit :
            coeff b • (b - root) =
              (coeff b - 2) • (b - root) +
                2 • (b - root) := by
          calc
            coeff b • (b - root) =
                (coeff b - 2 + 2) • (b - root) :=
              congrArg (fun n : ℕ => n • (b - root)) hkbeq
            _ = (coeff b - 2) • (b - root) +
                2 • (b - root) := add_nsmul _ _ _
        calc
          (coeff b - 2) • (b - root) +
                  (coeff c + 1) • (c - root) +
                (coeff d + 1) • (d - root) =
              ((coeff b - 2) • (b - root) +
                  coeff c • (c - root) +
                coeff d • (d - root)) +
                  ((c - root) + (d - root)) := by
                    simp only [add_nsmul, one_nsmul]
                    abel
          _ = ((coeff b - 2) • (b - root) +
                  coeff c • (c - root) +
                coeff d • (d - root)) +
                  ((b - root) + (b - root)) := by
                    rw [htranslate]
          _ = coeff b • (b - root) +
                  coeff c • (c - root) +
                coeff d • (d - root) := by
                    rw [hsplit]
                    simp only [two_nsmul]
                    ac_rfl
      have hvalue' : Value k' = y := by
        have hvalue0 := hkvalid.1
        change
          (∑ x ∈ B, coeff' x • (x - root)) = y
        change
          (∑ x ∈ B, coeff x • (x - root)) = y at hvalue0
        rw [hBdecomp] at hvalue0 ⊢
        rw [Finset.sum_insert hbTail, Finset.sum_insert hcTail,
          Finset.sum_insert hdRest] at hvalue0 ⊢
        rw [hcoeff'b, hcoeff'c, hcoeff'd]
        have hrest :
            ∑ x ∈ rest, coeff' x • (x - root) =
              ∑ x ∈ rest, coeff x • (x - root) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hcoeff'Rest x hx]
        rw [hrest]
        calc
          (coeff b - 2) • (b - root) +
                ((coeff c + 1) • (c - root) +
                  ((coeff d + 1) • (d - root) +
                    ∑ x ∈ rest, coeff x • (x - root))) =
              ((coeff b - 2) • (b - root) +
                  (coeff c + 1) • (c - root) +
                (coeff d + 1) • (d - root)) +
                  ∑ x ∈ rest, coeff x • (x - root) := by abel
          _ = (coeff b • (b - root) +
                  coeff c • (c - root) +
                coeff d • (d - root)) +
                  ∑ x ∈ rest, coeff x • (x - root) := by
                    rw [hreplaceValue]
          _ = coeff b • (b - root) +
                (coeff c • (c - root) +
                  (coeff d • (d - root) +
                    ∑ x ∈ rest, coeff x • (x - root))) := by abel
          _ = y := hvalue0
      have hscoreIncrease : Score k < Score k' := by
        change
          (∑ x ∈ B, coeff x * weight x) <
            ∑ x ∈ B, coeff' x * weight x
        rw [hBdecomp]
        rw [Finset.sum_insert hbTail, Finset.sum_insert hcTail,
          Finset.sum_insert hdRest, Finset.sum_insert hbTail,
          Finset.sum_insert hcTail, Finset.sum_insert hdRest]
        rw [hcoeff'b, hcoeff'c, hcoeff'd]
        have hrest :
            ∑ x ∈ rest, coeff' x * weight x =
              ∑ x ∈ rest, coeff x * weight x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hcoeff'Rest x hx]
        rw [hrest]
        have hkbeq : coeff b = coeff b - 2 + 2 :=
          (Nat.sub_add_cancel hkb).symm
        have hsplit :
            coeff b * weight b =
              (coeff b - 2) * weight b + 2 * weight b := by
          calc
            coeff b * weight b =
                (coeff b - 2 + 2) * weight b :=
              congrArg (fun n : ℕ => n * weight b) hkbeq
            _ = (coeff b - 2) * weight b +
                2 * weight b := Nat.add_mul _ _ _
        rw [hsplit]
        simp only [Nat.add_mul, one_mul]
        have hdpos := hweight_pos d
        omega
      have hk'valid : Valid k' := by
        exact ⟨hvalue', by
          change ∑ x ∈ B, coeff' x = N
          exact hmass'⟩
      have hk'vectors : k' ∈ vectors :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'valid⟩
      exact (not_lt_of_ge (hmax k' hk'vectors)) hscoreIncrease
    let T : Finset (ZMod p) :=
      B.filter fun b => b ≠ root ∧ coeff b = 1
    have hTsub : T ⊆ B := Finset.filter_subset _ _
    refine ⟨T, Finset.mem_powerset.mpr hTsub, ?_⟩
    have hsumEq :
        (∑ x ∈ T, (x - root)) =
          ∑ x ∈ B, coeff x • (x - root) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbr : b = root
      · subst b
        simp
      · have hbin := hkBinary b hb hbr
        have hzero_or_one : coeff b = 0 ∨ coeff b = 1 := by omega
        rcases hzero_or_one with hzero | hone
        · simp [hbr, hzero]
        · simp [hbr, hone]
    rw [hsumEq]
    exact hkvalid.1
  have hpow_card : p ≤ 2 ^ B.card := by
    let subsetSum : Finset (ZMod p) → ZMod p := fun T =>
      ∑ x ∈ T, (x - root)
    have huniv :
        Finset.image subsetSum B.powerset =
          (Finset.univ : Finset (ZMod p)) := by
      apply Finset.eq_univ_of_forall
      intro y
      obtain ⟨T, hT, hsum⟩ := hspan y
      exact Finset.mem_image.mpr ⟨T, hT, hsum⟩
    calc
      p = Fintype.card (ZMod p) := (ZMod.card p).symm
      _ = (Finset.image subsetSum B.powerset).card := by
        rw [huniv]
        simp
      _ ≤ B.powerset.card := Finset.card_image_le
      _ = 2 ^ B.card := Finset.card_powerset B
  have hBcard : B.card ≤ A.card := Finset.card_le_card hBsubA
  have hpowA : p ≤ 2 ^ A.card :=
    le_trans hpow_card
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hBcard)
  have hpreal : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpowreal : (0 : ℝ) < (2 : ℝ) ^ A.card :=
    pow_pos (by norm_num) _
  have hreal : (p : ℝ) ≤ (2 : ℝ) ^ A.card := by
    exact_mod_cast hpowA
  have hlog :=
    (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num)
      hpreal hpowreal).2 hreal
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  simpa using hlog

/-- The `dimA A < 10` base branch already implies the same square-root
conclusion as the main iteration.

Charter: `object-layer-charter.md:46-48`.
Source displays: Bedert author LaTeX `main.tex:497-498`; streamlined form
note-v3-draft.md (4.14), lines 713-721:
`K = n/d > n/10 ≥ 2^M/10`.
The conclusion is written in the exact form of
`SqrtChain.sqrt_improvement`, with `sqrtChainDenominator = 404`.

Shared hypotheses retained exactly: `hthr` and `hM10`.
The weak balancedness inequality is supplied by
`hbalanced_from_usf_zmod_proposed`. -/
theorem small_dim_sqrt_improvement_proposed
    {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hUSF : IsUSF A)
    (hdim : 0 < dimA A)
    (hthr : 0 < Real.logb 2 (p : ℝ))
    (hM10 : 10 ≤ Real.logb 2 (Real.logb 2 (p : ℝ)))
    (hd : dimA A < 10) :
    Real.sqrt
        (Real.logb 2 (Real.logb 2 (p : ℝ)) /
          sqrtChainDenominator) <
      (KA A : ℝ) := by
  let M : ℝ := Real.logb 2 (Real.logb 2 (p : ℝ))
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM10
  have hhalfpos : 0 < M / 2 := div_pos hMpos (by norm_num)
  have hloghalf :
      Real.log (M / 2) ≤ M / 2 - 1 :=
    Real.log_le_sub_one_of_pos hhalfpos
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogM :
      Real.log M = Real.log (M / 2) + Real.log 2 := by
    conv_lhs => rw [show M = (M / 2) * 2 by ring]
    rw [Real.log_mul (ne_of_gt hhalfpos) (by norm_num)]
  have hlogtwohalf : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogM_le : Real.log M ≤ Real.log 2 * M := by
    rw [hlogM]
    nlinarith
  have hM_le_pow : M ≤ (2 : ℝ) ^ M := by
    calc
      M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (Real.log 2 * M) :=
        Real.exp_le_exp.mpr hlogM_le
      _ = (2 : ℝ) ^ M :=
        (Real.rpow_def_of_pos (by norm_num) M).symm
  have hpow_pos : 0 < (2 : ℝ) ^ M :=
    Real.rpow_pos_of_pos (by norm_num) M
  have hpow_large : (10 : ℝ) ≤ (2 : ℝ) ^ M :=
    le_trans hM10 hM_le_pow
  have hsqrt_pow :
      Real.sqrt (M / sqrtChainDenominator) <
        (2 : ℝ) ^ M / 10 := by
    have hright : 0 < (2 : ℝ) ^ M / 10 := div_pos hpow_pos (by norm_num)
    rw [Real.sqrt_lt' hright]
    dsimp [sqrtChainDenominator]
    nlinarith [sq_nonneg ((2 : ℝ) ^ M)]
  have hbalanced :=
    hbalanced_from_usf_zmod_proposed hp A hUSF hdim
  have hpow_eq :
      (2 : ℝ) ^ M = Real.logb 2 (p : ℝ) := by
    dsimp [M]
    exact Real.rpow_logb (by norm_num) (by norm_num) hthr
  have hcardpos : (0 : ℝ) < A.card :=
    lt_of_lt_of_le hthr hbalanced
  have hdimpos : (0 : ℝ) < dimA A := by exact_mod_cast hdim
  have hdimlt : ((dimA A : ℕ) : ℝ) < 10 := by exact_mod_cast hd
  have hratio :
      (A.card : ℝ) / 10 <
        (A.card : ℝ) / (dimA A : ℝ) :=
    (div_lt_div_iff_of_pos_left hcardpos (by norm_num) hdimpos).mpr hdimlt
  rw [ka_eq_card_div_dimA_proposed A hdim]
  calc
    Real.sqrt
        (Real.logb 2 (Real.logb 2 (p : ℝ)) /
          sqrtChainDenominator) =
        Real.sqrt (M / sqrtChainDenominator) := by rfl
    _ < (2 : ℝ) ^ M / 10 := hsqrt_pow
    _ ≤ (A.card : ℝ) / 10 := by
      rw [hpow_eq]
      exact div_le_div_of_nonneg_right hbalanced (by norm_num)
    _ < (A.card : ℝ) / (dimA A : ℝ) := hratio

/-! ## Object-level composition -/

/-- Object-level square-root improvement for a no-unique-sum subset of
`ZMod p`.

Charter: `object-layer-charter.md:46-48,58-60`.
Conclusion: exactly `SqrtChain.sqrt_improvement`, but with its scalar `K`
identified as `(KA A : ℝ)` and its scalar `p` identified with the prime
cyclic `p(G)` by `p_eq_pG_zmod_proposed`.

The proof skeleton must:

1. choose `D` with `D.card = dimA A` using
   `exists_maximal_dissociated_proposed`;
2. use `small_dim_sqrt_improvement_proposed` when `dimA A < 10`;
3. otherwise derive the exact shared seams `hd`, `hK`, `hscale`, and
   `hbalanced`;
4. feed the universally quantified `hstep` into
   `object_iteration_termination_proposed`;
5. set `cT = outward.card` and `fI = inward.card`, obtaining the exact shared
   seams `hcT`, `hfI`, `htelescope`, `hgrowth`, `hterminalSize`, and
   `hcapFailure` from the object iteration;
6. invoke `SqrtChain.sqrt_improvement` with the retained exact hypothesis
   names `hthr`, `hM10`, `hMC`, and `hC`.

`hstep` is the only proposed re-entry interface in this headline statement.
Each of its instances consumes the conclusion of
`one_bit_iteration_step_from_O5_proposed`, hence ultimately one of the two O5
banks. It explicitly includes both current cap hypotheses. This preserves the
three expected ambiguity flags rather than silently selecting a state machine.

Source displays: the cap and maximal `D` are Bedert author LaTeX
`main.tex:479-484,497-503`; the outward bank is `main.tex:707-713`; the inward
equations are `main.tex:716-724`; the streamlined telescope, growth, terminal
alternatives, and constant `404` are note-v3-draft.md (4.2)-(4.13). -/
theorem sqrt_improvement'
    {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p)) {C : ℝ}
    (hUSF : IsUSF A)
    (hdim : 0 < dimA A)
    (hthr : 0 < Real.logb 2 (p : ℝ))
    (hM10 : 10 ≤ Real.logb 2 (Real.logb 2 (p : ℝ)))
    (hMC :
      2 * Real.logb 2 C ≤
        Real.logb 2 (Real.logb 2 (p : ℝ)))
    (hC : 1 ≤ C)
    (hC_object : 129024 ≤ C)
    (hstep :
      ∀ (D S : Finset (ZMod p)),
        D ⊆ A →
          DissociatedF D →
            D.card = dimA A →
              10 ≤ D.card →
                (0 : ZMod p) ∈ S →
                  (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
                    FourthPowerCap A D S C →
                      ∃ t : ZMod p,
                        t ≠ 0 ∧
                          (S + ({0, t} : Finset (ZMod p))).card ≤
                            2 * S.card ∧
                          ((D.card : ℝ) / (36 * (KA A : ℝ)) ≤
                              ((((A ∩
                                  (D + (S + ({0, t} : Finset (ZMod p))))) \
                                (D + S)).card : ℕ) : ℝ) ∨
                            (D.card : ℝ) / (49 * (KA A : ℝ)) <
                              ((((A ∩
                                  (D + (S + ({0, t} : Finset (ZMod p))))) \
                                (D + S)).card : ℕ) : ℝ))) :
    Real.sqrt
        (Real.logb 2 (Real.logb 2 (p : ℝ)) /
          sqrtChainDenominator) <
      (KA A : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨D, hDsubA, hD, hDcard⟩ :=
    exists_maximal_dissociated_proposed A
  by_cases hsmall : dimA A < 10
  · exact small_dim_sqrt_improvement_proposed
      hp A hUSF hdim hthr hM10 hsmall
  have hdNat : 10 ≤ D.card := by omega
  have hd : (10 : ℝ) ≤ D.card := by exact_mod_cast hdNat
  have hDnonempty : D.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 10) hdNat)
  have hK : (1 : ℝ) ≤ (KA A : ℝ) :=
    one_le_ka_of_maximal_dissociated_proposed
      A D hDsubA hDcard hdim
  have hscale :
      (A.card : ℝ) = (KA A : ℝ) * (D.card : ℝ) :=
    ka_scale_from_maximal_dissociated_proposed A D hDcard hdim
  have hbalanced :
      Real.logb 2 (p : ℝ) ≤ (A.card : ℝ) :=
    hbalanced_from_usf_zmod_proposed hp A hUSF hdim
  obtain ⟨j, S, shift, outward, inward, hstart, hpartition,
      hsteps, houtward, hinward, hterminalSize, hcapFailure⟩ :=
    object_iteration_termination_proposed
      A D hDsubA hDnonempty hK hC hscale
      (fun S h0 hrect hcap =>
        hstep D S hDsubA hD hDcard hdNat h0 hrect hcap)
  have htelescope :
      (outward.card : ℝ) *
            ((D.card : ℝ) / (36 * (KA A : ℝ))) +
          (inward.card : ℝ) *
            ((D.card : ℝ) / (49 * (KA A : ℝ))) ≤
        (A.card : ℝ) :=
    htelescope_from_object_banks_proposed
      A D S shift outward inward hpartition
      (fun i hi => (hsteps i hi).2.1) houtward hinward
  have hgrowth :
      Real.logb 2 ((S j).card : ℝ) ≤
        (outward.card : ℝ) + (inward.card : ℝ) :=
    hgrowth_from_object_steps_proposed
      S outward inward hstart hpartition
      (fun i hi => (hsteps i hi).2.2)
  exact sqrt_improvement
    (p := (p : ℝ))
    (terminalSize := ((S j).card : ℝ))
    (d := (D.card : ℝ))
    (n := (A.card : ℝ))
    (K := (KA A : ℝ))
    (C := C)
    (cT := (outward.card : ℝ))
    (fI := (inward.card : ℝ))
    hthr hM10 hMC hterminalSize hd hK hC
    (by positivity) (by positivity) hscale hbalanced
    htelescope hgrowth hcapFailure

end ObjectLayer
end BedertLab
