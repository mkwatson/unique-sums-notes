/-
# Object layer, O4: star-extraction interface

FROZEN 2026-07-24 by the Claude freeze arm — fill sorries only; BLOCKED if
unprovable as written.

Charter: candidates/bedert-omega/object-layer-charter.md, phase O4.
Grounding:

* `ObjectLayer/O1Defs.lean`, `O2Budget.lean`, and `O3GoodPair.lean`;
* `LemmaFCore.lean`, especially `lemmaF_core_sharp`;
* candidates/bedert-omega/conjecture-51-v2.md, Section 1;
* sources/bedert/src/main.tex:624-704.

## Freeze record (2026-07-24, Claude freeze arm)

Checklist run (reference/claim-checklists.md, counting-lemma + pricing-chain
items; verification-battery freeze-gate addendum):

* Quantifier audit: every statement diffed against its source display
  (main.tex 624-716 `manygood`/`largeN(a)sum`/`mathcalNdefinition`/the
  N(1/3) display/`smallbaad`/the sigma multiplicity-and-range argument;
  conjecture-51-v2.md (1.2), (1.8)-(1.12)). Per-g multiplicity in
  `sigma_multiplicity_le_proposed` is deliberately per-value (∀ g), not a
  global sum bound (the B-S3 trap); the global bound is composed in
  `lemmaF_hbad_from_objects_proposed` via `sigmaRange_card_le_proposed`.
* Floor-vs-ceiling directions: `hmany`/`hmass` are floors (≤ from below),
  `hbad`/`sigmaRange` are packing ceilings (≤ from above),
  `countingTriples_card_lower_proposed` encodes (2.2) as
  `∑ q² ≤ 3|T|` — the floor on |T|, never an upper bound. All directions
  match the sources.
* Seam-constant audit against `lemmaF_core_sharp`: `hmass` shape
  `d²/3 ≤ ∑ q`, `hbad` shape `3 * C₁ * n² * S⁴` with `C₁ = 63` (matching
  the certified `two_families_pairs : k ≤ 63`), `hS4` shape
  `S⁴ ≤ d⁶/(C n⁵)`, `hstarcap` shape `q ≤ 3(d-1)`, `hcard` shape
  `|labels| ≤ n`, campaign contract `129024 = 2048·63 ≤ C`
  (constant-C-interface.md, weak form), conclusion constants `d²/7`,
  `d/21`. The filter set in the `hbad` discharge equals
  `(s \ star).filter (threshold)` byte-for-byte at the LemmaFCore seam.
* Vacuity/witness audit: each fragment theorem's hypothesis set has a
  concrete witness (e.g. `S = {0}`, `A = D` a large dissociated set,
  `G2 = binom(D,2)` satisfies `hsecond`; `G2 = ∅` satisfies `hρ`). The
  full composition `star_extraction_sharp_proposed` inherits the source
  proposition's hypothesis set verbatim; joint satisfiability of
  `hρ` + `hsecond` is grounded in conjecture-51-v2.md sec 1.4
  (𝔛(𝔖) ≠ ∅ under no-unique-sum), a prose fact, deliberately NOT assumed
  here — the theorems are conditional counting lemmas, faithful to the
  source proposition's own conditional form.
* Junk-value audit: all divisions are real and either guarded
  (`hd : 10 ≤ D.card`, `hDsubA` giving `n ≥ d ≥ 10`, `hC : 129024 ≤ C`)
  or collapse harmlessly (empty `A` empties `fibreLabels`, making both
  sides of the `hbad` discharge 0). No ℕ subtraction or ℕ division occurs
  in any statement; `3 * (d - 1)` is real subtraction with `d ≥ 1` forced
  by the star witness `u ∈ D`. `starFibres` clears the `q/3` denominator
  as `q ≤ 3·deg`, which is EXACT over ℚ (flag 11), not a weakening.
* Constant recomputation: `d²/3 ≤ |G2|` at `C = 129024` was re-derived
  from scratch: `63s⁴ ≤ d/2048` from the cap and `d ≤ n`, so
  `binom(d - 63s⁴, 2) - 63s⁴ - d·s⁴ ≥ 0.4995d² - 0.5003d - d²/129024
  ≥ d²/3` for `d ≥ 10` with wide slack (source only claims "sufficiently
  large C"; the exact constant is the campaign's, per
  constant-C-interface.md).

Statements changed at freeze: NONE. All sixteen ambiguity flags below were
adjudicated as recorded; in particular flag 7 (the `sigmaRange` grouping is
semantically the source set, since pointwise add/sub is associative and
commutative), flag 9 (campaign weak contract, not the source strict one),
and flag 11 (exact integer clearing) were re-verified rather than assumed.

## Ambiguity flags (adjudicated at freeze; dispositions as recorded)

1. The O4 charter says that O3 supplies `B2`, `G2`, and
   `|G2| >= d^2 / 3`, but the certified `O3GoodPair.lean` currently stops
   after `badOne_card_le`; it contains no second-removal definition or theorem.
   `HasSecondRemovalBound` therefore exposes the missing O3 contract as a
   hypothesis. It is not certified O3 output.
2. Neither the charter nor the existing Lean layer fixes a type for unordered
   pairs. This proposal represents a pair by a two-element `Finset G` and uses
   `D.powersetCard 2`.
3. Conjecture 5.1' separates an unordered quotient-valued representation
   choice `rho` from an orientation rule `omega`. The task asks for a
   representation-choice function as data. `RepresentationChoice` combines
   those two choices into one oriented function `Finset G -> G × G`.
4. The source defines `N(a)` for `a in A`, while Conjecture 5.1' writes it for
   `a in A \ (D + S)`. Here `fibreN` and `fibreCount` are total in `a`, and
   `fibreLabels` is the summation domain `A \ (D + S)`.
5. O1-O3 do not formalize the admissible source selector, its simultaneous
   uniqueness property, `B2`, the good-pair uniqueness lemma, or the existence
   of a noncanonical oriented representation from `IsUSF`.
   `IsOrientedRepresentationChoice` records only the consequences O4 uses.
   A later layer must prove that predicate from the missing source objects.
6. The paper's `T` counts ordered triples `(a, P, Q)`: `P` is chosen first and
   then `Q` is counted. `countingTriples` retains that ordering. Quotienting by
   `(P, Q) ~ (Q, P)` would change constants.
7. The paper writes the syndrome range as `A - A + 2S - 2S` without Lean
   parentheses. `sigmaRange` chooses `(A - A) + twoSsub S`, where
   `twoSsub S = S + S - S - S` is the frozen O3 definition.
8. The certified `two_families_pairs` fixes the natural-number multiplicity
   constant at `63`, whereas `lemmaF_core_sharp` has a real parameter `C₁`.
   This proposal instantiates `C₁ = 63` and consequently assumes
   `129024 = 2048 * 63 <= C`.
9. Bedert's printed source asks for the strict choice `C > 2048 C₁`; the
   campaign interface supports the weak condition `2048 C₁ <= C`. The final
   bridge below uses the campaign condition, not the source-only condition.
10. The source cap is stated with a fourth root. O1-O3 contain no cap object,
    so `FourthPowerCap` starts from the already-raised inequality required by
    `LemmaFCore.hS4`. A future source-object layer must justify raising the
    root-form cap and its sign side conditions.
11. The source writes the star condition as degree at least `q_a / 3`.
    `starFibres` clears the natural-number denominator as
    `q_a <= 3 * degree`. This exact integer interpretation must be frozen
    deliberately.
12. `LemmaFCore` accepts an abstract `star`. Here `starFibres` means the heavy
    fibres with a qualifying centre, matching `H_chi` in Conjecture 5.1'.
    Including light centred fibres instead would give a different set while
    still satisfying part of the abstract interface.
13. The source group is finite and the conjecture first targets `ZMod p`;
    O1-O3 are stated for an arbitrary additive commutative group using finite
    subsets. This proposal follows O1-O3 and does not add `Fintype G` or
    prime-cyclic hypotheses.
14. The names `d`, `n`, and `S` in `LemmaFCore` denote real scalar sizes.
    This proposal specializes them to the casts of `D.card`, `A.card`, and
    `S.card`. The fibre counts remain natural numbers until the interface
    inequalities cast them to `ℝ`.
15. The requested `hmass`, `hbad`, and `hS4` are not the whole
    `lemmaF_core_sharp` interface. The companion `hcard` and `hstarcap`
    statements are included so the final proposed composition has no hidden
    object-to-scalar assumptions.
16. The source choices are dependent functions whose domains are `D` or
    `G2`. Lean's `sel` and `RepresentationChoice` are total functions, with
    values off those finite domains ignored. Replacing them by subtype-indexed
    dependent functions would change the API and its extensionality lemmas.
-/
import BedertLab.LemmaFCore
import BedertLab.ObjectLayer.O3GoodPair

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- An oriented alternative-representation choice for every possible pair.
Only its restriction to `G2` is constrained. -/
abbrev RepresentationChoice (G : Type*) := Finset G → G × G

/-- The endpoint oriented outside `D + S`. -/
def chosenX (ρ : RepresentationChoice G) (P : Finset G) : G := (ρ P).1

/-- The other endpoint of the chosen representation. -/
def chosenY (ρ : RepresentationChoice G) (P : Finset G) : G := (ρ P).2

/-- The canonical sum attached to `P` by the source selector. -/
def pairTarget (sel : G → G) (P : Finset G) : G :=
  ∑ u ∈ P, (u + sel u)

/-- The object-level conditions on the combined representation and orientation
choice that are used by the O4 counting argument. -/
def IsOrientedRepresentationChoice (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G) : Prop :=
  (∀ u ∈ D, sel u ∈ S ∧ u + sel u ∈ A) ∧
    ∀ P ∈ G2,
      P ∈ D.powersetCard 2 ∧
        chosenX ρ P ∈ A \ (D + S) ∧
        chosenY ρ P ∈ A ∧
        chosenX ρ P + chosenY ρ P = pairTarget sel P

/-- The labels on which the source fibres partition `G2`. -/
def fibreLabels (A D S : Finset G) : Finset G := A \ (D + S)

/-- Source `N(a)`: the good pairs whose oriented first endpoint is `a`. -/
def fibreN (G2 : Finset (Finset G)) (ρ : RepresentationChoice G)
    (a : G) : Finset (Finset G) :=
  G2.filter fun P => chosenX ρ P = a

/-- Source `q_a = |N(a)|`. -/
def fibreCount (G2 : Finset (Finset G)) (ρ : RepresentationChoice G)
    (a : G) : ℕ :=
  (fibreN G2 ρ a).card

/-- The number of pairs in `N(a)` incident with `u`. -/
def fibreDegree (G2 : Finset (Finset G)) (ρ : RepresentationChoice G)
    (a u : G) : ℕ :=
  ((fibreN G2 ρ a).filter fun P => u ∈ P).card

/-- Source `mathcal N`: fibres at or above the `d² / (6n)` threshold. -/
noncomputable def heavyFibres (A D S : Finset G) (G2 : Finset (Finset G))
    (ρ : RepresentationChoice G) : Finset G :=
  (fibreLabels A D S).filter fun a =>
    (D.card : ℝ) ^ 2 / (6 * (A.card : ℝ)) ≤
      (fibreCount G2 ρ a : ℝ)

/-- Source `mathcal N(1/3)` / Conjecture 5.1' `H_chi`, with the denominator
cleared over natural numbers. -/
noncomputable def starFibres (A D S : Finset G) (G2 : Finset (Finset G))
    (ρ : RepresentationChoice G) : Finset G :=
  (heavyFibres A D S G2 ρ).filter fun a =>
    ∃ u ∈ D, fibreCount G2 ρ a ≤ 3 * fibreDegree G2 ρ a u

/-- Ordered counting triples `(a, P, Q)`. -/
abbrev CountingTriple (G : Type*) := G × (Finset G × Finset G)

/-- The source triple set over a supplied set of nonstar labels. -/
def countingTriples (bad : Finset G) (G2 : Finset (Finset G))
    (ρ : RepresentationChoice G) : Finset (CountingTriple G) :=
  (bad.product (G2.product G2)).filter fun t =>
    chosenX ρ t.2.1 = t.1 ∧
      chosenX ρ t.2.2 = t.1 ∧
      Disjoint t.2.1 t.2.2

/-- The source syndrome map
`sigma(a, P, Q) = sum(P) - sum(Q)`. -/
def sigmaMap (t : CountingTriple G) : G :=
  (∑ u ∈ t.2.1, u) - ∑ u ∈ t.2.2, u

/-- The finite-set version of the source syndrome range. -/
def sigmaRange (A S : Finset G) : Finset G := A - A + twoSsub S

/-- The fourth-power form of the Proposition 6 cap. -/
def FourthPowerCap (A D S : Finset G) (C : ℝ) : Prop :=
  (S.card : ℝ) ^ 4 ≤
    (D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)

/-- Temporary contract for the O3 second removal that is absent from the
current certified O3 file. -/
def HasSecondRemovalBound (D S : Finset G)
    (G2 : Finset (Finset G)) : Prop :=
  G2 ⊆ (goodOne D S).powersetCard 2 ∧
    (((goodOne D S).powersetCard 2) \ G2).card ≤
      63 * S.card ^ 4 + D.card * S.card ^ 4

/-- Proposed O3-to-O4 mass statement. The fill must use
`badOne_card_le` together with the future second-removal theorem encoded by
`HasSecondRemovalBound`. -/
theorem goodPair_card_lower_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) {C : ℝ}
    (hDsubA : D ⊆ A) (hD : DissociatedF D)
    (h0 : (0 : G) ∈ S) (hd : 10 ≤ D.card)
    (hC : 129024 ≤ C) (hcap : FourthPowerCap A D S C)
    (hsecond : HasSecondRemovalBound D S G2) :
    (D.card : ℝ) ^ 2 / 3 ≤ (G2.card : ℝ) := by
  classical
  have hS_card_pos : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
  have hd_pos : 0 < (D.card : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hn_pos : 0 < (A.card : ℝ) := by
    exact lt_of_lt_of_le hd_pos (by exact_mod_cast Finset.card_le_card hDsubA)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hdn : (D.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hDsubA
  have hdn5 : (D.card : ℝ) ^ 5 ≤ (A.card : ℝ) ^ 5 := by
    gcongr
  have hden :
      129024 * (D.card : ℝ) ^ 5 ≤ C * (A.card : ℝ) ^ 5 := by
    calc
      129024 * (D.card : ℝ) ^ 5 ≤ C * (D.card : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ C * (A.card : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hdn5 hC_pos.le
  have hcap_mul :
      (S.card : ℝ) ^ 4 * (C * (A.card : ℝ) ^ 5) ≤
        (D.card : ℝ) ^ 6 := by
    exact (le_div_iff₀ (mul_pos hC_pos (by positivity))).mp hcap
  have hS4small :
      (S.card : ℝ) ^ 4 ≤ (D.card : ℝ) / 129024 := by
    apply (le_div_iff₀ (by norm_num)).2
    have hmul := mul_le_mul_of_nonneg_left hden
      (pow_nonneg hS_card_pos.le 4)
    have htotal :
        (S.card : ℝ) ^ 4 * (129024 * (D.card : ℝ) ^ 5) ≤
          (D.card : ℝ) ^ 6 :=
      hmul.trans hcap_mul
    nlinarith [show 0 < (D.card : ℝ) ^ 5 by positivity]
  have hbad_subset : badOne D S ⊆ D := by
    intro u hu
    exact (Finset.mem_filter.mp hu).1
  have hbad :
      ((badOne D S).card : ℝ) ≤ 63 * (S.card : ℝ) ^ 4 := by
    exact_mod_cast badOne_card_le D S hD
  have hgood_card :
      ((goodOne D S).card : ℝ) =
        (D.card : ℝ) - ((badOne D S).card : ℝ) := by
    rw [goodOne, Finset.cast_card_sdiff hbad_subset]
  have hgood_lower :
      (D.card : ℝ) - 63 * (S.card : ℝ) ^ 4 ≤
        ((goodOne D S).card : ℝ) := by
    linarith
  have h63S4 :
      63 * (S.card : ℝ) ^ 4 ≤ (D.card : ℝ) / 2000 := by
    nlinarith
  have hgood_lower' :
      99 * (D.card : ℝ) / 100 ≤ ((goodOne D S).card : ℝ) := by
    nlinarith
  have hgood_one : 1 ≤ ((goodOne D S).card : ℝ) := by
    nlinarith [show (10 : ℝ) ≤ (D.card : ℝ) by exact_mod_cast hd]
  have hpairs_card :
      (((goodOne D S).powersetCard 2).card : ℝ) =
        ((goodOne D S).card : ℝ) *
          (((goodOne D S).card : ℝ) - 1) / 2 := by
    rw [Finset.card_powersetCard, Nat.cast_choose_two]
  have hremoved :
      ((((goodOne D S).powersetCard 2) \ G2).card : ℝ) ≤
        63 * (S.card : ℝ) ^ 4 +
          (D.card : ℝ) * (S.card : ℝ) ^ 4 := by
    exact_mod_cast hsecond.2
  have hpartition :
      ((G2.card : ℝ) :
        ℝ) =
        (((goodOne D S).powersetCard 2).card : ℝ) -
          ((((goodOne D S).powersetCard 2) \ G2).card : ℝ) := by
    have h := Finset.cast_card_sdiff (R := ℝ) hsecond.1
    linarith
  have hpair_lower :
      (99 * (D.card : ℝ) / 100) *
          (99 * (D.card : ℝ) / 100 - 1) / 2 ≤
        (((goodOne D S).powersetCard 2).card : ℝ) := by
    rw [hpairs_card]
    have hfactor :
        0 ≤ (((goodOne D S).card : ℝ) -
              99 * (D.card : ℝ) / 100) *
            (((goodOne D S).card : ℝ) +
              99 * (D.card : ℝ) / 100 - 1) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have hDS4 :
      (D.card : ℝ) * (S.card : ℝ) ^ 4 ≤
        (D.card : ℝ) ^ 2 / 100000 := by
    have hmul := mul_le_mul_of_nonneg_left hS4small hd_pos.le
    nlinarith
  rw [hpartition, hpairs_card]
  rw [hpairs_card] at hpair_lower
  nlinarith [show (10 : ℝ) ≤ (D.card : ℝ) by exact_mod_cast hd]

/-- The fibres partition `G2` when the chosen first endpoint always lies in
the declared label set. -/
theorem fibre_mass_eq_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ) :
    ∑ a ∈ fibreLabels A D S, fibreCount G2 ρ a = G2.card := by
  classical
  symm
  simpa only [fibreCount, fibreN] using
    (Finset.card_eq_sum_card_fiberwise
      (s := G2) (t := fibreLabels A D S) (f := chosenX ρ)
      (fun P hP => (hρ.2 P hP).2.1))

/-- Object-level discharge of `lemmaF_core_sharp.hmass`. -/
theorem lemmaF_hmass_from_objects_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hmany : (D.card : ℝ) ^ 2 / 3 ≤ (G2.card : ℝ)) :
    (D.card : ℝ) ^ 2 / 3 ≤
      ∑ a ∈ fibreLabels A D S, (fibreCount G2 ρ a : ℝ) := by
  calc
    (D.card : ℝ) ^ 2 / 3 ≤ (G2.card : ℝ) := hmany
    _ = (∑ a ∈ fibreLabels A D S, fibreCount G2 ρ a : ℕ) := by
      exact_mod_cast (fibre_mass_eq_proposed A D S G2 sel ρ hρ).symm
    _ = ∑ a ∈ fibreLabels A D S, (fibreCount G2 ρ a : ℝ) := by
      norm_cast

/-- The syndrome map has multiplicity at most the certified constant `63`.
The fill must invoke `two_families_pairs`; this is a freeze requirement, not
an additional abstract hypothesis. -/
theorem sigma_multiplicity_le_proposed (D bad : Finset G)
    (G2 : Finset (Finset G)) (ρ : RepresentationChoice G)
    (hD : DissociatedF D) (hpairs : G2 ⊆ D.powersetCard 2) :
    ∀ g : G,
      ((countingTriples bad G2 ρ).filter fun t =>
        sigmaMap t = g).card ≤ 63 := by
  classical
  intro g
  let W := (countingTriples bad G2 ρ).filter fun t => sigmaMap t = g
  let e : Fin W.card ≃ W := W.equivFin.symm
  let t : Fin W.card → CountingTriple G := fun i => e i
  have htW (i : Fin W.card) : t i ∈ W := by
    change (e i : CountingTriple G) ∈ W
    exact (e i).property
  have ht_count (i : Fin W.card) :
      t i ∈ countingTriples bad G2 ρ :=
    (Finset.mem_filter.mp (htW i)).1
  have ht_sigma (i : Fin W.card) : sigmaMap (t i) = g :=
    (Finset.mem_filter.mp (htW i)).2
  have ht_product (i : Fin W.card) :
      t i ∈ bad.product (G2.product G2) :=
    (Finset.mem_filter.mp (ht_count i)).1
  have ht_left (i : Fin W.card) : (t i).2.1 ∈ G2 :=
    (Finset.mem_product.mp
      (Finset.mem_product.mp (ht_product i)).2).1
  have ht_right (i : Fin W.card) : (t i).2.2 ∈ G2 :=
    (Finset.mem_product.mp
      (Finset.mem_product.mp (ht_product i)).2).2
  have ht_chosen_left (i : Fin W.card) :
      chosenX ρ (t i).2.1 = (t i).1 :=
    (Finset.mem_filter.mp (ht_count i)).2.1
  have ht_disjoint (i : Fin W.card) :
      Disjoint (t i).2.1 (t i).2.2 :=
    (Finset.mem_filter.mp (ht_count i)).2.2.2
  change W.card ≤ 63
  apply two_families_pairs
      (fun i => (t i).2.1) (fun i => (t i).2.2)
  · intro i
    exact (Finset.mem_powersetCard.mp (hpairs (ht_left i))).2.le
  · intro i
    exact (Finset.mem_powersetCard.mp (hpairs (ht_right i))).2.le
  · exact ht_disjoint
  · intro i j hij
    by_contra hcross
    simp only [not_or, not_not] at hcross
    have hleft_i :
        (t i).2.1 ⊆ D :=
      (Finset.mem_powersetCard.mp (hpairs (ht_left i))).1
    have hright_i :
        (t i).2.2 ⊆ D :=
      (Finset.mem_powersetCard.mp (hpairs (ht_right i))).1
    have hleft_j :
        (t j).2.1 ⊆ D :=
      (Finset.mem_powersetCard.mp (hpairs (ht_left j))).1
    have hright_j :
        (t j).2.2 ⊆ D :=
      (Finset.mem_powersetCard.mp (hpairs (ht_right j))).1
    have hsum_diff :
        (∑ x ∈ (t i).2.1, x) - ∑ x ∈ (t i).2.2, x =
          (∑ x ∈ (t j).2.1, x) - ∑ x ∈ (t j).2.2, x := by
      exact (ht_sigma i).trans (ht_sigma j).symm
    have hsum_add :
        (∑ x ∈ (t i).2.1, x) + ∑ x ∈ (t j).2.2, x =
          (∑ x ∈ (t j).2.1, x) + ∑ x ∈ (t i).2.2, x :=
      sub_eq_sub_iff_add_eq_add.mp hsum_diff
    have hunion :
        (t i).2.1 ∪ (t j).2.2 = (t j).2.1 ∪ (t i).2.2 := by
      apply hD
      · rw [Finset.mem_powerset]
        exact Finset.union_subset hleft_i hright_j
      · rw [Finset.mem_powerset]
        exact Finset.union_subset hleft_j hright_i
      · simpa only [Finset.sum_union hcross.1,
          Finset.sum_union hcross.2] using hsum_add
    have hPiQi := ht_disjoint i
    have hPjQj := ht_disjoint j
    rw [Finset.disjoint_left] at hPiQi hPjQj
    have hleft_eq : (t i).2.1 = (t j).2.1 := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hx' : x ∈ (t j).2.1 ∪ (t i).2.2 := by
          rw [← hunion]
          exact Finset.mem_union_left _ hx
        rcases Finset.mem_union.mp hx' with hxj | hxiq
        · exact hxj
        · exact False.elim (hPiQi hx hxiq)
      · intro x hx
        have hx' : x ∈ (t i).2.1 ∪ (t j).2.2 := by
          rw [hunion]
          exact Finset.mem_union_left _ hx
        rcases Finset.mem_union.mp hx' with hxi | hxjq
        · exact hxi
        · exact False.elim (hPjQj hx hxjq)
    have hright_eq : (t i).2.2 = (t j).2.2 := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hx' : x ∈ (t i).2.1 ∪ (t j).2.2 := by
          rw [hunion]
          exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hx' with hxip | hxj
        · exact False.elim (hPiQi hxip hx)
        · exact hxj
      · intro x hx
        have hx' : x ∈ (t j).2.1 ∪ (t i).2.2 := by
          rw [← hunion]
          exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hx' with hxjp | hxi
        · exact False.elim (hPjQj hxjp hx)
        · exact hxi
    have ht_eq : t i = t j := by
      apply Prod.ext
      · rw [← ht_chosen_left i, ← ht_chosen_left j, hleft_eq]
      · exact Prod.ext hleft_eq hright_eq
    apply hij
    apply e.injective
    apply Subtype.ext
    exact ht_eq

/-- Every syndrome of a valid counting triple lies in the source range. -/
theorem sigma_mem_range_proposed (A D S : Finset G)
    (G2 pairs : Finset (Finset G)) (bad : Finset G)
    (sel : G → G) (ρ : RepresentationChoice G)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hpairs : pairs ⊆ G2) (t : CountingTriple G)
    (ht : t ∈ countingTriples bad pairs ρ) :
    sigmaMap t ∈ sigmaRange A S := by
  classical
  have ht_filter := Finset.mem_filter.mp ht
  have ht_product := Finset.mem_product.mp ht_filter.1
  have ht_pairs := Finset.mem_product.mp ht_product.2
  have hP_G2 : t.2.1 ∈ G2 := hpairs ht_pairs.1
  have hQ_G2 : t.2.2 ∈ G2 := hpairs ht_pairs.2
  obtain ⟨hP_pow, hxP, hyP, htargetP⟩ := hρ.2 t.2.1 hP_G2
  obtain ⟨hQ_pow, hxQ, hyQ, htargetQ⟩ := hρ.2 t.2.2 hQ_G2
  have hP_card : t.2.1.card = 2 :=
    (Finset.mem_powersetCard.mp hP_pow).2
  have hQ_card : t.2.2.card = 2 :=
    (Finset.mem_powersetCard.mp hQ_pow).2
  obtain ⟨p₁, p₂, hp_ne, hp_eq⟩ := Finset.card_eq_two.mp hP_card
  obtain ⟨q₁, q₂, hq_ne, hq_eq⟩ := Finset.card_eq_two.mp hQ_card
  have hp₁D : p₁ ∈ D := (Finset.mem_powersetCard.mp hP_pow).1 (by simp [hp_eq])
  have hp₂D : p₂ ∈ D := (Finset.mem_powersetCard.mp hP_pow).1 (by simp [hp_eq])
  have hq₁D : q₁ ∈ D := (Finset.mem_powersetCard.mp hQ_pow).1 (by simp [hq_eq])
  have hq₂D : q₂ ∈ D := (Finset.mem_powersetCard.mp hQ_pow).1 (by simp [hq_eq])
  have hp₁S : sel p₁ ∈ S := (hρ.1 p₁ hp₁D).1
  have hp₂S : sel p₂ ∈ S := (hρ.1 p₂ hp₂D).1
  have hq₁S : sel q₁ ∈ S := (hρ.1 q₁ hq₁D).1
  have hq₂S : sel q₂ ∈ S := (hρ.1 q₂ hq₂D).1
  have htargetP' :
      chosenX ρ t.2.1 + chosenY ρ t.2.1 =
        (∑ u ∈ t.2.1, u) + (sel p₁ + sel p₂) := by
    rw [htargetP]
    simp [pairTarget, hp_eq, hp_ne]
    abel
  have htargetQ' :
      chosenX ρ t.2.2 + chosenY ρ t.2.2 =
        (∑ u ∈ t.2.2, u) + (sel q₁ + sel q₂) := by
    rw [htargetQ]
    simp [pairTarget, hq_eq, hq_ne]
    abel
  have hsumP :
      (∑ u ∈ t.2.1, u) =
        chosenX ρ t.2.1 + chosenY ρ t.2.1 - (sel p₁ + sel p₂) := by
    calc
      (∑ u ∈ t.2.1, u) =
          ((∑ u ∈ t.2.1, u) + (sel p₁ + sel p₂)) -
            (sel p₁ + sel p₂) := by abel
      _ = chosenX ρ t.2.1 + chosenY ρ t.2.1 -
            (sel p₁ + sel p₂) := by rw [← htargetP']
  have hsumQ :
      (∑ u ∈ t.2.2, u) =
        chosenX ρ t.2.2 + chosenY ρ t.2.2 - (sel q₁ + sel q₂) := by
    calc
      (∑ u ∈ t.2.2, u) =
          ((∑ u ∈ t.2.2, u) + (sel q₁ + sel q₂)) -
            (sel q₁ + sel q₂) := by abel
      _ = chosenX ρ t.2.2 + chosenY ρ t.2.2 -
            (sel q₁ + sel q₂) := by rw [← htargetQ']
  have htwo :
      (sel q₁ + sel q₂) - (sel p₁ + sel p₂) ∈ twoSsub S := by
    unfold twoSsub
    rw [Finset.mem_sub]
    refine ⟨(sel q₁ + sel q₂) - sel p₁, ?_, sel p₂, hp₂S, by abel⟩
    rw [Finset.mem_sub]
    exact ⟨sel q₁ + sel q₂, Finset.add_mem_add hq₁S hq₂S,
      sel p₁, hp₁S, rfl⟩
  rw [sigmaRange, Finset.mem_add]
  refine ⟨chosenY ρ t.2.1 - chosenY ρ t.2.2,
    Finset.sub_mem_sub hyP hyQ,
    (sel q₁ + sel q₂) - (sel p₁ + sel p₂), htwo, ?_⟩
  unfold sigmaMap
  rw [hsumP, hsumQ, ht_filter.2.1, ht_filter.2.2.1]
  abel

/-- Crude cardinality bound for the syndrome range. -/
theorem sigmaRange_card_le_proposed (A S : Finset G) :
    (sigmaRange A S).card ≤ A.card ^ 2 * S.card ^ 4 := by
  have htwoSsub : (twoSsub S).card ≤ S.card ^ 4 := by
    unfold twoSsub
    calc
      (S + S - S - S).card ≤ (S + S - S).card * S.card :=
        Finset.card_sub_le
      _ ≤ ((S + S).card * S.card) * S.card := by
        gcongr
        exact Finset.card_sub_le
      _ ≤ ((S.card * S.card) * S.card) * S.card := by
        gcongr
        exact Finset.card_add_le
      _ = S.card ^ 4 := by ring
  unfold sigmaRange
  calc
    (A - A + twoSsub S).card ≤ (A - A).card * (twoSsub S).card :=
      Finset.card_add_le
    _ ≤ (A.card * A.card) * S.card ^ 4 := by
      gcongr
      exact Finset.card_sub_le
    _ = A.card ^ 2 * S.card ^ 4 := by ring

/-- Local ordered-disjoint-pair count for all heavy nonstar fibres. -/
theorem countingTriples_card_lower_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ) :
    ∑ a ∈ heavyFibres A D S G2 ρ \ starFibres A D S G2 ρ,
        fibreCount G2 ρ a ^ 2 ≤
      3 * (countingTriples
        (heavyFibres A D S G2 ρ \ starFibres A D S G2 ρ)
        G2 ρ).card := by
  classical
  let bad := heavyFibres A D S G2 ρ \ starFibres A D S G2 ρ
  let T := countingTriples bad G2 ρ
  have hlocal (a : G) (ha : a ∈ bad) :
      fibreCount G2 ρ a ^ 2 ≤
        3 * (T.filter fun t => t.1 = a).card := by
    let N := fibreN G2 ρ a
    let U := (N.product N).filter fun p => Disjoint p.1 p.2
    let I := (N.product N).filter fun p => ¬Disjoint p.1 p.2
    have ha_heavy : a ∈ heavyFibres A D S G2 ρ :=
      (Finset.mem_sdiff.mp ha).1
    have ha_notstar : a ∉ starFibres A D S G2 ρ :=
      (Finset.mem_sdiff.mp ha).2
    have hdegree (u : G) (hu : u ∈ D) :
        3 * fibreDegree G2 ρ a u < fibreCount G2 ρ a := by
      have hnot :
          ¬fibreCount G2 ρ a ≤ 3 * fibreDegree G2 ρ a u := by
        intro hlarge
        apply ha_notstar
        rw [starFibres, Finset.mem_filter]
        exact ⟨ha_heavy, u, hu, hlarge⟩
      omega
    have hJbound (P : Finset G) (hP : P ∈ N) :
        3 * (N.filter fun Q => ¬Disjoint P Q).card ≤
          2 * fibreCount G2 ρ a := by
      have hP_G2 : P ∈ G2 := (Finset.mem_filter.mp hP).1
      have hP_pow := (hρ.2 P hP_G2).1
      have hP_sub : P ⊆ D := (Finset.mem_powersetCard.mp hP_pow).1
      have hP_card : P.card = 2 := (Finset.mem_powersetCard.mp hP_pow).2
      have hcover :
          N.filter (fun Q => ¬Disjoint P Q) ⊆
            P.biUnion fun u => N.filter fun Q => u ∈ Q := by
        intro Q hQ
        have hQ' := Finset.mem_filter.mp hQ
        obtain ⟨u, huP, huQ⟩ := Finset.not_disjoint_iff.mp hQ'.2
        exact Finset.mem_biUnion.mpr
          ⟨u, huP, Finset.mem_filter.mpr ⟨hQ'.1, huQ⟩⟩
      have hintersect :
          (N.filter fun Q => ¬Disjoint P Q).card ≤
            ∑ u ∈ P, fibreDegree G2 ρ a u := by
        calc
          (N.filter fun Q => ¬Disjoint P Q).card ≤
              (P.biUnion fun u => N.filter fun Q => u ∈ Q).card :=
            Finset.card_le_card hcover
          _ ≤ ∑ u ∈ P, (N.filter fun Q => u ∈ Q).card :=
            Finset.card_biUnion_le
          _ = ∑ u ∈ P, fibreDegree G2 ρ a u := by
            simp only [N, fibreDegree]
      obtain ⟨u, v, huv, hP_eq⟩ := Finset.card_eq_two.mp hP_card
      have huD : u ∈ D := hP_sub (by simp [hP_eq])
      have hvD : v ∈ D := hP_sub (by simp [hP_eq])
      have hsumdegree :
          3 * (∑ x ∈ P, fibreDegree G2 ρ a x) <
            2 * fibreCount G2 ρ a := by
        have hsum_eq :
            (∑ x ∈ P, fibreDegree G2 ρ a x) =
              fibreDegree G2 ρ a u + fibreDegree G2 ρ a v := by
          rw [hP_eq]
          simp [huv]
        rw [hsum_eq]
        have hu_bound := hdegree u huD
        have hv_bound := hdegree v hvD
        omega
      omega
    have hI_fibre (P : Finset G) (hP : P ∈ N) :
        (I.filter fun p => p.1 = P).card =
          (N.filter fun Q => ¬Disjoint P Q).card := by
      have heq :
          I.filter (fun p => p.1 = P) =
            (({P} : Finset (Finset G)).product
              (N.filter fun Q => ¬Disjoint P Q)) := by
        ext p
        rcases p with ⟨P', Q⟩
        simp [I, and_assoc, and_comm]
        constructor
        · rintro ⟨rfl, hdisj, hpN, hQN⟩
          exact ⟨rfl, hdisj, hQN⟩
        · rintro ⟨hPP', hdisj, hQN⟩
          subst P'
          exact ⟨rfl, hdisj, hP, hQN⟩
      rw [heq]
      calc
        (({P} : Finset (Finset G)).product
            (N.filter fun Q => ¬Disjoint P Q)).card =
            ({P} : Finset (Finset G)).card *
              (N.filter fun Q => ¬Disjoint P Q).card :=
          Finset.card_product _ _
        _ = (N.filter fun Q => ¬Disjoint P Q).card := by simp
    have hIcard :
        I.card =
          ∑ P ∈ N, (N.filter fun Q => ¬Disjoint P Q).card := by
      calc
        I.card = ∑ P ∈ N, (I.filter fun p => p.1 = P).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro p hp
          exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        _ = ∑ P ∈ N, (N.filter fun Q => ¬Disjoint P Q).card := by
          apply Finset.sum_congr rfl
          exact hI_fibre
    have hIbound :
        3 * I.card ≤ 2 * fibreCount G2 ρ a ^ 2 := by
      calc
        3 * I.card =
            ∑ P ∈ N, 3 * (N.filter fun Q => ¬Disjoint P Q).card := by
          rw [hIcard]
          simp [Finset.mul_sum]
        _ ≤ ∑ _P ∈ N, 2 * fibreCount G2 ρ a := by
          apply Finset.sum_le_sum
          exact hJbound
        _ = 2 * fibreCount G2 ρ a ^ 2 := by
          simp [N, fibreCount]
          ring
    have hpartition :
        U.card + I.card = fibreCount G2 ρ a ^ 2 := by
      have hfilter :=
        Finset.card_filter_add_card_filter_not
          (s := N.product N) (fun p => Disjoint p.1 p.2)
      calc
        U.card + I.card = (N.product N).card := hfilter
        _ = N.card * N.card := Finset.card_product N N
        _ = fibreCount G2 ρ a ^ 2 := by
          simp [N, fibreCount, pow_two]
    have hUbound : fibreCount G2 ρ a ^ 2 ≤ 3 * U.card := by
      omega
    have hTfibre :
        (T.filter fun t => t.1 = a) =
          (({a} : Finset G).product U) := by
      ext t
      rcases t with ⟨a', P, Q⟩
      simp [T, U, N, countingTriples, fibreN,
        and_assoc, and_left_comm, and_comm]
      constructor
      · rintro ⟨rfl, hdisj, hPG2, hQG2, hxP, hxQ, _⟩
        exact ⟨rfl, hdisj, hPG2, hQG2, hxP, hxQ⟩
      · rintro ⟨haa', hdisj, hPG2, hQG2, hxP, hxQ⟩
        subst a'
        exact ⟨rfl, hdisj, hPG2, hQG2, hxP, hxQ, ha⟩
    have hcard_singleton :
        (({a} : Finset G).product U).card = U.card := by
      calc
        (({a} : Finset G).product U).card =
            ({a} : Finset G).card * U.card :=
          Finset.card_product _ _
        _ = U.card := by simp
    rw [hTfibre, hcard_singleton]
    exact hUbound
  change (∑ a ∈ bad, fibreCount G2 ρ a ^ 2) ≤ 3 * T.card
  have hTsum :
      (∑ a ∈ bad, (T.filter fun t => t.1 = a).card) = T.card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro t ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
  calc
    (∑ a ∈ bad, fibreCount G2 ρ a ^ 2) ≤
        ∑ a ∈ bad, 3 * (T.filter fun t => t.1 = a).card := by
      apply Finset.sum_le_sum
      exact hlocal
    _ = 3 * ∑ a ∈ bad, (T.filter fun t => t.1 = a).card := by
      simp [Finset.mul_sum]
    _ = 3 * T.card := by rw [hTsum]

/-- Object-level discharge of `lemmaF_core_sharp.hbad`, with
`C₁ = 63`. The intended fill composes the ordered-triple lower bound, the
`two_families_pairs` multiplicity bound, the syndrome image bound, and the
crude cardinality bound for `sigmaRange`. -/
theorem lemmaF_hbad_from_objects_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G) (hD : DissociatedF D)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ) :
    ∑ a ∈
        ((fibreLabels A D S \ starFibres A D S G2 ρ).filter fun a =>
          (D.card : ℝ) ^ 2 / (6 * (A.card : ℝ)) ≤
            (fibreCount G2 ρ a : ℝ)),
        (fibreCount G2 ρ a : ℝ) ^ 2 ≤
      3 * (63 : ℝ) * (A.card : ℝ) ^ 2 * (S.card : ℝ) ^ 4 := by
  classical
  let bad := heavyFibres A D S G2 ρ \ starFibres A D S G2 ρ
  let T := countingTriples bad G2 ρ
  have hbad_eq :
      ((fibreLabels A D S \ starFibres A D S G2 ρ).filter fun a =>
          (D.card : ℝ) ^ 2 / (6 * (A.card : ℝ)) ≤
            (fibreCount G2 ρ a : ℝ)) = bad := by
    ext a
    simp only [bad, heavyFibres, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hpairs : G2 ⊆ D.powersetCard 2 := by
    intro P hP
    exact (hρ.2 P hP).1
  have htriple_lower :
      (∑ a ∈ bad, (fibreCount G2 ρ a : ℝ) ^ 2) ≤
        3 * (T.card : ℝ) := by
    exact_mod_cast
      countingTriples_card_lower_proposed A D S G2 sel ρ hρ
  have hmultiplicity :
      T.card ≤ 63 * (sigmaRange A S).card := by
    apply Finset.card_le_mul_card_image_of_maps_to
    · intro t ht
      exact sigma_mem_range_proposed A D S G2 G2 bad sel ρ hρ
        (fun _ h => h) t ht
    · intro g hg
      exact sigma_multiplicity_le_proposed D bad G2 ρ hD hpairs g
  have hTcard :
      T.card ≤ 63 * (A.card ^ 2 * S.card ^ 4) := by
    exact hmultiplicity.trans
      (Nat.mul_le_mul_left 63 (sigmaRange_card_le_proposed A S))
  have hTcard_real :
      (T.card : ℝ) ≤
        63 * (A.card : ℝ) ^ 2 * (S.card : ℝ) ^ 4 := by
    have hTcard' :
        T.card ≤ 63 * A.card ^ 2 * S.card ^ 4 := by
      calc
        T.card ≤ 63 * (A.card ^ 2 * S.card ^ 4) := hTcard
        _ = 63 * A.card ^ 2 * S.card ^ 4 := by ring
    exact_mod_cast hTcard'
  rw [hbad_eq]
  nlinarith

/-- Object-level discharge of `lemmaF_core_sharp.hS4`. -/
theorem lemmaF_hS4_from_objects_proposed (A D S : Finset G) {C : ℝ}
    (hcap : FourthPowerCap A D S C) :
    (S.card : ℝ) ^ 4 ≤
      (D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5) := by
  by_cases hzero : (0 : G) = 0
  · exact hcap
  · exact (hzero rfl).elim

/-- Companion discharge of `lemmaF_core_sharp.hcard`. -/
theorem lemmaF_hcard_from_objects_proposed (A D S : Finset G) :
    ((fibreLabels A D S).card : ℝ) ≤ (A.card : ℝ) := by
  exact_mod_cast
    Finset.card_le_card (show fibreLabels A D S ⊆ A by
      exact Finset.sdiff_subset)

/-- Companion discharge of `lemmaF_core_sharp.hstarcap`. -/
theorem lemmaF_hstarcap_from_objects_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ) :
    ∀ a ∈ starFibres A D S G2 ρ,
      (fibreCount G2 ρ a : ℝ) ≤ 3 * ((D.card : ℝ) - 1) := by
  classical
  intro a ha
  obtain ⟨_, u, huD, hstar⟩ :=
    Finset.mem_filter.mp ha
  let F := (fibreN G2 ρ a).filter fun P => u ∈ P
  let f : Finset G → G := fun P => ∑ x ∈ P.erase u, x
  have hP_data (P : Finset G) (hP : P ∈ F) :
      P ∈ G2 ∧ P ⊆ D ∧ P.card = 2 ∧ u ∈ P := by
    have hP' := Finset.mem_filter.mp hP
    have hP_G2 : P ∈ G2 := (Finset.mem_filter.mp hP'.1).1
    have hP_pow := (hρ.2 P hP_G2).1
    exact ⟨hP_G2, (Finset.mem_powersetCard.mp hP_pow).1,
      (Finset.mem_powersetCard.mp hP_pow).2, hP'.2⟩
  have hf_mem (P : Finset G) (hP : P ∈ F) : f P ∈ D.erase u := by
    obtain ⟨hP_G2, hPsub, hPcard, huP⟩ := hP_data P hP
    have herase_card : (P.erase u).card = 1 := by
      rw [Finset.card_erase_of_mem huP, hPcard]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp herase_card
    have hvP : v ∈ P := by
      have : v ∈ P.erase u := by simp [hv]
      exact Finset.mem_of_mem_erase this
    have hvne : v ≠ u := by
      have : v ∈ P.erase u := by simp [hv]
      exact (Finset.mem_erase.mp this).1
    have hvD : v ∈ D := hPsub hvP
    simp [f, hv, hvD, hvne]
  have hf_injective : Set.InjOn f F := by
    intro P hP Q hQ hPQ
    obtain ⟨hP_G2, hPsub, hPcard, huP⟩ := hP_data P hP
    obtain ⟨hQ_G2, hQsub, hQcard, huQ⟩ := hP_data Q hQ
    have hPerase_card : (P.erase u).card = 1 := by
      rw [Finset.card_erase_of_mem huP, hPcard]
    have hQerase_card : (Q.erase u).card = 1 := by
      rw [Finset.card_erase_of_mem huQ, hQcard]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hPerase_card
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hQerase_card
    have hvw : v = w := by
      simpa [f, hv, hw] using hPQ
    apply Finset.erase_injOn' u huP huQ
    change P.erase u = Q.erase u
    rw [hv, hw, hvw]
  have hdegree_card :
      fibreDegree G2 ρ a u ≤ (D.erase u).card := by
    have himage : F.image f ⊆ D.erase u := by
      intro x hx
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      exact hf_mem P hP
    calc
      fibreDegree G2 ρ a u = F.card := rfl
      _ = (F.image f).card :=
        (Finset.card_image_of_injOn hf_injective).symm
      _ ≤ (D.erase u).card := Finset.card_le_card himage
  have hdegree :
      fibreDegree G2 ρ a u ≤ D.card - 1 := by
    simpa [Finset.card_erase_of_mem huD] using hdegree_card
  have hnat :
      fibreCount G2 ρ a ≤ 3 * (D.card - 1) :=
    hstar.trans (Nat.mul_le_mul_left 3 hdegree)
  have hd_one : 1 ≤ D.card := Finset.card_pos.mpr ⟨u, huD⟩
  calc
    (fibreCount G2 ρ a : ℝ) ≤ (3 * (D.card - 1) : ℕ) := by
      exact_mod_cast hnat
    _ = 3 * ((D.card : ℝ) - 1) := by
      norm_num [Nat.cast_sub hd_one]

/-- Proposed full O4 composition into `lemmaF_core_sharp`, specialized to the
certified Two Families constant `C₁ = 63`. -/
theorem star_extraction_sharp_proposed (A D S : Finset G)
    (G2 : Finset (Finset G)) (sel : G → G)
    (ρ : RepresentationChoice G) {C : ℝ}
    (hDsubA : D ⊆ A) (hD : DissociatedF D)
    (h0 : (0 : G) ∈ S) (hd : 10 ≤ D.card)
    (hC : 129024 ≤ C) (hcap : FourthPowerCap A D S C)
    (hsecond : HasSecondRemovalBound D S G2)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ) :
    (D.card : ℝ) ^ 2 / 7 ≤
        ∑ a ∈ starFibres A D S G2 ρ, (fibreCount G2 ρ a : ℝ) ∧
      (D.card : ℝ) / 21 ≤ ((starFibres A D S G2 ρ).card : ℝ) := by
  classical
  have hsub :
      starFibres A D S G2 ρ ⊆ fibreLabels A D S := by
    intro a ha
    have ha_heavy := (Finset.mem_filter.mp ha).1
    exact (Finset.mem_filter.mp ha_heavy).1
  have hd_real : (10 : ℝ) ≤ (D.card : ℝ) := by
    exact_mod_cast hd
  have hdn : (D.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hDsubA
  have hC1 : (1 : ℝ) ≤ 63 := by norm_num
  have hC' : 2048 * (63 : ℝ) ≤ C := by
    norm_num
    exact hC
  have hmany :
      (D.card : ℝ) ^ 2 / 3 ≤ (G2.card : ℝ) :=
    goodPair_card_lower_proposed A D S G2 hDsubA hD h0 hd hC hcap hsecond
  have hmass :
      (D.card : ℝ) ^ 2 / 3 ≤
        ∑ a ∈ fibreLabels A D S, (fibreCount G2 ρ a : ℝ) :=
    lemmaF_hmass_from_objects_proposed A D S G2 sel ρ hρ hmany
  exact lemmaF_core_sharp
    (fibreLabels A D S) (starFibres A D S G2 ρ) hsub
    (fibreCount G2 ρ)
    (d := (D.card : ℝ)) (n := (A.card : ℝ))
    (C₁ := 63) (C := C) (S := (S.card : ℝ))
    hd_real hdn hC1 hC'
    (lemmaF_hS4_from_objects_proposed A D S hcap)
    hmass
    (lemmaF_hcard_from_objects_proposed A D S)
    (lemmaF_hbad_from_objects_proposed A D S G2 sel ρ hD hρ)
    (lemmaF_hstarcap_from_objects_proposed A D S G2 sel ρ hρ)

end ObjectLayer
end BedertLab
