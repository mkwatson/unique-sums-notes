/-
# Object layer, O7d: diagonal and off-diagonal multiplicity adapter

PROPOSED 2026-07-24 by the Codex proposal arm.
FROZEN 2026-07-24 by the Claude freeze arm. Statements changed at freeze:
NONE. The body remains `sorry` for the fill arm.

Authority: `candidates/bedert-omega/o7-charter-proposal.md`, Sections 1 and 6,
approved with Option B. This file contains only the one proposed O7d theorem
signature. Its body is `sorry`.

## FREEZE ADJUDICATION (2026-07-24)

* Seam audit against the certified O5 chain: the premise subset
  `{hD, hsecond, hρ, hretained, hinward}` is byte-identical to
  `inward_successful_spokes_local_from_multiplicity_proposed`'s premises at
  `G2 := goodTwo D S sel`, and `{hDsubA, h0, hd, hC, hcap, hstarMass}` plus
  the local bound is byte-identical to `inward_mass_from_local_proposed`'s.
  The conclusion is byte-identical to
  `inward_mass_bound_from_objects_proposed`'s conclusion at the same
  specialization, including the strict `D.card ^ 2 / 49` inequality and the
  exact `let u := (∑ x ∈ P, x) - center a` success equation. Constants
  checked at every seam: `7`, `49`, `63` (inside the chain), `3`, `129024`.
* `hstarMass` is byte-identical to the first conclusion conjunct of O7c's
  certified `star_mass_for_constructed_system_proposed` (flag 2 upheld). It
  is logically redundant: the remaining premises already derive it through
  the certified `star_extraction_sharp_proposed`, so the theorem is also a
  one-invocation corollary of `inward_mass_bound_from_objects_proposed`
  with `hstarMass` unused. Accepted as deliberate interface transparency;
  two certified fill routes exist, so freeze risk is nil.
* Flag 3 upheld: no `hcenter` premise is needed — the certified
  discrepancy chain consumes `center` only through `hretained`'s subset
  half (checked against
  `inward_spoke_discrepancy_decomposition_proposed`'s argument list).
* `hsecond`/`hρ` are byte-identical to the conclusion types of O7b's
  certified `goodTwo_hasSecondRemovalBound_proposed` and
  `exists_oriented_representation_choice_from_isUSF_proposed`;
  `hinward` is byte-identical to the strict inward branch of O7c's
  certified `constructed_branch_dichotomy_proposed`.
* Junk audit: every binder and hypothesis is consumed by the intended
  two-step composition; none is deletable without changing the seam.
  Vacuity audit: with `hd : 10 ≤ D.card` the conclusion forces strictly
  positive successful mass; not vacuously satisfiable.
* Back-translation trial (Lean text first, docstrings diffed after):
  matches charter Section 6's `d²/49 < Σ_H |I(a)|` package with no
  discrepancy; quantifier order `∃ I` before the three `∀ a ∈ starFibres`
  conjuncts matches the O5 conclusion exactly.
* Build gate at freeze: `lake env lean` exit 0, exactly one `sorry`
  warning.

This phase adds no combinatorial claim. The intended fill composes the
certified discrepancy decomposition and fixed-discrepancy multiplicity chain
in `O5Multiplicity` with O5's certified strict-mass summation.

Source attribution is deliberately three-way:

* Bedert's printed inward equations and `e = d` argument are
  `sources/bedert/src/main.tex:716-724,726-762`.
* The campaign's sharpened arm is
  `candidates/bedert-omega/note-core/prose-proof-arm1.md`, from (A1.7)
  through its inward absorption argument.
* The independent blind arm audits the same diagonal/off-diagonal split in
  `candidates/bedert-omega/note-core/prose-proof-arm2-blind.md`. The strict
  `1/49` mass conclusion is campaign content and is not attributed to
  Bedert.

## AMBIGUITY FLAGS

1. The pair system is specialized to O7b's concrete
   `goodTwo D S sel`; this is not a second abstract `G2` interface.
2. The star-mass inequality is accepted explicitly in O7c's exact first
   conclusion shape. The unused star-cardinality conclusion is not repeated.
3. The centre-membership inequality is not an input: the certified
   diagonal chain consumes `center` only through the retained-family
   interface. Adding the unused O7c centre premise would not strengthen the
   returned O5 package.
4. The conclusion is byte-for-byte in the `I`-package shape of
   `inward_mass_bound_from_objects_proposed`, including the strict
   `D.card ^ 2 / 49` inequality. No implementation of `I` is exposed.
5. This is a composition seam only. A failed fill must be reported as an
   O7b/O7c-to-O5 interface mismatch, not repaired by changing an O5 theorem.
-/
import BedertLab.ObjectLayer.O5Multiplicity
import BedertLab.ObjectLayer.O7cHeavyFibres

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Package the certified diagonal/off-diagonal multiplicity chain for the
constructed O7b pair system.

The intended body invokes
`inward_successful_spokes_local_from_multiplicity_proposed`, then
`inward_mass_from_local_proposed`. No counting argument belongs in this
adapter. -/
theorem inward_diagonal_package_from_constructed_system_proposed
    (A D S : Finset G) (sel center : G → G)
    (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G)) {C : ℝ}
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (h0 : (0 : G) ∈ S)
    (hd : 10 ≤ D.card)
    (hC : 129024 ≤ C)
    (hcap : FourthPowerCap A D S C)
    (hsecond :
      HasSecondRemovalBound D S (goodTwo D S sel))
    (hρ :
      IsOrientedRepresentationChoice
        A D S (goodTwo D S sel) sel ρ)
    (hretained :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        retained a ⊆
            (fibreN (goodTwo D S sel) ρ a).filter
              (fun P => center a ∈ P) ∧
          fibreCount (goodTwo D S sel) ρ a ≤
            3 * (retained a).card)
    (hstarMass :
      (D.card : ℝ) ^ 2 / 7 ≤
        ∑ a ∈ starFibres A D S (goodTwo D S sel) ρ,
          (fibreCount (goodTwo D S sel) ρ a : ℝ))
    (hinward :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card) :
    ∃ I : G → Finset (Finset G),
      (∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        I a ⊆
          (retained a).filter (fun P => chosenY ρ P ∈ D + S)) ∧
      (∀ a ∈ starFibres A D S (goodTwo D S sel) ρ, ∀ P ∈ I a,
        (let u := (∑ x ∈ P, x) - center a;
          u ∈ goodOne D S ∧
            sel u - (a - (center a + sel (center a))) ∈ S ∧
              chosenY ρ P =
                u + (sel u - (a - (center a + sel (center a)))))) ∧
      (D.card : ℝ) ^ 2 / 49 <
        ∑ a ∈ starFibres A D S (goodTwo D S sel) ρ,
          ((I a).card : ℝ) := by
  exact inward_mass_bound_from_objects_proposed
    A D S (goodTwo D S sel) sel center ρ retained
    hDsubA hD h0 hd hC hcap hsecond hρ hretained hinward

end ObjectLayer
end BedertLab
