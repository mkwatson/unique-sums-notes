/-
# Object layer, O7c: heavy fibres, centres, and branch classification

PROPOSED 2026-07-24 by the Codex proposal arm.
FROZEN 2026-07-24 by the Claude freeze arm. Statements changed at freeze:
NONE. All bodies remain `sorry` for the fill arm.

Authority: `candidates/bedert-omega/o7-charter-proposal.md`, Sections 1 and 5,
approved with Option B in `attack-log.md` at approximately 21:15Z. This file
contains only the three proposed O7c theorem signatures. Every theorem body is
`sorry`.

Source attribution is deliberately three-way:

* Bedert's printed definitions of `N(a)`, the heavy family, and
  `N(1/3)`, together with the two-case split, are
  `sources/bedert/src/main.tex:635-716`.
* The campaign's sharpened arm uses the star mass, centred spokes, and
  outward/inward split in `note-core/prose-proof-arm1.md`
  (A1.12)-(A1.18).
* The independent blind arm reconstructs the same objects in
  `note-core/prose-proof-arm2-blind.md`, especially displays (7)-(8).
  Its sharpened one-bit consequences are not attributed to Bedert.

The signatures specialize to O7b's concrete `goodTwo D S sel`. They consume
O7b's certified second-removal and oriented-repair interfaces; they do not
reopen `IsUSF`.

## FREEZE ADJUDICATION (2026-07-24)

* `star_mass_for_constructed_system_proposed` is byte-identical to O4's
  proved `star_extraction_sharp_proposed` specialized at
  `G2 := goodTwo D S sel`: same hypothesis list (including `hd : 10 ≤
  D.card` and `hC : 129024 ≤ C`), both conclusions verbatim, constants
  `1/7` and `1/21` matching at the seam. Its `hsecond`/`hρ` premises are
  exactly the conclusion types of O7b's
  `goodTwo_hasSecondRemovalBound_proposed` and
  `exists_oriented_representation_choice_from_isUSF_proposed`.
* `constructed_branch_dichotomy_proposed` is byte-identical to O5's proved
  `branch_classification_proposed` at the same specialization. Its
  `hρ`/`hcenter`/`hretained` are unused by the excluded-middle fill but
  retained deliberately: O5's header records the same disposition, and
  deletion would break interface identity at the O5/O6 seam. Quantifiers
  checked against `main.tex:704-716` and both prose arms: outward
  existential weak (`2·out ≥ card`, ties outward per `main.tex:707`),
  inward universal strict (`2·in > card`), the exact complement; it
  implies Bedert's weak final case and matches O5 flag 4.
* `exists_star_centres_and_retained_proposed` correctly needs no
  hypotheses: `starFibres` membership carries the `∃ u ∈ D, q ≤ 3·deg`
  witness, so a choice of centre plus the full centred fibre realize every
  conjunct, with `(retained a).card = fibreDegree … (center a)` closing
  the final bound. Not vacuous; it is the Skolemization step. Its first
  and last conjuncts are byte-for-byte the `hcenter`/`hretained` premise
  shapes of `constructed_branch_dichotomy_proposed`.
* Threshold audit: heavy threshold is O4's real weak inequality
  `d²/(6n) ≤ q_a` (`main.tex` definition of `mathcal N`); the star
  condition is the exact ℚ-clearing `q ≤ 3·deg`; the `/2` halving to
  `N(1/3)` and the downstream `m' ≥ d²/(36n)` live inside O4's certified
  extraction and O5's outward bank respectively, deliberately NOT
  restated here (charter: no new star-counting claim in O7c). No floors,
  no ℕ subtraction, no ℕ division in any statement.
* Junk-value audit: `center`/`retained` total with junk off `starFibres`
  (flag 3); all statement-level divisions are by the literals 7 and 21.
* Build gate at freeze: `lake env lean` exit 0, exactly three `sorry`
  warnings.

## AMBIGUITY FLAGS

1. O4 already freezes the source fibre as `fibreN` and its size as
   `fibreCount`. O7c does not introduce a second definition of `N(a)`.
   Likewise, all sums remain over O4's total functions restricted to its
   finite label sets.
2. The heavy threshold and the star refinement are distinct. This proposal
   uses O4's exact real inequality
   `D.card ^ 2 / (6 * A.card) <= fibreCount` in `heavyFibres`, then the
   denominator-cleared natural inequality
   `fibreCount <= 3 * fibreDegree` in `starFibres`. Replacing the heavy
   threshold by the `N(1/3)` condition, or admitting light centred fibres,
   would change the theorem.
3. The centre and retained-family witnesses are total functions. Only their
   values on `starFibres` are constrained; values elsewhere are junk. A
   subtype-indexed dependent choice would not feed O5's frozen API.
4. The proposal takes the retained family on a star label to be the full
   centred fibre, and exposes that equality in addition to O5's exact subset
   and cardinality interface. Cutting a smaller qualifying substar, or
   exposing only the weaker O5 interface, would be a different freeze choice.
5. Branch ties are outward:
   `2 * |{P in retained(a) : chosenY(P) notin D + S}| >= |retained(a)|`.
   Its complementary all-inward alternative is therefore strict. Sending
   ties inward would alter both inequalities.
6. `star_mass_for_constructed_system_proposed` accepts O7b's exact
   `HasSecondRemovalBound` and `IsOrientedRepresentationChoice` proofs as
   premises. It does not accept raw `IsUSF`, nor does it choose a second
   repair system internally.
7. The two star-mass conclusions are preserved together, with constants
   `1/7` and `1/21`. No new star-counting claim is proposed here: the fill
   must be a direct specialization of O4's certified
   `star_extraction_sharp_proposed`.
-/
import BedertLab.ObjectLayer.O5Banks
import BedertLab.ObjectLayer.O7bRepairChoice

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Choose total star centres and the full centred fibres retained for O5.

Bedert printed step: `main.tex:668-704`, especially the definition of
`N(1/3)` and the centred equations.
Campaign sharpened arm: (A1.12)-(A1.18).
Blind arm: the centre-pinned objects preceding reconstructed displays
(7)-(8).

The final conjunct is byte-for-byte in O5's retained-family input shape. -/
theorem exists_star_centres_and_retained_proposed
    (A D S : Finset G) (sel : G → G)
    (ρ : RepresentationChoice G) :
    ∃ center : G → G,
      ∃ retained : G → Finset (Finset G),
        (∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
          center a ∈ D ∧
            fibreCount (goodTwo D S sel) ρ a ≤
              3 * fibreDegree (goodTwo D S sel) ρ a (center a)) ∧
          (∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
            retained a =
              (fibreN (goodTwo D S sel) ρ a).filter
                (fun P => center a ∈ P)) ∧
            ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
              retained a ⊆
                  (fibreN (goodTwo D S sel) ρ a).filter
                    (fun P => center a ∈ P) ∧
                fibreCount (goodTwo D S sel) ρ a ≤
                  3 * (retained a).card := by
  classical
  let center : G → G := fun a =>
    if ha : a ∈ starFibres A D S (goodTwo D S sel) ρ then
      Classical.choose (Finset.mem_filter.mp ha).2
    else
      0
  let retained : G → Finset (Finset G) := fun a =>
    (fibreN (goodTwo D S sel) ρ a).filter (fun P => center a ∈ P)
  refine ⟨center, retained, ?_, ?_, ?_⟩
  · intro a ha
    have hchoice :=
      Classical.choose_spec (Finset.mem_filter.mp ha).2
    simpa [center, ha] using hchoice
  · intro a ha
    rfl
  · intro a ha
    constructor
    · exact Finset.Subset.rfl
    · have hcenter :
          fibreCount (goodTwo D S sel) ρ a ≤
            3 * fibreDegree (goodTwo D S sel) ρ a (center a) :=
        (by
          have hchoice :=
            Classical.choose_spec (Finset.mem_filter.mp ha).2
          simpa [center, ha] using hchoice.2)
      simpa [retained, fibreDegree] using hcenter

/-- Specialize O4's sharp star extraction to O7b's concrete good-pair and
oriented-repair system.

Bedert printed step: the `N(a)` partition and `N(1/3)` extraction at
`main.tex:635-704`.
Campaign sharpened arm: the mass-weighted estimate (A1.12).
Blind arm: reconstructed displays (4)-(5).

Both conclusions are retained because O5/O7d use the mass bound while later
nonvacuity and counting seams may use the star-cardinality bound. -/
theorem star_mass_for_constructed_system_proposed
    (A D S : Finset G) (sel : G → G)
    (ρ : RepresentationChoice G) {C : ℝ}
    (hDsubA : D ⊆ A) (hD : DissociatedF D)
    (h0 : (0 : G) ∈ S) (hd : 10 ≤ D.card)
    (hC : 129024 ≤ C) (hcap : FourthPowerCap A D S C)
    (hsecond :
      HasSecondRemovalBound D S (goodTwo D S sel))
    (hρ :
      IsOrientedRepresentationChoice
        A D S (goodTwo D S sel) sel ρ) :
    (D.card : ℝ) ^ 2 / 7 ≤
        ∑ a ∈ starFibres A D S (goodTwo D S sel) ρ,
          (fibreCount (goodTwo D S sel) ρ a : ℝ) ∧
      (D.card : ℝ) / 21 ≤
        ((starFibres A D S (goodTwo D S sel) ρ).card : ℝ) := by
  exact star_extraction_sharp_proposed
    A D S (goodTwo D S sel) sel ρ
    hDsubA hD h0 hd hC hcap hsecond hρ

/-- Instantiate O5's outward-tie/inward-strict classification on the
constructed O7b repair system and the retained centred stars.

Bedert printed step: the case split at `main.tex:704-716`.
Campaign sharpened arm: (A1.16)-(A1.18).
Blind arm: reconstructed display (6) and the strict inward hypothesis before
display (7).

This is the exact classification later used to choose the two bank premises
of `one_bit_branch_dichotomy_from_objects_proposed`. -/
theorem constructed_branch_dichotomy_proposed
    (A D S : Finset G) (sel center : G → G)
    (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G))
    (hρ :
      IsOrientedRepresentationChoice
        A D S (goodTwo D S sel) sel ρ)
    (hcenter :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        center a ∈ D ∧
          fibreCount (goodTwo D S sel) ρ a ≤
            3 * fibreDegree (goodTwo D S sel) ρ a (center a))
    (hretained :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        retained a ⊆
            (fibreN (goodTwo D S sel) ρ a).filter
              (fun P => center a ∈ P) ∧
          fibreCount (goodTwo D S sel) ρ a ≤
            3 * (retained a).card) :
    (∃ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card) ∨
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card := by
  classical
  by_cases hout :
      ∃ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card
  · exact Or.inl hout
  · right
    intro a ha
    have hout_lt :
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card <
          (retained a).card := by
      exact Nat.lt_of_not_ge (fun hge => hout ⟨a, ha, hge⟩)
    have hpartition :
        ((retained a).filter fun P =>
            chosenY ρ P ∈ D + S).card +
          ((retained a).filter fun P =>
            chosenY ρ P ∉ D + S).card =
        (retained a).card := by
      exact Finset.card_filter_add_card_filter_not
        (s := retained a) (p := fun P => chosenY ρ P ∈ D + S)
    omega

end ObjectLayer
end BedertLab
