/-
# Object layer, O7e: exact O5 witness package

PROPOSED 2026-07-24 by the Codex proposal arm.
FROZEN 2026-07-24 by the Claude freeze arm. Statements changed at freeze:
NONE. All bodies remain `sorry` for the fill arm.

Authority: `candidates/bedert-omega/o7-charter-proposal.md`, Sections 1 and 7,
approved with Option B. This file contains only the three proposed O7e
theorem signatures. Every theorem body is `sorry`.

## FREEZE ADJUDICATION (2026-07-24)

* `constructed_second_removal_and_orientation_proposed`: `hD` plus
  `hsel`'s `.1` projection are exactly the premises of O7b's certified
  `goodTwo_hasSecondRemovalBound_proposed`; `hUSF`, full `hsel`, and
  `hsim` are byte-identical to the premises of O7b's certified
  `exists_oriented_representation_choice_from_isUSF_proposed`, whose
  conclusion supplies the `∃ ρ`. Every hypothesis is load-bearing.
  Placing the ρ-independent `HasSecondRemovalBound` inside the `∃ ρ`
  scope is packaging only. Vacuity of the oriented component on empty
  `goodTwo` is inherited from O7b's freeze note and charter Section 9.
* `retained_chosenY_injective_proposed` (the one genuinely new
  statement): quantifiers verified per-`a`, never global — `∀ a ∈
  starFibres`, then `Set.InjOn` on `↑(retained a)`. Source
  triangulation: byte-checked against Bedert's `Nlarge` proof
  (`main.tex:648-657`, "if {d₁,d₁'},{d₂,d₂'} ∈ N(a) are distinct then
  y(d₁,d₁') ≠ y(d₂,d₂')"), arm 1's "y-values are distinct for fixed a"
  (prose-proof-arm1.md, after (A1.13)), and arm 2's outward
  distinctness supporting reconstructed display (6). The frozen claim
  restricts Bedert's whole-`N(a)` injectivity to `retained a` and to
  star labels — restriction toward O5's consumption shape, never a
  strengthening. Provability basis from exactly these premises: equal
  `chosenY` on one `chosenX` fibre forces equal `pairTarget` (via
  `hρ.2`); a distinct second pair `P' ⊆ goodOne ⊆ D` with
  `sel`-values in `S` (via `hρ.1`) would witness `P ∈ badTwo`,
  contradicting `goodTwo` membership. No `DissociatedF` hypothesis is
  needed; its absence is correct, not an omission. `hretained`'s
  cardinality half is non-load-bearing but frozen for O7c shape
  identity (flag 3 upheld).
* `exists_o5_witness_package_from_isUSF_proposed`: witness types match
  O5/O6 consumption exactly (`G2 : Finset (Finset G)`,
  `ρ : RepresentationChoice G`, `retained : G → Finset (Finset G)` are
  the binder types of `one_bit_iteration_step_from_O5_proposed`).
  Conjunct 3 is byte-identical to O7c's certified centre conclusion,
  conjunct 4 to O7c's retained conclusion, conjunct 5 to statement 2's
  conclusion, all at abstract `G2`; conjuncts 1-2 to statement 1's.
  `hchoose`/`hDsubA`/`h0` are exactly O7a's
  `source_selector_from_simultaneous_proposed` premises; `hD`/`hUSF`
  feed statement 1. No junk hypotheses; `hd`/`hC`/`hcap` correctly
  absent (no composed piece needs them).
* Abstract-`G2` scope note (flag 4 adjudicated): the package
  deliberately omits `G2 = goodTwo D S sel`, so a consumer of this
  existential can reach every O5Banks/O4/O6 theorem (all abstract in
  `G2`) but NOT the `goodTwo`-specific O7c/O7d theorems. O7f's inward
  route is fully supplied either way: abstractly via
  `inward_mass_bound_from_objects_proposed`, or concretely by
  re-running the O7a→O7b→O7c→O7d chain as charter Section 8 words it.
  Both routes were checked end-to-end at freeze; nothing is missing
  for the `hstep` discharge.
* Back-translation trials (Lean text first, docstrings diffed after):
  all three match their docstrings and charter Section 7 with no
  discrepancy.
* Build gate at freeze: `lake env lean` exit 0, exactly three `sorry`
  warnings.

The first and third statements are packaging adapters. They re-export the
now-certified O7b second-removal and oriented-repair witnesses and the frozen
O7c centre/retained witnesses in O5's exact input shapes. The second
statement, injectivity of `chosenY` on each retained star, is genuinely new
content.

Source attribution is deliberately three-way:

* Bedert's source selection, good-pair uniqueness, oriented repairs, and
  fixed-fibre injectivity are
  `sources/bedert/src/main.tex:516-572,635-657`; centres and retained stars
  are at `main.tex:668-704`.
* The campaign's sharpened arm fixes the oriented endpoints in
  `candidates/bedert-omega/note-core/prose-proof-arm1.md` (A1.7), then uses
  their distinctness in the outward and inward branches.
* The independent blind arm audits the same oriented objects and distinct
  fixed-fibre endpoints in
  `candidates/bedert-omega/note-core/prose-proof-arm2-blind.md`. Its later
  sharpened one-bit conclusions are not attributed to Bedert.

## AMBIGUITY FLAGS

1. `constructed_second_removal_and_orientation_proposed` returns O7b's
   concrete `goodTwo D S sel` and one total `RepresentationChoice`; values of
   the choice off `goodTwo` remain junk.
2. `retained_chosenY_injective_proposed` is the only new mathematical
   statement. It asserts injectivity on the entire retained star, not only
   on its outward or inward filter.
3. The injectivity statement accepts O5's full retained-family conjunction.
   Its cardinality half is intentionally non-load-bearing but retained so
   the theorem can consume O7c's frozen output without repackaging.
4. The final package existentially exposes an abstract name `G2`, instantiated
   in the intended fill by `goodTwo D S sel`. It does not add a persistent
   equality field because O5 consumes `G2` only through the listed facts.
5. The final package starts from O7a's
   `IsSimultaneousUniqueSelector`, rather than duplicating the Option B
   `hBLR` parameter. The single external rectification assumption remains
   visible upstream in O7a and must remain visible again in O7f.
6. `hyDistinct` is pointwise on `starFibres`, exactly matching the premise of
   O5's outward bank after specialization to a selected star.
-/
import BedertLab.ObjectLayer.O7aRectification
import BedertLab.ObjectLayer.O7bRepairChoice
import BedertLab.ObjectLayer.O7cHeavyFibres

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Collect O7b's exact second-removal and oriented-repair seams.

This statement is composition only: the intended body invokes
`goodTwo_hasSecondRemovalBound_proposed` and
`exists_oriented_representation_choice_from_isUSF_proposed`. -/
theorem constructed_second_removal_and_orientation_proposed
    (A D S : Finset G) (sel : G → G)
    (hD : DissociatedF D)
    (hUSF : IsUSF A)
    (hsel : ∀ d ∈ D, sel d ∈ S ∧ d + sel d ∈ A)
    (hsim :
      ∀ d ∈ D, ∀ d' ∈ D,
        ∀ x ∈ S, d + x ∈ A →
          ∀ y ∈ S, d' + y ∈ A →
            x + y = sel d + sel d' →
              x = sel d ∧ y = sel d') :
    ∃ ρ : RepresentationChoice G,
      HasSecondRemovalBound D S (goodTwo D S sel) ∧
        IsOrientedRepresentationChoice
          A D S (goodTwo D S sel) sel ρ := by
  obtain ⟨ρ, hρ⟩ :=
    exists_oriented_representation_choice_from_isUSF_proposed
      A D S sel hUSF hsel hsim
  exact ⟨ρ,
    goodTwo_hasSecondRemovalBound_proposed
      D S sel hD (fun d hd => (hsel d hd).1),
    hρ⟩

/-- The selected second endpoints are injective on every retained star.

This is the genuinely new O7e statement. Equal `chosenY` endpoints in one
fixed `chosenX` fibre give equal canonical target sums; the good-pair
uniqueness encoded by `goodTwo` then recovers the same unordered pair.

Bedert source: `main.tex:635-657`.
Campaign source: arm 1 (A1.7) and the distinct outward endpoints.
Blind audit: the fixed-fibre distinctness item supporting its outward case. -/
theorem retained_chosenY_injective_proposed
    (A D S : Finset G) (sel center : G → G)
    (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G))
    (hρ :
      IsOrientedRepresentationChoice
        A D S (goodTwo D S sel) sel ρ)
    (hretained :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        retained a ⊆
            (fibreN (goodTwo D S sel) ρ a).filter
              (fun P => center a ∈ P) ∧
          fibreCount (goodTwo D S sel) ρ a ≤
            3 * (retained a).card) :
    ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
      Set.InjOn (chosenY ρ)
        (↑(retained a) : Set (Finset G)) := by
  classical
  intro a ha P hP Q hQ hY
  have hP_fibre :
      P ∈ fibreN (goodTwo D S sel) ρ a :=
    (Finset.mem_filter.mp ((hretained a ha).1 hP)).1
  have hQ_fibre :
      Q ∈ fibreN (goodTwo D S sel) ρ a :=
    (Finset.mem_filter.mp ((hretained a ha).1 hQ)).1
  have hP_data := Finset.mem_filter.mp hP_fibre
  have hQ_data := Finset.mem_filter.mp hQ_fibre
  have htarget :
      pairTarget sel P = pairTarget sel Q := by
    calc
      pairTarget sel P =
          chosenX ρ P + chosenY ρ P :=
        (hρ.2 P hP_data.1).2.2.2.symm
      _ = chosenX ρ Q + chosenY ρ Q := by
        rw [hP_data.2, hQ_data.2, hY]
      _ = pairTarget sel Q :=
        (hρ.2 Q hQ_data.1).2.2.2
  by_contra hPQ
  have hQ_base :
      Q ∈ (goodOne D S).powersetCard 2 :=
    (Finset.mem_sdiff.mp hQ_data.1).1
  have hQ_pow := Finset.mem_powersetCard.mp hQ_base
  obtain ⟨u, v, huv, hQuv⟩ := Finset.card_eq_two.mp hQ_pow.2
  have hu_good : u ∈ goodOne D S :=
    hQ_pow.1 (by simp [hQuv])
  have hv_good : v ∈ goodOne D S :=
    hQ_pow.1 (by simp [hQuv])
  have huD : u ∈ D := (Finset.mem_sdiff.mp hu_good).1
  have hvD : v ∈ D := (Finset.mem_sdiff.mp hv_good).1
  have htargetQ :
      pairTarget sel Q =
        (u + sel u) + (v + sel v) := by
    calc
      pairTarget sel Q =
          ∑ z ∈ ({u, v} : Finset G), (z + sel z) :=
        congrArg
          (fun R : Finset G => ∑ z ∈ R, (z + sel z)) hQuv
      _ = (u + sel u) + (v + sel v) := Finset.sum_pair huv
  have hP_bad : P ∈ badTwo D S sel := by
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_sdiff.mp hP_data.1).1, ?_⟩
    refine ⟨u, huD, v, hvD,
      sel u, (hρ.1 u huD).1, sel v, (hρ.1 v hvD).1, ?_, ?_⟩
    · exact htarget.trans htargetQ
    · intro h
      apply hPQ
      exact h.symm.trans hQuv.symm
  exact (Finset.mem_sdiff.mp hP_data.1).2 hP_bad

/-- Construct the complete witness package consumed by O5.

The intended fill obtains `sel` from O7a, obtains the concrete `goodTwo`
system and `ρ` from the first theorem, obtains `center` and `retained` from
O7c, and adds the pointwise injectivity theorem above. -/
theorem exists_o5_witness_package_from_isUSF_proposed
    (A D S : Finset G) (choose : Finset G → G)
    (hchoose : IsSimultaneousUniqueSelector S choose)
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (h0 : (0 : G) ∈ S)
    (hUSF : IsUSF A) :
    ∃ G2 : Finset (Finset G),
      ∃ sel : G → G,
        ∃ ρ : RepresentationChoice G,
          ∃ center : G → G,
            ∃ retained : G → Finset (Finset G),
              HasSecondRemovalBound D S G2 ∧
                IsOrientedRepresentationChoice A D S G2 sel ρ ∧
                  (∀ a ∈ starFibres A D S G2 ρ,
                    center a ∈ D ∧
                      fibreCount G2 ρ a ≤
                        3 * fibreDegree G2 ρ a (center a)) ∧
                    (∀ a ∈ starFibres A D S G2 ρ,
                      retained a ⊆
                          (fibreN G2 ρ a).filter
                            (fun P => center a ∈ P) ∧
                        fibreCount G2 ρ a ≤
                          3 * (retained a).card) ∧
                      ∀ a ∈ starFibres A D S G2 ρ,
                        Set.InjOn (chosenY ρ)
                          (↑(retained a) : Set (Finset G)) := by
  obtain ⟨sel, hsel, hsim⟩ :=
    source_selector_from_simultaneous_proposed
      A D S choose hchoose hDsubA h0
  obtain ⟨ρ, hsecond, hρ⟩ :=
    constructed_second_removal_and_orientation_proposed
      A D S sel hD hUSF hsel hsim
  obtain ⟨center, retained, hcenter, _, hretained⟩ :=
    exists_star_centres_and_retained_proposed
      A D S sel ρ
  exact ⟨goodTwo D S sel, sel, ρ, center, retained,
    hsecond, hρ, hcenter, hretained,
    retained_chosenY_injective_proposed
      A D S sel center ρ retained hρ hretained⟩

end ObjectLayer
end BedertLab
