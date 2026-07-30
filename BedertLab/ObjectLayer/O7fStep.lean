/-
# Object layer, O7f: sharpened one-step theorem and exact O6 discharge

PROPOSED 2026-07-24 by the Codex proposal arm.

Authority: `candidates/bedert-omega/o7-charter-proposal.md`, Sections 1, 8,
and 10, approved with Option B. This file contains only the two proposed
O7f theorem signatures. Every theorem body is `sorry`.

Binding tier label on fill completion (charter Section 10, Option B,
verbatim; never shorten):

> Kernel-certified from the original finite objects conditional on one
> explicitly stated Lev 2008 cyclic rectification interface; the
> campaign's sharpened one-bit argument and all witness reconstruction
> after rectification are kernel-certified.

It must not be shortened to "kernel-certified from the original objects."
The `hBLR` parameter name is retained unchanged (frozen trust-boundary
identifier); the prose attribution is corrected here because the encoded
`log_2 p` threshold matches Lev 2008 Theorem 1, not Bilu-Lev-Ruzsa's own
Theorem 3.1 (which proves only `log_4 p` at order 2). See
`candidates/bedert-omega/tailored-rectification.md` PHASE 1.2 and
`attack-log.md`'s bibliographic catch.

PHASE 1 DONE: route resolved + statements.
PHASE 2 DONE: builds clean (`lake env lean`; two `sorry` warnings only).

The proposed fill uses the concrete route. At every current state `S`, it
obtains a simultaneous selector from O7a, constructs O7b's
`goodTwo D S sel`, obtains the centres and retained stars from O7c, obtains
fixed-fibre endpoint injectivity from O7e, and invokes O7d at that same
concrete pair system. It then composes the certified O5 outward and inward
banks and packages their one-bit alternative in O6's exact shape.

Source attribution is deliberately three-way:

* Bedert's printed proposition has the outward one-bit branch but a cubic
  inward update: `sources/bedert/src/main.tex:479-494,704-765`.
* The strict inward one-bit conclusion and the exact campaign cap
  `129024` are the campaign's sharpened argument in
  `candidates/bedert-omega/note-core/prose-proof-arm1.md`.
* The independent blind arm in
  `candidates/bedert-omega/note-core/prose-proof-arm2-blind.md`
  reconstructs the four inward object inputs with the larger cap
  `8128512`; the final popular-label aggregation is the already-certified
  O5/SqrtChain bridge. The sharpened theorem is not attributed to Bedert.

## AMBIGUITY FLAGS

1. **ROUTE: concrete.** O7e's
   `exists_o5_witness_package_from_isUSF_proposed` erases the equality
   `G2 = goodTwo D S sel`. Its abstract package is sufficient for the
   generic O5 route through `inward_mass_bound_from_objects_proposed`, but
   the goodTwo-specific O7c/O7d theorems are then unreachable. Charter
   Section 8 explicitly requires O7d's `I` and mass package and says that
   all witnesses are reconstructed at every invocation. The proposed fill
   therefore re-runs O7a through O7d at
   `G2 := goodTwo D S sel`; it does not destruct O7e's abstract package.
2. The core theorem is maximality-free. It assumes only `D ⊆ A`,
   `DissociatedF D`, and `10 ≤ D.card`; `D.card = dimA A` first appears in
   the adapter.
3. Option B's `hBLR` is repeated verbatim as one explicit theorem
   parameter in both signatures. It is not a Lean axiom and is not hidden
   behind a local definition.
4. The core freezes the campaign constant through `129024 ≤ C`. The blind
   arm independently supports the object pattern only at its larger
   constant; it does not certify this sharper numerical contract.
5. The adapter's conclusion repeats O6's `hstep` binder in its exact
   universal-current-state shape. The rectification and fourth-power caps
   re-enter inside the quantification over `S`; no witness persists between
   invocations.
6. The branch signs are intentionally asymmetric: outward is non-strict at
   `D.card / (36 * K)`, while inward is strict at
   `D.card / (49 * K)`. Both branches use the same actual new-point bank.
7. There is no global label or shift. Each invocation returns one nonzero
   `t`, grows the current state by exactly `S + {0, t}`, and proves the
   one-bit cardinality bound.
-/
import BedertLab.ObjectLayer.O6Iterate
import BedertLab.ObjectLayer.O7dDiagonal
import BedertLab.ObjectLayer.O7eWitnessPackage

open Pointwise

namespace BedertLab
namespace ObjectLayer

/-- The maximality-free sharpened one-bit step in the prime-cyclic setting.

The future concrete fill reconstructs all source selectors, good pairs,
oriented repairs, stars, retained endpoints, and inward channels at this
particular `S`. Bedert supplies the printed outward objects and equations;
the strict inward one-bit bank is campaign content, independently audited
at the object-interface level by the blind arm. -/
theorem sharpened_one_step_from_isUSF_proposed
    (hBLR :
      ∀ {p : ℕ}, p.Prime →
        ∀ S : Finset (ZMod p),
          (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
            ∃ T : Finset ℤ, ∃ φ : ZMod p → ℤ,
              IsAddFreimanIso 2 (↑S) (↑T) φ)
    {p : ℕ} (hp : p.Prime)
    (A D S : Finset (ZMod p)) {K C : ℝ}
    (hUSF : IsUSF A)
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (hd : 10 ≤ D.card)
    (h0 : (0 : ZMod p) ∈ S)
    (hrect : (S.card : ℝ) ≤ Real.logb 2 (p : ℝ))
    (hcap : FourthPowerCap A D S C)
    (hC : 129024 ≤ C)
    (hK : 1 ≤ K)
    (hscale : (A.card : ℝ) = K * (D.card : ℝ)) :
    ∃ t : ZMod p,
      t ≠ 0 ∧
        (S + ({0, t} : Finset (ZMod p))).card ≤ 2 * S.card ∧
          ((D.card : ℝ) / (36 * K) ≤
              ((((A ∩
                  (D + (S + ({0, t} : Finset (ZMod p))))) \
                (D + S)).card : ℕ) : ℝ) ∨
            (D.card : ℝ) / (49 * K) <
              ((((A ∩
                  (D + (S + ({0, t} : Finset (ZMod p))))) \
                (D + S)).card : ℕ) : ℝ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨choose, hchoose⟩ :=
    simultaneous_selector_from_blr_proposed
      (fun hp' S' hrect' =>
        blr_rectification_zmod_proposed hBLR hp' S' hrect')
      hp S hrect
  obtain ⟨sel, hsel, hsim⟩ :=
    source_selector_from_simultaneous_proposed
      A D S choose hchoose hDsubA h0
  have hsecond :
      HasSecondRemovalBound D S (goodTwo D S sel) :=
    goodTwo_hasSecondRemovalBound_proposed
      D S sel hD (fun d hdD => (hsel d hdD).1)
  obtain ⟨ρ, hρ⟩ :=
    exists_oriented_representation_choice_from_isUSF_proposed
      A D S sel hUSF hsel hsim
  obtain ⟨center, retained, hcenter, _, hretained⟩ :=
    exists_star_centres_and_retained_proposed A D S sel ρ
  have hstarMass :=
    star_mass_for_constructed_system_proposed
      A D S sel ρ hDsubA hD h0 hd hC hcap hsecond hρ
  have hbranchClassification :=
    constructed_branch_dichotomy_proposed
      A D S sel center ρ retained hρ hcenter hretained
  have hyDistinct :=
    retained_chosenY_injective_proposed
      A D S sel center ρ retained hρ hretained
  have houtwardBank :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card →
        ∃ t : ZMod p,
          t ≠ 0 ∧
            (S + ({0, t} : Finset (ZMod p))).card ≤ 2 * S.card ∧
              (D.card : ℝ) / (36 * K) ≤
                ((((A ∩
                    (D + (S + ({0, t} : Finset (ZMod p))))) \
                  (D + S)).card : ℕ) : ℝ) := by
    intro a ha houtward
    obtain ⟨t, _, ht, hcard, hgain⟩ :=
      outward_bank_from_objects_proposed
        A D S (goodTwo D S sel) sel center ρ retained
        hρ hK hscale ha (hcenter a ha) (hretained a ha)
        (hyDistinct a ha) houtward
    exact ⟨t, ht, hcard, hgain⟩
  have hinwardBank :
      (∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card) →
        ∃ t : ZMod p,
          t ≠ 0 ∧
            (S + ({0, t} : Finset (ZMod p))).card ≤ 2 * S.card ∧
              (D.card : ℝ) / (49 * K) <
                ((((A ∩
                    (D + (S + ({0, t} : Finset (ZMod p))))) \
                  (D + S)).card : ℕ) : ℝ) := by
    intro hinward
    obtain ⟨I, hI_sub, hI_success, hmass⟩ :=
      inward_diagonal_package_from_constructed_system_proposed
        A D S sel center ρ retained hDsubA hD h0 hd hC hcap
        hsecond hρ hretained hstarMass.1 hinward
    have hnonzero :=
      inward_label_nonzero_from_objects_proposed
        A D S (goodTwo D S sel) sel center ρ hρ
        (fun a ha => (hcenter a ha).1)
    have htransfer :=
      inward_successful_transfer_from_objects_proposed
        A D S (goodTwo D S sel) sel center ρ retained I hρ
        (fun a ha => (hretained a ha).1)
        (by
          intro a ha P hPI
          exact ⟨(Finset.mem_filter.mp (hI_sub a ha hPI)).1,
            hI_success a ha P hPI⟩)
    have hbudget :=
      inward_target_budget_from_objects_proposed
        A D S (goodTwo D S sel) sel ρ h0 hρ
    exact inward_bank_from_interfaces_proposed
      A D S (goodTwo D S sel) sel center ρ I hρ
      (fun a ha => (hcenter a ha).1)
      (by exact_mod_cast hd) hK hscale hnonzero htransfer hbudget hmass
  obtain ⟨t, Snext, ht, hSnext, _, _, hcard, hgain⟩ :=
    one_bit_iteration_step_from_O5_proposed
      A D S (goodTwo D S sel) ρ retained h0 houtwardBank hinwardBank
  subst Snext
  rcases hbranchClassification with _ | _
  · exact ⟨t, ht, hcard, hgain⟩
  · exact ⟨t, ht, hcard, hgain⟩

/-- Discharge the exact `hstep` hypothesis of O6's `sqrt_improvement'`.

Maximality is used only here, through `D.card = dimA A`, to invoke O6's
certified lower guard and scale identity for `K = KA A`. The conclusion is
the O6 binder itself, including both caps under the current-state
quantifier. -/
theorem o6_hstep_from_isUSF_proposed
    (hBLR :
      ∀ {p : ℕ}, p.Prime →
        ∀ S : Finset (ZMod p),
          (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
            ∃ T : Finset ℤ, ∃ φ : ZMod p → ℤ,
              IsAddFreimanIso 2 (↑S) (↑T) φ)
    {p : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) {C : ℝ}
    (hUSF : IsUSF A)
    (hdim : 0 < dimA A)
    (hC_object : 129024 ≤ C) :
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
                              (D + S)).card : ℕ) : ℝ)) := by
  intro D S hDsubA hD hDcard hd h0 hrect hcap
  have hscale :
      (A.card : ℝ) = (KA A : ℝ) * (D.card : ℝ) :=
    ka_scale_from_maximal_dissociated_proposed A D hDcard hdim
  have hK : (1 : ℝ) ≤ (KA A : ℝ) :=
    one_le_ka_of_maximal_dissociated_proposed
      A D hDsubA hDcard hdim
  exact sharpened_one_step_from_isUSF_proposed
    hBLR hp A D S hUSF hDsubA hD hd h0 hrect hcap
    hC_object hK hscale

end ObjectLayer
end BedertLab
