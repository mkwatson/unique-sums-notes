/-
# Object layer, O7a: rectification and simultaneous uniqueness

PROPOSED 2026-07-24 by the Codex proposal arm.
FROZEN 2026-07-24 by the Claude freeze arm: claim-type checklist (counting
lemma) run line by line; verification-battery freeze gate applied per
statement; back-translation trial (process-lab #45) run on all four
signatures with no statement/docstring mismatch; all four ambiguity flags
below adjudicated ACCEPTED as encoded. The `hBLR` binder was diffed
token-for-token against the charter Section 10 Option B display and matches
exactly, as a theorem parameter, in both theorems that carry it. All theorem
statements and both definitions are byte-unchanged from the proposal.
Statements are now trust boundaries: fills may not alter them; print
BLOCKED instead.

Authority: `candidates/bedert-omega/o7-charter-proposal.md`, Sections 1, 3,
and 10, approved with Option B in `attack-log.md` at approximately 21:15Z.
This file contains the two proposed trust-boundary definitions and the four
O7a theorem signatures. Every theorem body is `sorry`.

Source attribution is deliberately three-way:

* Bedert's printed rectification and simultaneous-selector steps are
  `sources/bedert/src/main.tex:123-133,516-522,532-541`.
* The campaign's sharpened arm consumes the resulting source selectors in
  `note-core/prose-proof-arm1.md` (A1.4)-(A1.7); it does not supply or claim
  a new rectification theorem.
* The independent blind arm follows the same selector and removal objects in
  `note-core/prose-proof-arm2-blind.md:49-70`; its restored displays are
  explicitly reconstructed, and there is no numbered blind selector display.

The external rectification interface is a theorem parameter with the exact
Option B signature. It is not a Lean axiom. At the encoded threshold
(order-2 Freiman isomorphism, `S.card ≤ logb 2 p`) the correct attribution
is Lev 2008, Theorem 1, not Bilu-Lev-Ruzsa: BLR's own Theorem 3.1 only
gives the weaker `logb 4 p` bound at this order. See
`candidates/bedert-omega/tailored-rectification.md` PHASE 1.2.

## AMBIGUITY FLAGS

1. Freiman-image packaging is open for freeze adjudication. The proposal
   follows Option B literally: `T : Finset ℤ` is existential data and
   `IsAddFreimanIso 2 (↑S) (↑T) φ` records the image relation. It does not
   additionally require `T = S.image φ`. Adding that equality, or replacing
   `T` by the image definitionally, would be a different trust boundary.
2. `IsSimultaneousUniqueSelector` uses a total function
   `Finset G → G`, constrained only on nonempty subsets of `S`. A dependent
   function on the subtype of nonempty subsets would be a different API.
3. The source selector is also total on `G`, matching O4. Its values outside
   `D` are ignored. The conclusion exposes O4's exact pointwise membership
   shape and states simultaneous uniqueness directly on the source fibres.
4. The cyclic cap is kept in O6's real convention and direction:
   `(S.card : ℝ) ≤ Real.logb 2 (p : ℝ)`. No natural-log or floor conversion
   is hidden in a definition.
-/
import BedertLab.ObjectLayer.O1Defs

namespace BedertLab
namespace ObjectLayer

/-- The finite-integer-image packaging of cyclic rectification.

Bedert printed step: `main.tex:123-133` states the rectification result for
small subsets of `ZMod p` (Bedert's Lemma cites Bilu-Lev-Ruzsa Theorem 3.1
there, but the stated threshold matches Lev 2008 Theorem 1, not BLR's own
weaker `log_4 p` bound; see the `hBLR` note below).
Campaign sharpened arm: this is upstream infrastructure only; arm 1 starts
using its simultaneous-selector consequence at (A1.4).
Blind arm: arm 2 independently reuses the same author-source selector step
but supplies no separate numbered rectification display. -/
def BLRRectifies (p : ℕ) (S : Finset (ZMod p)) : Prop :=
  ∃ T : Finset ℤ, ∃ φ : ZMod p → ℤ,
    IsAddFreimanIso 2 (↑S) (↑T) φ

/-- A single choice rule whose selected elements are jointly unique for all
two-fibre sum equations.

Bedert printed step: `main.tex:516-522` chooses the inverse image of the
maximum of every nonempty rectified image.
Campaign sharpened arm: `prose-proof-arm1.md` (A1.4) uses the induced
choices `s_u ∈ S_u`.
Blind arm: `prose-proof-arm2-blind.md:49-52` independently follows the same
simultaneous choice, without a numbered blind display. -/
def IsSimultaneousUniqueSelector
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (choose : Finset G → G) : Prop :=
  (∀ X : Finset G, X.Nonempty → X ⊆ S → choose X ∈ X) ∧
    ∀ X Y : Finset G,
      X.Nonempty →
        Y.Nonempty →
          X ⊆ S →
            Y ⊆ S →
              ∀ x ∈ X, ∀ y ∈ Y,
                x + y = choose X + choose Y →
                  x = choose X ∧ y = choose Y

/-- The single external O7 slot, exposed as an explicit theorem parameter.

Bedert printed step: `main.tex:130-133`, citing Bilu-Lev-Ruzsa Theorem 3.1;
the exact threshold encoded here (`log_2 p`, order 2) is however Lev 2008,
Theorem 1 (Combinatorica 28(4), 2008, 491-497, DOI 10.1007/s00493-008-2299-8),
not Bilu-Lev-Ruzsa's own Theorem 3.1, which proves only `log_4 p` at this
order.
Campaign sharpened arm: no new rectification claim is made; the campaign is
conditional on this exact interface.
Blind arm: the blind derivation begins after the author rectification and
does not independently prove the rectification interface.

The `hBLR` binder is byte-for-byte in the mathematical shape approved as
Option B in charter Section 10. -/
theorem blr_rectification_zmod_proposed
    (hBLR :
      ∀ {p : ℕ}, p.Prime →
        ∀ S : Finset (ZMod p),
          (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
            ∃ T : Finset ℤ, ∃ φ : ZMod p → ℤ,
              IsAddFreimanIso 2 (↑S) (↑T) φ)
    {p : ℕ} (hp : p.Prime) (S : Finset (ZMod p))
    (hS : (S.card : ℝ) ≤ Real.logb 2 (p : ℝ)) :
    BLRRectifies p S := by
  exact hBLR hp S hS

/-- A two-Freiman isomorphism into a finite integer set yields the
simultaneous selector.

Bedert printed step: this is exactly the maximum-image argument at
`main.tex:520-522`.
Campaign sharpened arm: its consequence is the family of choices used in
(A1.4)-(A1.7), not a new sharpened incidence conclusion.
Blind arm: the blind proof accepts the same simultaneous source choice before
constructing its good-pair family. -/
theorem simultaneous_selector_of_freiman_iso_proposed
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (T : Finset ℤ) (φ : G → ℤ)
    (hφ : IsAddFreimanIso 2 (↑S) (↑T) φ) :
    ∃ choose : Finset G → G,
      IsSimultaneousUniqueSelector S choose := by
  classical
  have hmax :
      ∀ X : Finset G, ∃ z : G,
        X.Nonempty → z ∈ X ∧ ∀ x ∈ X, φ x ≤ φ z := by
    intro X
    by_cases hX : X.Nonempty
    · let m := (X.image φ).max' (hX.image φ)
      have hm : m ∈ X.image φ := Finset.max'_mem _ _
      obtain ⟨z, hz, hφz⟩ := Finset.mem_image.mp hm
      refine ⟨z, fun _ => ⟨hz, ?_⟩⟩
      intro x hx
      rw [hφz]
      exact Finset.le_max' (X.image φ) (φ x)
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · exact ⟨0, fun h => (hX h).elim⟩
  choose choose hchoose using hmax
  refine ⟨choose, ?_, ?_⟩
  · intro X hX hXS
    exact (hchoose X hX).1
  · intro X Y hX hY hXS hYS x hx y hy hsum
    have hxS : x ∈ (↑S : Set G) := hXS hx
    have hyS : y ∈ (↑S : Set G) := hYS hy
    have hchooseXS : choose X ∈ (↑S : Set G) :=
      hXS (hchoose X hX).1
    have hchooseYS : choose Y ∈ (↑S : Set G) :=
      hYS (hchoose Y hY).1
    have hφsum :
        φ x + φ y = φ (choose X) + φ (choose Y) :=
      (hφ.add_eq_add hxS hyS hchooseXS hchooseYS).2 hsum
    have hxle : φ x ≤ φ (choose X) :=
      (hchoose X hX).2 x hx
    have hyle : φ y ≤ φ (choose Y) :=
      (hchoose Y hY).2 y hy
    have hφx : φ x = φ (choose X) := by omega
    have hφy : φ y = φ (choose Y) := by omega
    exact ⟨hφ.bijOn.injOn hxS hchooseXS hφx,
      hφ.bijOn.injOn hyS hchooseYS hφy⟩

/-- The conditional cyclic simultaneous-selector theorem with O6's exact
real-log cap.

Bedert printed step: composition of `main.tex:130-133` with
`main.tex:516-522`.
Campaign sharpened arm: supplies the pinned selectors later used by the
campaign incidence argument.
Blind arm: independently starts from the same pinned-selector object but does
not certify the external rectification premise (correctly attributed to
Lev 2008, not Bilu-Lev-Ruzsa; see the `hBLR` note above). -/
theorem simultaneous_selector_from_blr_proposed
    (hBLR :
      ∀ {p : ℕ}, p.Prime →
        ∀ S : Finset (ZMod p),
          (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
            ∃ T : Finset ℤ, ∃ φ : ZMod p → ℤ,
              IsAddFreimanIso 2 (↑S) (↑T) φ)
    {p : ℕ} (hp : p.Prime) (S : Finset (ZMod p))
    (hS : (S.card : ℝ) ≤ Real.logb 2 (p : ℝ)) :
    ∃ choose : Finset (ZMod p) → ZMod p,
      IsSimultaneousUniqueSelector S choose := by
  obtain ⟨T, φ, hφ⟩ := hBLR hp S hS
  exact simultaneous_selector_of_freiman_iso_proposed S T φ hφ

/-- Specialize a simultaneous subset selector to Bedert's source fibres
`S_d = {s ∈ S | d + s ∈ A}` and return the total selector required by O4.

Bedert printed step: the source fibres and their selected elements are
`main.tex:532-541`.
Campaign sharpened arm: (A1.4)-(A1.7) keeps these canonical endpoints
explicit before choosing repairs.
Blind arm: the adjudicated blind route uses the same centre-pinned selectors;
no blind display number is claimed.

The first conjunct is in O4's exact pointwise shape. The second conjunct
states simultaneous two-sum uniqueness on every pair of source fibres. -/
theorem source_selector_from_simultaneous_proposed
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A D S : Finset G) (choose : Finset G → G)
    (hchoose : IsSimultaneousUniqueSelector S choose)
    (hDsubA : D ⊆ A) (h0 : (0 : G) ∈ S) :
    ∃ sel : G → G,
      (∀ d ∈ D, sel d ∈ S ∧ d + sel d ∈ A) ∧
        ∀ d ∈ D, ∀ d' ∈ D,
          ∀ x ∈ S, d + x ∈ A →
            ∀ y ∈ S, d' + y ∈ A →
              x + y = sel d + sel d' →
                x = sel d ∧ y = sel d' := by
  let fibre : G → Finset G :=
    fun d => S.filter fun x => d + x ∈ A
  have hfibre_nonempty :
      ∀ d ∈ D, (fibre d).Nonempty := by
    intro d hd
    refine ⟨0, Finset.mem_filter.mpr ⟨h0, ?_⟩⟩
    simpa using hDsubA hd
  have hfibre_subset :
      ∀ d : G, fibre d ⊆ S := by
    intro d
    exact Finset.filter_subset _ _
  have hsel_exists :
      ∃ sel : G → G, ∀ d : G, sel d = choose (fibre d) :=
    ⟨fun d => choose (fibre d), fun _ => rfl⟩
  let sel : G → G := Classical.choose hsel_exists
  have hsel_spec : ∀ d : G, sel d = choose (fibre d) :=
    Classical.choose_spec hsel_exists
  refine ⟨sel, ?_, ?_⟩
  · intro d hd
    have hmem :=
      hchoose.1 (fibre d) (hfibre_nonempty d hd) (hfibre_subset d)
    rw [hsel_spec d]
    exact Finset.mem_filter.mp hmem
  · intro d hd d' hd' x hxS hdxA y hyS hdyA hsum
    have hx : x ∈ fibre d := Finset.mem_filter.mpr ⟨hxS, hdxA⟩
    have hy : y ∈ fibre d' := Finset.mem_filter.mpr ⟨hyS, hdyA⟩
    have hresult := hchoose.2 (fibre d) (fibre d')
      (hfibre_nonempty d hd) (hfibre_nonempty d' hd')
      (hfibre_subset d) (hfibre_subset d')
      x hx y hy (by simpa only [hsel_spec d, hsel_spec d'] using hsum)
    simpa only [hsel_spec d, hsel_spec d'] using hresult

end ObjectLayer
end BedertLab
