/-
# Object layer, O5: branch dichotomy and the banks

FROZEN 2026-07-24 by the Claude freeze arm — fill sorries only; BLOCKED if
unprovable as written. Statements changed at freeze: NONE (all ten theorem
statements are byte-identical to the Sol proposal; only this status header
was updated).

## Freeze record (2026-07-24, Claude freeze arm)

Checklist run (reference/claim-checklists.md, counting-lemma + pricing-chain
items; verification-battery freeze-gate addendum):

* Quantifier audit: every statement diffed against its cited display.
  `hbudget` is the GLOBAL sum over all labels (note-v3 (3.8)), not a per-t
  bound (the B-S3 trap); `hlocal`/`htransfer`/`hnonzero` are per-a as the
  sources and `inwardBank_core` require; the target is the u-side set
  `{u ∈ G^(1) : s_u - t ∈ S_u}` (note-v3 (3.7)), not an a-side count (the
  blind2 swap incident).
* Seam audit (pricing-chain item, byte-level): the final adapter's
  `hnonzero`/`htransfer`/`hbudget`/`hmass` match `SqrtChain.inwardBank_core`
  exactly under `H := starFibres`, `label a := a - (center a + sel (center
  a))`, `successful a := (I a).card`, `E t := (goodOne D S).filter (fun u =>
  sel u - t ∈ S.filter (fun r => u + r ∈ A))`, `d := (D.card : ℝ)`,
  `n := (A.card : ℝ)`; the redundant `(· : ℕ)` ascription on `card`
  elaborates away. O4 seam: `hstarMass` shape `d²/7 ≤ Σ q` equals
  `star_extraction_sharp_proposed`'s conclusion; `C₁ = 63` equals the
  certified `two_families_pairs` constant; `129024 ≤ C` equals the O4
  campaign contract.
* Floor/ceiling directions: local absorption and mass are floors, budget is
  a ceiling, outward gain non-strict (main.tex:712), inward gain and mass
  strict (note-v3 (3.5)/(3.11), `inwardBank_core`). All match.
* Constant recomputation from scratch: tie+retained give the outward count
  ≥ q/6 ≥ d²/(36n) = d/(36K) under `hscale`; inward
  1/6 - 6·63/129024 = 0.16373... > 1/7, so Σ|I| > Q/7 ≥ d²/49 strictly
  (arcB-s3 (2.3)-(2.7), note-v3 (3.5)); Q > 0 from d ≥ 10.
* Vacuity audit: every hypothesis set has a witness (degenerate `G2 = ∅`
  satisfies the conditional statements; the inward-control.md sec 3 woven
  family satisfies the full inward interface for every complete χ, and the
  mass hypotheses are satisfiable per that prose witness — deliberately NOT
  assumed here, matching the sources' conditional form).
* Junk-value audit: all divisions real and guarded (`hK : 1 ≤ K` wherever K
  divides in a derivation; `heavyFibres`' `6n` denominator collapses
  harmlessly when `A = ∅` since `fibreLabels ⊆ A`); no ℕ subtraction or ℕ
  division in any statement; `[Fintype G]` only on the budget and the final
  adapter (flag 9), matching `inwardBank_core`'s `[Fintype τ]`.
* Derivability line-check: each conclusion re-derived on paper from exactly
  the stated hypotheses (outward bank via `pairTarget` algebra +
  `hyDistinct`; label nonzero via `starFibres ⊆ A \ (D+S)` + `hcenter` +
  `hρ.1`; budget via `goodOne_sep` + `sub_subset_twoSsub` + `uside_budget`
  + `fibre_sum_eq`, with `E_t = ∅` off `S - S`; transfer via the structural
  injection `P ↦ (∑ P) - center a` on two-element centred pairs; the wall
  and mass stages per arcB-s3 (1.8)-(2.7)). `hsecond` is load-bearing in
  the wall statement: it supplies `u ∈ goodOne` in the success equation.
* Non-load-bearing hypotheses noted (kept deliberately, no deletion):
  `branch_classification_proposed`'s `hρ`/`hcenter`/`hretained` are not
  needed for its fill (the dichotomy is excluded middle over the exact
  complement filters); they document the (1.13)-(1.18) application context
  and are supplied by every downstream consumer.

All fourteen ambiguity flags below were adjudicated at freeze and are
honored by the statements as written; none required a change.

Statement skeletons only. Every theorem body is `sorry`. The charter source is
`candidates/bedert-omega/object-layer-charter.md:42-45`: O5 must derive the
outward `d/(36K)` gain and the four object-level hypotheses consumed by
`inwardBank_core`, with the successful-mass bound stated even if its fill must
be staged.

The object vocabulary is imported from O1-O4. In particular:

* `goodOne`, `fibreN`, `fibreCount`, `heavyFibres`, `starFibres`,
  `chosenY`, `FourthPowerCap`, and `HasSecondRemovalBound` are the certified
  objects used below;
* the u-side target is written literally as
  `{u ∈ goodOne D S | sel u - t ∈ {r ∈ S | u + r ∈ A}}`, so it is the
  object specialization of O2's budget rather than an a-side count;
* the four shared hypotheses retain the downstream names `hnonzero`,
  `htransfer`, `hbudget`, and `hmass` at the final adapter to
  `SqrtChain.inwardBank_core`.

## Ambiguity flags (adjudicated at freeze; all honored as written)

1. O4 does not formalize the complete dependent choice object
   `chi = (rho, center, retained, orientation)` from
   `conjecture-51-v2.md:181-303`. This file therefore quantifies total
   functions `center` and `retained`, constraining only their values on
   `starFibres`. Values off that finite domain are ignored.
2. O4's `IsOrientedRepresentationChoice` deliberately omits the upstream
   simultaneous-selector uniqueness and good-pair uniqueness consequences.
   The outward theorem exposes injectivity of `chosenY` on a retained star as
   `hyDistinct`; no derivation of that fact from the current O1-O4 API is
   silently claimed.
3. The retained-spoke lower bound is encoded exactly over naturals as
   `fibreCount <= 3 * retained.card`, matching O4's denominator-cleared star
   convention. The sources permit an arbitrary retained subset satisfying
   this bound; the proposal does not silently replace it by the full star.
4. Ties are outward: `2 * |outward| >= |retained|`. Consequently the
   all-inward alternative is strict:
   `2 * |inward| > |retained|`. This is the convention fixed by
   `conjecture-51-v2.md` (1.18) and Bedert `main.tex:704-716`.
5. The two branch shifts have opposite signs. The source outward shift is
   `center a + sel (center a) - a` (`main.tex:707-713`); the streamlined
   inward label is `a - (center a + sel (center a))`
   (`note-v3-draft.md` (3.6)). Both signs are kept explicitly.
6. Bedert's printed final case uses `2S-S` (`main.tex:731-742`). The one-bit
   inward update and the strict `d/(49K)` bank are later repaired interfaces,
   grounded in the source equations at `main.tex:716-724` and the audited
   incidence argument in `arcB-s3-attempt.md`. They are not attributed to a
   nonexistent source display.
7. A successful spoke is encoded using the canonical other endpoint
   `sum(P) - center a`. For a two-element retained pair containing the fixed
   centre this is the leaf. Success means that this leaf is in `goodOne` and
   that `chosenY` has the exact u-side target form. No uniqueness of a
   `D+S` decomposition of `chosenY` is assumed.
8. The local loss constant is fixed at the certified Two Families value
   `C1 = 63`, giving the stage
   `q_a / 6 - 63 * |S|^2 <= |I(a)|`. This local `e=d` absorption statement is
   the EXPECTED WALL. The later summation and constant arithmetic are separate
   stages and must not conceal it.
9. The target budget sums over the whole label type, as
   `inwardBank_core.hbudget` does. Thus only the budget and final inward-bank
   adapter add `[Fintype G]`; O1-O4 and the local counting statements remain
   valid for arbitrary additive commutative groups with finite subsets.
10. O1 defines `KA A` using `dimA A`, but O4 has no hypothesis identifying
    `D.card` with `dimA A`. O5 therefore uses a real `K` together with the
    explicit scale identity `(A.card : R) = K * (D.card : R)`. Identifying it
    with `KA A` belongs to O6.
11. A new-point bank is represented by
    `((A ∩ (D + (S + {0,t}))) \ (D + S)).card`. The one-bit size statement is
    written for `S + {0,t}`, the pointwise form of `S ∪ (S+t)`.
12. The outward gain is non-strict, as in Bedert `main.tex:712`; the inward
    gain and successful mass are strict, matching `inwardBank_core`.
13. `IsUSF A` is not repeated in every O5 statement because the current O4
    seam begins after a representation choice `hρ` has been supplied. Deriving
    that choice from `IsUSF` and the missing O3 second-removal objects is an
    upstream obligation, not a claim of this file. This also preserves the
    scope warning in `inward-control.md`: its woven family is a valid local
    control but is not globally USF.
14. `HasSecondRemovalBound` is still an exposed hypothesis because O4 records
    that the certified O3 file has not yet produced the second-removal object.
    O5 does not silently promote it to certified O3 output.
-/
import BedertLab.ObjectLayer.O2Budget
import BedertLab.ObjectLayer.O4Star
import BedertLab.ObjectLayer.O5Multiplicity
import BedertLab.SqrtChain

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Object-level outward-tie/inward-strict classification of the retained
stars.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: the retained-spoke partition (1.17)-(1.18) in
`conjecture-51-v2.md:222-253`, with the outward tie convention at Bedert
`main.tex:704-716`.
Downstream: selects either `outward_bank_from_objects_proposed`, which supplies
the `d/(36*K)` summand of `one_bit_budget_steps.htelescope`, or the four inward
interfaces consumed by `inwardBank_core`. -/
theorem branch_classification_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G))
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hcenter :
      ∀ a ∈ starFibres A D S G2 ρ,
        center a ∈ D ∧
          fibreCount G2 ρ a ≤
            3 * fibreDegree G2 ρ a (center a))
    (hretained :
      ∀ a ∈ starFibres A D S G2 ρ,
        retained a ⊆
            (fibreN G2 ρ a).filter (fun P => center a ∈ P) ∧
          fibreCount G2 ρ a ≤ 3 * (retained a).card) :
    (∃ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card) ∨
      ∀ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card := by
  classical
  by_cases hout :
      ∃ a ∈ starFibres A D S G2 ρ,
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

/-- The outward `d/(36K)` bank from an outward retained O4 star.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: `N(a)`, the fixed centre, and the translated output equation at Bedert
`main.tex:635-648,696-704`; the shift and gain calculation are exactly
`main.tex:707-713`.
Downstream: supplies the outward step gain in
`one_bit_budget_steps.htelescope` and `sqrt_improvement.htelescope`; the
cardinality bound on `S + {0,t}` supplies an instance of
`one_bit_growth.hstep`. -/
theorem outward_bank_from_objects_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G)) {a : G} {K : ℝ}
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hK : 1 ≤ K)
    (hscale : (A.card : ℝ) = K * (D.card : ℝ))
    (ha : a ∈ starFibres A D S G2 ρ)
    (hcenter :
      center a ∈ D ∧
        fibreCount G2 ρ a ≤
          3 * fibreDegree G2 ρ a (center a))
    (hretained :
      retained a ⊆
          (fibreN G2 ρ a).filter (fun P => center a ∈ P) ∧
        fibreCount G2 ρ a ≤ 3 * (retained a).card)
    (hyDistinct :
      Set.InjOn (chosenY ρ) (↑(retained a) : Set (Finset G)))
    (houtward :
      2 *
          ((retained a).filter fun P =>
            chosenY ρ P ∉ D + S).card ≥
        (retained a).card) :
    ∃ t : G,
      t = center a + sel (center a) - a ∧
        t ≠ 0 ∧
          (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
            (D.card : ℝ) / (36 * K) ≤
              ((((A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)).card :
                ℕ) : ℝ) := by
  classical
  let t := center a + sel (center a) - a
  let outward :=
    (retained a).filter fun P => chosenY ρ P ∉ D + S
  let newPoints := (A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)
  have ha_label : a ∈ fibreLabels A D S := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have ha_not_mem : a ∉ D + S := (Finset.mem_sdiff.mp ha_label).2
  have ht_ne : t ≠ 0 := by
    intro ht
    have hcenterS : center a + sel (center a) ∈ D + S :=
      Finset.add_mem_add hcenter.1 (hρ.1 (center a) hcenter.1).1
    have hcenter_eq : center a + sel (center a) = a :=
      sub_eq_zero.mp ht
    rw [hcenter_eq] at hcenterS
    exact ha_not_mem hcenterS
  have hsize : (S + ({0, t} : Finset G)).card ≤ 2 * S.card := by
    have hpair_card : ({0, t} : Finset G).card ≤ 2 := by
      calc
        ({0, t} : Finset G).card ≤ ({t} : Finset G).card + 1 :=
          Finset.card_insert_le 0 {t}
        _ = 2 := by simp
    calc
      (S + ({0, t} : Finset G)).card ≤
          S.card * ({0, t} : Finset G).card :=
        Finset.card_add_le
      _ ≤ S.card * 2 := by
        exact Nat.mul_le_mul_left S.card hpair_card
      _ = 2 * S.card := by omega
  have himage : outward.image (chosenY ρ) ⊆ newPoints := by
    intro y hy
    obtain ⟨P, hPout, rfl⟩ := Finset.mem_image.mp hy
    have hPdata := Finset.mem_filter.mp hPout
    have hPfibre := hretained.1 hPdata.1
    have hPfibre_data := Finset.mem_filter.mp hPfibre
    have hPN_data := Finset.mem_filter.mp hPfibre_data.1
    have hPG2 : P ∈ G2 := hPN_data.1
    have hchosenX : chosenX ρ P = a := hPN_data.2
    obtain ⟨hPpow, _, hchosenY_A, htarget⟩ := hρ.2 P hPG2
    have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hPpow).2
    have hPsubD : P ⊆ D := (Finset.mem_powersetCard.mp hPpow).1
    have hcenterP : center a ∈ P := hPfibre_data.2
    have herase_card : (P.erase (center a)).card = 1 := by
      rw [Finset.card_erase_of_mem hcenterP, hPcard]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp herase_card
    have hv_erase : v ∈ P.erase (center a) := by simp [hv]
    have hv_ne : v ≠ center a := (Finset.mem_erase.mp hv_erase).1
    have hP_eq : P = {center a, v} := by
      rw [← Finset.insert_erase hcenterP, hv]
    have hvD : v ∈ D := hPsubD (by simp [hP_eq])
    have hselvS : sel v ∈ S := (hρ.1 v hvD).1
    have htarget' :
        a + chosenY ρ P =
          (center a + sel (center a)) + (v + sel v) := by
      calc
        a + chosenY ρ P =
            chosenX ρ P + chosenY ρ P := by rw [hchosenX]
        _ = pairTarget sel P := htarget
        _ = (center a + sel (center a)) + (v + sel v) := by
          simp [pairTarget, hP_eq, hv_ne.symm]
    have hy_eq :
        chosenY ρ P = v + (sel v + t) := by
      calc
        chosenY ρ P = (a + chosenY ρ P) - a := by abel
        _ = ((center a + sel (center a)) + (v + sel v)) - a := by
          rw [htarget']
        _ = v + (sel v + t) := by
          dsimp [t]
          abel
    rw [Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨⟨hchosenY_A, ?_⟩, hPdata.2⟩
    rw [Finset.mem_add]
    refine ⟨v, hvD, sel v + t, ?_, hy_eq.symm⟩
    rw [Finset.mem_add]
    exact ⟨sel v, hselvS, t, by simp, rfl⟩
  have houtward_card :
      outward.card ≤ newPoints.card := by
    calc
      outward.card = (outward.image (chosenY ρ)).card :=
        (Finset.card_image_of_injOn
          (hyDistinct.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))).symm
      _ ≤ newPoints.card := Finset.card_le_card himage
  have hthreshold :
      (D.card : ℝ) ^ 2 / (6 * (A.card : ℝ)) ≤
        (fibreCount G2 ρ a : ℝ) := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
  have hfibre_outward :
      fibreCount G2 ρ a ≤ 6 * outward.card := by
    calc
      fibreCount G2 ρ a ≤ 3 * (retained a).card := hretained.2
      _ ≤ 3 * (2 * outward.card) := Nat.mul_le_mul_left 3 houtward
      _ = 6 * outward.card := by ring
  have hbank :
      (D.card : ℝ) / (36 * K) ≤ (outward.card : ℝ) := by
    by_cases hDzero : D.card = 0
    · simp [hDzero]
    · have hd_pos : 0 < (D.card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hDzero
      have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
      have hfibre_outward_real :
          (fibreCount G2 ρ a : ℝ) ≤ 6 * (outward.card : ℝ) := by
        exact_mod_cast hfibre_outward
      calc
        (D.card : ℝ) / (36 * K) =
            ((D.card : ℝ) ^ 2 / (6 * (A.card : ℝ))) / 6 := by
          rw [hscale]
          field_simp
          ring
        _ ≤ (fibreCount G2 ρ a : ℝ) / 6 :=
          div_le_div_of_nonneg_right hthreshold (by norm_num)
        _ ≤ (outward.card : ℝ) := by linarith
  refine ⟨t, rfl, ht_ne, hsize, ?_⟩
  change (D.card : ℝ) / (36 * K) ≤ (newPoints.card : ℝ)
  exact hbank.trans (by exact_mod_cast houtward_card)

/-- The centre-pinned inward label is nonzero on every O4 star fibre.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: O4's labels lie in `A \ (D+S)`, transcribing Bedert
`main.tex:635-648`; the fixed-centre equations are `main.tex:696-704`.
Downstream: discharges `inwardBank_core.hnonzero` for
`label a = a - (center a + sel (center a))`. -/
theorem inward_label_nonzero_from_objects_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hcenter :
      ∀ a ∈ starFibres A D S G2 ρ, center a ∈ D) :
    ∀ a ∈ starFibres A D S G2 ρ,
      a - (center a + sel (center a)) ≠ 0 := by
  intro a ha hzero
  have ha_label : a ∈ fibreLabels A D S :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have ha_not_mem : a ∉ D + S := (Finset.mem_sdiff.mp ha_label).2
  have hcenterD : center a ∈ D := hcenter a ha
  have hcenterS : center a + sel (center a) ∈ D + S :=
    Finset.add_mem_add hcenterD (hρ.1 (center a) hcenterD).1
  have ha_eq : a = center a + sel (center a) := sub_eq_zero.mp hzero
  rw [← ha_eq] at hcenterS
  exact ha_not_mem hcenterS

/-- The complete u-side target budget specialized to the O1-O4 objects.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: `S_u` is Bedert `main.tex:532-540`; the original `2S-2S` removal is
`main.tex:541-546`. O2's `uside_budget` and `fibre_sum_eq` certify the
injection and the change of variables used here.
Downstream: discharges `inwardBank_core.hbudget` with
`E t = {u ∈ goodOne D S | sel u - t ∈ S_u}`. -/
theorem inward_target_budget_from_objects_proposed
    [Fintype G]
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel : G → G) (ρ : RepresentationChoice G)
    (h0 : (0 : G) ∈ S)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ) :
    (∑ t : G,
        ((((goodOne D S).filter fun u =>
          sel u - t ∈ (S.filter fun r => u + r ∈ A)).card : ℕ) : ℝ)) ≤
      (A.card : ℝ) := by
  classical
  let Su : G → Finset G := fun u => S.filter fun r => u + r ∈ A
  let E : G → Finset G := fun t =>
    (goodOne D S).filter fun u => sel u - t ∈ Su u
  have hSu : ∀ u ∈ goodOne D S, Su u ⊆ S := by
    intro u hu r hr
    exact (Finset.mem_filter.mp hr).1
  have hmem : ∀ u ∈ goodOne D S, ∀ r ∈ Su u, u + r ∈ A := by
    intro u hu r hr
    exact (Finset.mem_filter.mp hr).2
  have hsel : ∀ u ∈ goodOne D S, sel u ∈ Su u := by
    intro u hu
    have huD : u ∈ D := (Finset.mem_sdiff.mp hu).1
    exact Finset.mem_filter.mpr
      ⟨(hρ.1 u huD).1, (hρ.1 u huD).2⟩
  have havoid :
      ∀ u ∈ goodOne D S, ∀ v ∈ goodOne D S,
        u - v ∈ S - S → u = v := by
    intro u hu v hv huv
    exact goodOne_sep D S u hu v hv (sub_subset_twoSsub S h0 huv)
  have huside :
      ∑ u ∈ goodOne D S, (Su u).card ≤ A.card :=
    uside_budget A (goodOne D S) S Su hSu hmem havoid
  have hfibre :
      ∑ t ∈ S - S, (E t).card =
        ∑ u ∈ goodOne D S, (Su u).card := by
    exact fibre_sum_eq (goodOne D S) S Su sel hSu hsel
  have hE_empty (t : G) (ht : t ∉ S - S) : E t = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro u hu hut
    have huD : u ∈ D := (Finset.mem_sdiff.mp hu).1
    have hselS : sel u ∈ S := (hρ.1 u huD).1
    have hrS : sel u - t ∈ S :=
      (Finset.mem_filter.mp hut).1
    apply ht
    rw [Finset.mem_sub]
    exact ⟨sel u, hselS, sel u - t, hrS, by abel⟩
  have hall :
      (∑ t : G, (E t).card) =
        ∑ t ∈ S - S, (E t).card := by
    symm
    simpa using
      (Finset.sum_subset (Finset.subset_univ (S - S))
        (fun t _ ht => by simp [hE_empty t ht]))
  have hnat : (∑ t : G, (E t).card) ≤ A.card := by
    rw [hall, hfibre]
    exact huside
  change (∑ t : G, ((E t).card : ℝ)) ≤ (A.card : ℝ)
  exact_mod_cast hnat

/-- Every successful inward spoke injects into its centre-pinned u-side
target.

The other vertex of a retained two-element pair is written canonically as
`(sum P) - center a`. The hypothesis `hI_success` is the exact successful
equation produced by the local absorption stage.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: the inward decomposition and fixed-centre equation are Bedert
`main.tex:716-724`; the successful cancellation is the `e=d` argument at
`main.tex:726-762`.
Downstream: discharges `inwardBank_core.htransfer` for
`successful a = (I a).card`. -/
theorem inward_successful_transfer_from_objects_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (retained I : G → Finset (Finset G))
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hretained :
      ∀ a ∈ starFibres A D S G2 ρ,
        retained a ⊆
          (fibreN G2 ρ a).filter (fun P => center a ∈ P))
    (hI_success :
      ∀ a ∈ starFibres A D S G2 ρ, ∀ P ∈ I a,
        P ∈ retained a ∧
          (let u := (∑ x ∈ P, x) - center a;
            u ∈ goodOne D S ∧
              sel u - (a - (center a + sel (center a))) ∈ S ∧
                chosenY ρ P =
                  u + (sel u - (a - (center a + sel (center a)))))) :
    ∀ a ∈ starFibres A D S G2 ρ,
      (I a).card ≤
        ((goodOne D S).filter fun u =>
          sel u - (a - (center a + sel (center a))) ∈
            (S.filter fun r => u + r ∈ A)).card := by
  classical
  intro a ha
  let f : Finset G → G := fun P => (∑ x ∈ P, x) - center a
  let E :=
    (goodOne D S).filter fun u =>
      sel u - (a - (center a + sel (center a))) ∈
        (S.filter fun r => u + r ∈ A)
  have hrecover (P : Finset G) (hPI : P ∈ I a) :
      P = {center a, f P} := by
    have hsuccess := hI_success a ha P hPI
    dsimp only at hsuccess
    have hPretained : P ∈ retained a := hsuccess.1
    have hPfibre := hretained a ha hPretained
    have hPfibre_data := Finset.mem_filter.mp hPfibre
    have hPN_data := Finset.mem_filter.mp hPfibre_data.1
    have hPG2 : P ∈ G2 := hPN_data.1
    have hPpow := (hρ.2 P hPG2).1
    have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hPpow).2
    have hcenterP : center a ∈ P := hPfibre_data.2
    have herase_card : (P.erase (center a)).card = 1 := by
      rw [Finset.card_erase_of_mem hcenterP, hPcard]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp herase_card
    have hv_erase : v ∈ P.erase (center a) := by simp [hv]
    have hv_ne : v ≠ center a := (Finset.mem_erase.mp hv_erase).1
    have hP_eq : P = {center a, v} := by
      rw [← Finset.insert_erase hcenterP, hv]
    have hf_eq : f P = v := by
      dsimp [f]
      rw [hP_eq]
      simp [hv_ne.symm]
    calc
      P = {center a, v} := hP_eq
      _ = {center a, f P} := by rw [hf_eq]
  have hf_injective : Set.InjOn f (↑(I a) : Set (Finset G)) := by
    intro P hPI Q hQI hPQ
    rw [hrecover P hPI, hrecover Q hQI, hPQ]
  have himage : (I a).image f ⊆ E := by
    intro u hu
    obtain ⟨P, hPI, rfl⟩ := Finset.mem_image.mp hu
    have hsuccess := hI_success a ha P hPI
    dsimp only at hsuccess
    have hPretained : P ∈ retained a := hsuccess.1
    have hPfibre := hretained a ha hPretained
    have hPN_data :=
      Finset.mem_filter.mp (Finset.mem_filter.mp hPfibre).1
    have hPG2 : P ∈ G2 := hPN_data.1
    have hchosenY_A : chosenY ρ P ∈ A := (hρ.2 P hPG2).2.2.1
    obtain ⟨hu_good, hrS, hy_eq⟩ := hsuccess.2
    rw [Finset.mem_filter]
    refine ⟨hu_good, Finset.mem_filter.mpr ⟨hrS, ?_⟩⟩
    rw [← hy_eq]
    exact hchosenY_A
  change (I a).card ≤ E.card
  calc
    (I a).card = ((I a).image f).card :=
      (Finset.card_image_of_injOn hf_injective).symm
    _ ≤ E.card := Finset.card_le_card himage

/-- EXPECTED WALL: local successful-spoke absorption in every inward O4 star.

The theorem freezes the full local output: a family `I` of inward retained
spokes, the exact u-side success equation for each member, and the loss bound
`q_a/6 - 63|S|^2 <= |I(a)|`. The later mass theorem is intentionally a
separate arithmetic stage.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45,61-63`.
Source: Bedert's inward decomposition, fixed-centre equation, and `e=d`
pigeonhole argument at `main.tex:716-762`; the accumulated successful-spoke
form is `arcB-s3-attempt.md` (1.8)-(2.7) and `note-v3-draft.md` (3.4).
Downstream: supplies the local hypothesis of
`inward_mass_from_local_proposed`, and its success equation supplies
`inward_successful_transfer_from_objects_proposed.hI_success`. -/
theorem inward_successful_spokes_local_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G))
    (hD : DissociatedF D)
    (hsecond : HasSecondRemovalBound D S G2)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hretained :
      ∀ a ∈ starFibres A D S G2 ρ,
        retained a ⊆
            (fibreN G2 ρ a).filter (fun P => center a ∈ P) ∧
          fibreCount G2 ρ a ≤ 3 * (retained a).card)
    (hinward :
      ∀ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card) :
    ∃ I : G → Finset (Finset G),
      (∀ a ∈ starFibres A D S G2 ρ,
        I a ⊆
          (retained a).filter (fun P => chosenY ρ P ∈ D + S)) ∧
      (∀ a ∈ starFibres A D S G2 ρ, ∀ P ∈ I a,
        (let u := (∑ x ∈ P, x) - center a;
          u ∈ goodOne D S ∧
            sel u - (a - (center a + sel (center a))) ∈ S ∧
              chosenY ρ P =
                u + (sel u - (a - (center a + sel (center a)))))) ∧
      (∀ a ∈ starFibres A D S G2 ρ,
        (fibreCount G2 ρ a : ℝ) / 6 -
            63 * (S.card : ℝ) ^ 2 ≤
          ((I a).card : ℝ)) := by
  exact inward_successful_spokes_local_from_multiplicity_proposed
    A D S G2 sel center ρ retained hD hsecond hρ hretained hinward

/-- Arithmetic summation stage from the local absorption estimate to strict
successful mass `d^2/49`.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: the sharp star mass starts from Bedert `main.tex:624-704`; the cap and
summed absorption are the audited displays `note-v3-draft.md` (3.4)-(3.5).
There is no Bedert display for the repaired constant `49`.
Downstream: its conclusion is exactly `inwardBank_core.hmass` with
`successful a = (I a).card`. -/
theorem inward_mass_from_local_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (ρ : RepresentationChoice G) (I : G → Finset (Finset G))
    {C : ℝ}
    (hDsubA : D ⊆ A)
    (h0 : (0 : G) ∈ S)
    (hd : 10 ≤ D.card)
    (hC : 129024 ≤ C)
    (hcap : FourthPowerCap A D S C)
    (hstarMass :
      (D.card : ℝ) ^ 2 / 7 ≤
        ∑ a ∈ starFibres A D S G2 ρ,
          (fibreCount G2 ρ a : ℝ))
    (hlocal :
      ∀ a ∈ starFibres A D S G2 ρ,
        (fibreCount G2 ρ a : ℝ) / 6 -
            63 * (S.card : ℝ) ^ 2 ≤
          ((I a).card : ℝ)) :
    (D.card : ℝ) ^ 2 / 49 <
      ∑ a ∈ starFibres A D S G2 ρ, ((I a).card : ℝ) := by
  classical
  let H := starFibres A D S G2 ρ
  let Q : ℝ := ∑ a ∈ H, (fibreCount G2 ρ a : ℝ)
  let R : ℝ := ∑ a ∈ H, ((I a).card : ℝ)
  let d : ℝ := D.card
  let n : ℝ := A.card
  let s : ℝ := S.card
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hn_pos : 0 < n := by
    have hdn' : d ≤ n := by
      dsimp [d, n]
      exact_mod_cast Finset.card_le_card hDsubA
    exact lt_of_lt_of_le hd_pos hdn'
  have hs_one : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hdn : d ≤ n := by
    dsimp [d, n]
    exact_mod_cast Finset.card_le_card hDsubA
  have hd4n4 : d ^ 4 ≤ n ^ 4 := by
    gcongr
  have hden : 129024 * d ^ 4 ≤ C * n ^ 4 := by
    calc
      129024 * d ^ 4 ≤ C * d ^ 4 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ C * n ^ 4 :=
        mul_le_mul_of_nonneg_left hd4n4 hC_pos.le
  have hcap' : s ^ 4 ≤ d ^ 6 / (C * n ^ 5) := by
    exact hcap
  have hcap_mul : s ^ 4 * (C * n ^ 5) ≤ d ^ 6 :=
    (le_div_iff₀ (mul_pos hC_pos (by positivity))).mp hcap'
  have hs2s4 : s ^ 2 ≤ s ^ 4 := by
    nlinarith [sq_nonneg (s ^ 2 - 1)]
  have hmul_den :
      (s ^ 4 * n) * (129024 * d ^ 4) ≤
        (s ^ 4 * n) * (C * n ^ 4) :=
    mul_le_mul_of_nonneg_left hden (mul_nonneg (by positivity) hn_pos.le)
  have hs4_scaled :
      (129024 * n * s ^ 4) * d ^ 4 ≤ d ^ 2 * d ^ 4 := by
    calc
      (129024 * n * s ^ 4) * d ^ 4 =
          (s ^ 4 * n) * (129024 * d ^ 4) := by ring
      _ ≤ (s ^ 4 * n) * (C * n ^ 4) := hmul_den
      _ = s ^ 4 * (C * n ^ 5) := by ring
      _ ≤ d ^ 6 := hcap_mul
      _ = d ^ 2 * d ^ 4 := by ring
  have hs2_scaled_mul :
      (129024 * n * s ^ 2) * d ^ 4 ≤ d ^ 2 * d ^ 4 := by
    calc
      (129024 * n * s ^ 2) * d ^ 4 ≤
          (129024 * n * s ^ 4) * d ^ 4 := by
        gcongr
      _ ≤ d ^ 2 * d ^ 4 := hs4_scaled
  have hs2_scaled : 129024 * n * s ^ 2 ≤ d ^ 2 :=
    le_of_mul_le_mul_right hs2_scaled_mul (by positivity)
  have hthreshold :
      ∀ a ∈ H, d ^ 2 / (6 * n) ≤ (fibreCount G2 ρ a : ℝ) := by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
  have hthreshold_sum :
      (H.card : ℝ) * (d ^ 2 / (6 * n)) ≤ Q := by
    calc
      (H.card : ℝ) * (d ^ 2 / (6 * n)) =
          ∑ a ∈ H, d ^ 2 / (6 * n) := by simp
      _ ≤ ∑ a ∈ H, (fibreCount G2 ρ a : ℝ) :=
        Finset.sum_le_sum fun a ha => hthreshold a ha
      _ = Q := rfl
  have hH_scaled :
      (H.card : ℝ) * d ^ 2 ≤ 6 * n * Q := by
    have htmp :
        (H.card : ℝ) * d ^ 2 / (6 * n) ≤ Q := by
      calc
        (H.card : ℝ) * d ^ 2 / (6 * n) =
            (H.card : ℝ) * (d ^ 2 / (6 * n)) := by ring
        _ ≤ Q := hthreshold_sum
    have hscaled :
        (H.card : ℝ) * d ^ 2 ≤ Q * (6 * n) :=
      (div_le_iff₀ (show 0 < 6 * n by positivity)).mp htmp
    calc
      (H.card : ℝ) * d ^ 2 ≤ Q * (6 * n) := hscaled
      _ = 6 * n * Q := by ring
  have hloss_pre :
      129024 * n * s ^ 2 * (H.card : ℝ) ≤ 6 * n * Q := by
    calc
      129024 * n * s ^ 2 * (H.card : ℝ) ≤
          d ^ 2 * (H.card : ℝ) := by
        gcongr
      _ = (H.card : ℝ) * d ^ 2 := by ring
      _ ≤ 6 * n * Q := hH_scaled
  have hloss_cancel :
      129024 * s ^ 2 * (H.card : ℝ) ≤ 6 * Q := by
    apply le_of_mul_le_mul_left _ hn_pos
    convert hloss_pre using 1 <;> ring
  have hloss :
      63 * s ^ 2 * (H.card : ℝ) ≤
        (6 * 63 / 129024 : ℝ) * Q := by
    nlinarith
  have hlocal_sum :
      (∑ a ∈ H,
          ((fibreCount G2 ρ a : ℝ) / 6 - 63 * s ^ 2)) ≤ R := by
    calc
      (∑ a ∈ H,
          ((fibreCount G2 ρ a : ℝ) / 6 - 63 * s ^ 2)) ≤
          ∑ a ∈ H, ((I a).card : ℝ) :=
        Finset.sum_le_sum fun a ha => hlocal a ha
      _ = R := rfl
  have hsum_q :
      (∑ a ∈ H, (fibreCount G2 ρ a : ℝ) / 6) = Q / 6 := by
    dsimp [Q]
    rw [Finset.sum_div]
  have hsum_loss :
      (∑ _a ∈ H, 63 * s ^ 2) =
        63 * s ^ 2 * (H.card : ℝ) := by
    simp
    ring
  have hR_lower :
      Q / 6 - 63 * s ^ 2 * (H.card : ℝ) ≤ R := by
    rw [Finset.sum_sub_distrib, hsum_q, hsum_loss] at hlocal_sum
    exact hlocal_sum
  change d ^ 2 / 49 < R
  change d ^ 2 / 7 ≤ Q at hstarMass
  nlinarith [show 0 < d ^ 2 by positivity]

/-- Full object-level successful-mass statement, with the expected wall
visible through the staged theorem immediately above rather than hidden in a
single scalar premise.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45,61-63`.
Source: Bedert `main.tex:624-704,716-762`, followed by the audited repaired
absorption `note-v3-draft.md` (3.4)-(3.5). The woven control at
`inward-control.md:257-345` satisfies this interface for every complete local
choice while failing the separate global-USF input.
Downstream: returns a concrete `I` together with the success equation needed
for `inwardBank_core.htransfer` and the strict inequality needed for
`inwardBank_core.hmass`. -/
theorem inward_mass_bound_from_objects_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G)) {C : ℝ}
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (h0 : (0 : G) ∈ S)
    (hd : 10 ≤ D.card)
    (hC : 129024 ≤ C)
    (hcap : FourthPowerCap A D S C)
    (hsecond : HasSecondRemovalBound D S G2)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hretained :
      ∀ a ∈ starFibres A D S G2 ρ,
        retained a ⊆
            (fibreN G2 ρ a).filter (fun P => center a ∈ P) ∧
          fibreCount G2 ρ a ≤ 3 * (retained a).card)
    (hinward :
      ∀ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card) :
    ∃ I : G → Finset (Finset G),
      (∀ a ∈ starFibres A D S G2 ρ,
        I a ⊆
          (retained a).filter (fun P => chosenY ρ P ∈ D + S)) ∧
      (∀ a ∈ starFibres A D S G2 ρ, ∀ P ∈ I a,
        (let u := (∑ x ∈ P, x) - center a;
          u ∈ goodOne D S ∧
            sel u - (a - (center a + sel (center a))) ∈ S ∧
              chosenY ρ P =
                u + (sel u - (a - (center a + sel (center a)))))) ∧
      (D.card : ℝ) ^ 2 / 49 <
        ∑ a ∈ starFibres A D S G2 ρ, ((I a).card : ℝ) := by
  obtain ⟨I, hI_sub, hI_success, hlocal⟩ :=
    inward_successful_spokes_local_proposed
      A D S G2 sel center ρ retained hD hsecond hρ hretained hinward
  have hstarMass :
      (D.card : ℝ) ^ 2 / 7 ≤
        ∑ a ∈ starFibres A D S G2 ρ,
          (fibreCount G2 ρ a : ℝ) :=
    (star_extraction_sharp_proposed
      A D S G2 sel ρ hDsubA hD h0 hd hC hcap hsecond hρ).1
  refine ⟨I, hI_sub, hI_success, ?_⟩
  exact inward_mass_from_local_proposed
    A D S G2 ρ I hDsubA h0 hd hC hcap hstarMass hlocal

/-- Exact object specialization of the certified abstract inward bank.

The shared argument names and shapes below are deliberately identical to
`SqrtChain.inwardBank_core`: `hnonzero`, `htransfer`, `hbudget`, and `hmass`.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: the centre-pinned label uses Bedert `main.tex:696-704,721-724`; the
one-bit inward bank is the audited repaired conclusion
`note-v3-draft.md` (3.6)-(3.11).
Downstream: supplies the inward `d/(49*K)` step in
`one_bit_budget_steps.htelescope` and `sqrt_improvement.htelescope`; the
one-bit size bound supplies `one_bit_growth.hstep`. -/
theorem inward_bank_from_interfaces_proposed
    [Fintype G]
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (I : G → Finset (Finset G)) {K : ℝ}
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hcenter :
      ∀ a ∈ starFibres A D S G2 ρ, center a ∈ D)
    (hd : (10 : ℝ) ≤ (D.card : ℝ))
    (hK : 1 ≤ K)
    (hscale : (A.card : ℝ) = K * (D.card : ℝ))
    (hnonzero :
      ∀ a ∈ starFibres A D S G2 ρ,
        a - (center a + sel (center a)) ≠ 0)
    (htransfer :
      ∀ a ∈ starFibres A D S G2 ρ,
        (I a).card ≤
          ((goodOne D S).filter fun u =>
            sel u - (a - (center a + sel (center a))) ∈
              (S.filter fun r => u + r ∈ A)).card)
    (hbudget :
      (∑ t : G,
          ((((goodOne D S).filter fun u =>
            sel u - t ∈ (S.filter fun r => u + r ∈ A)).card : ℕ) : ℝ)) ≤
        (A.card : ℝ))
    (hmass :
      (D.card : ℝ) ^ 2 / 49 <
        ∑ a ∈ starFibres A D S G2 ρ, ((I a).card : ℝ)) :
    ∃ t : G,
      t ≠ 0 ∧
        (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
          (D.card : ℝ) / (49 * K) <
            ((((A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)).card :
              ℕ) : ℝ) := by
  classical
  let H := starFibres A D S G2 ρ
  let label : G → G := fun a => a - (center a + sel (center a))
  let successful : G → ℕ := fun a => (I a).card
  let E : G → Finset G := fun t =>
    (goodOne D S).filter fun u =>
      sel u - t ∈ (S.filter fun r => u + r ∈ A)
  obtain ⟨t, ht_ne, hpopular⟩ :=
    inwardBank_core H label successful E
      (d := (D.card : ℝ)) (n := (A.card : ℝ)) (K := K)
      hd hK hscale hnonzero htransfer hbudget hmass
  let popular := H.filter fun a => label a = t
  let newPoints := (A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)
  have hsize : (S + ({0, t} : Finset G)).card ≤ 2 * S.card := by
    have hpair_card : ({0, t} : Finset G).card ≤ 2 := by
      calc
        ({0, t} : Finset G).card ≤ ({t} : Finset G).card + 1 :=
          Finset.card_insert_le 0 {t}
        _ = 2 := by simp
    calc
      (S + ({0, t} : Finset G)).card ≤
          S.card * ({0, t} : Finset G).card :=
        Finset.card_add_le
      _ ≤ S.card * 2 := Nat.mul_le_mul_left S.card hpair_card
      _ = 2 * S.card := by omega
  have hpopular_sub : popular ⊆ newPoints := by
    intro a ha
    have ha_data := Finset.mem_filter.mp ha
    have haH : a ∈ H := ha_data.1
    have hlabel : label a = t := ha_data.2
    have ha_fibre : a ∈ fibreLabels A D S :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp haH).1).1
    have haA : a ∈ A := (Finset.mem_sdiff.mp ha_fibre).1
    have ha_not : a ∉ D + S := (Finset.mem_sdiff.mp ha_fibre).2
    have hcenterD : center a ∈ D := hcenter a haH
    have hselS : sel (center a) ∈ S :=
      (hρ.1 (center a) hcenterD).1
    have ha_eq : center a + (sel (center a) + t) = a := by
      dsimp [label] at hlabel
      rw [← hlabel]
      abel
    rw [Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨⟨haA, ?_⟩, ha_not⟩
    rw [Finset.mem_add]
    refine ⟨center a, hcenterD, sel (center a) + t, ?_, ha_eq⟩
    rw [Finset.mem_add]
    exact ⟨sel (center a), hselS, t, by simp, rfl⟩
  refine ⟨t, ht_ne, hsize, ?_⟩
  change (D.card : ℝ) / (49 * K) < (newPoints.card : ℝ)
  exact hpopular.trans_le (by
    exact_mod_cast Finset.card_le_card hpopular_sub)

/-- Final one-bit branch alternative after composing the object-level
classification with the two bank statements.

The hypotheses `houtwardBank` and `hinwardBank` are precisely the conclusions
of the staged outward and inward object theorems above. Keeping this final
composition separate prevents the local inward wall from being hidden inside
the headline dichotomy.

Charter: `candidates/bedert-omega/object-layer-charter.md:42-45`.
Source: Bedert's outward branch is `main.tex:696-713`; the repaired inward
branch is grounded in `main.tex:716-724` and stated in
`note-v3-draft.md` Proposition 3.1.
Downstream: this is the O5 step alternative from which O6 constructs
`sqrt_improvement.htelescope` and `one_bit_growth.hstep`. -/
theorem one_bit_branch_dichotomy_from_objects_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G)) {K : ℝ}
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
    (∃ t : G,
        t ≠ 0 ∧
          (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
            (D.card : ℝ) / (36 * K) ≤
              ((((A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)).card :
                ℕ) : ℝ)) ∨
      ∃ t : G,
        t ≠ 0 ∧
          (S + ({0, t} : Finset G)).card ≤ 2 * S.card ∧
            (D.card : ℝ) / (49 * K) <
              ((((A ∩ (D + (S + ({0, t} : Finset G)))) \ (D + S)).card :
                ℕ) : ℝ) := by
  classical
  by_cases hout :
      ∃ a ∈ starFibres A D S G2 ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card
  · obtain ⟨a, ha, ha_outward⟩ := hout
    exact Or.inl (houtwardBank a ha ha_outward)
  · right
    apply hinwardBank
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
