/-
# Object layer, O7b: second removal and oriented repair choice

PROPOSED 2026-07-24 by the Codex proposal arm.
FROZEN 2026-07-24 by the Claude freeze arm: claim-type checklist (counting
lemma) run line by line; verification-battery freeze gate applied per
statement; back-translation trial (process-lab #45) run on all five
signatures and both definitions with no statement/docstring mismatch; all
five ambiguity flags below adjudicated ACCEPTED as encoded. Vacuity audit:
`IsUSF` is load-bearing in both statements that carry it (without it the
existential conclusions are unprovable; see the freeze notes on those
docstrings). All theorem statements and both definitions are byte-unchanged
from the proposal. Statements are now trust boundaries: fills may not alter
them; print BLOCKED instead.

Authority: `candidates/bedert-omega/o7-charter-proposal.md`, Sections 1 and 4,
approved with Option B in `attack-log.md` at approximately 21:15Z. This file
contains the two proposed trust-boundary definitions and the five O7b theorem
signatures. Every theorem body is `sorry`.

Source attribution is deliberately three-way:

* Bedert's printed second removal, good-pair uniqueness, and repair choice are
  `sources/bedert/src/main.tex:541-644`.
* The campaign's sharpened arm starts from the resulting good-pair and repair
  system in `note-core/prose-proof-arm1.md` (A1.5)-(A1.8).
* The independent blind arm reconstructs the same good-pair and oriented
  repair objects in `note-core/prose-proof-arm2-blind.md` displays (2)-(3)
  and their supporting displays. Those displays are explicitly marked
  reconstructed in that file.

The two downstream outputs use O4's declarations literally:
`HasSecondRemovalBound D S G2` and
`IsOrientedRepresentationChoice A D S G2 sel ρ`.

## AMBIGUITY FLAGS

1. The alternative side of `badTwo` is encoded by ordered witnesses
   `e,e',s,s'`, but its canonical comparison is the unordered finset
   `{e,e'}`. The case `e = e'` therefore becomes a singleton and is
   automatically different from the two-element canonical pair. Treating the
   alternative as a multiset would change the source definition.
2. The raw noncanonical repair is formulated using explicit canonical
   endpoints `u,v` and excludes both canonical orders. An equality between
   unordered endpoint finsets or an image-finset formulation would be a
   different API, especially in repeated-endpoint cases.
3. The global repair selection returns O4's total
   `RepresentationChoice G = Finset G → G × G`. Only values on `goodTwo`
   are constrained; values off that set are junk. A subtype-indexed choice
   function would not meet O4's frozen target type.
4. Classical choice enters only in the fills: witness selection for the
   source's arbitrary bad-pair witnesses, and global selection plus
   orientation of one repair for every good pair. No new axiom or opaque
   choice constant is proposed.
5. `badTwo_card_le_proposed` assumes only the selector membership needed by
   the printed counting proof. The good-pair uniqueness and orientation
   statements separately expose the stronger source-fibre membership and
   simultaneous-uniqueness facts. Bundling those into a new predicate would
   add a trust boundary not named by the charter.
-/
import BedertLab.ObjectLayer.O4Star

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Bedert's second bad set inside the two-element subsets of `goodOne`.

Bedert printed step: `main.tex:546-551` defines the alternative
`D + S` representation and compares the unordered `D`-endpoint pair with the
canonical pair.
Campaign sharpened arm: (A1.5)-(A1.6) removes exactly this family before the
incidence argument.
Blind arm: reconstructed display (2) starts after the same `B^(2)` removal.

Repeated alternative endpoints are represented by the singleton `{e,e}`;
they are not silently promoted to a two-element multiset. -/
def badTwo (D S : Finset G) (sel : G → G) :
    Finset (Finset G) :=
  ((goodOne D S).powersetCard 2).filter fun P =>
    ∃ e ∈ D, ∃ e' ∈ D, ∃ s ∈ S, ∃ s' ∈ S,
      pairTarget sel P = (e + s) + (e' + s') ∧
        ({e, e'} : Finset G) ≠ P

/-- Bedert's good-pair system `G^(2)`, the complement of `badTwo`.

Bedert printed step: `main.tex:552-555`.
Campaign sharpened arm: this is the `G^(2)` in (A1.6)-(A1.8).
Blind arm: this is the family `mathcal G` in reconstructed display (2). -/
def goodTwo (D S : Finset G) (sel : G → G) :
    Finset (Finset G) :=
  (goodOne D S).powersetCard 2 \ badTwo D S sel

/-- The printed second-removal cardinality ceiling with the certified
Two Families constant `63`.

Bedert printed step: `main.tex:599-621`, display `smallbaad`,
`|B^(2)| ≤ C₁|S|^4 + |D||S|^4`.
Campaign sharpened arm: (A1.6) specializes `C₁ = 63`.
Blind arm: its good-pair mass reconstruction follows the same two removals,
but does not independently sharpen this source ceiling. -/
theorem badTwo_card_le_proposed
    (D S : Finset G) (sel : G → G)
    (hD : DissociatedF D)
    (hsel : ∀ d ∈ D, sel d ∈ S) :
    (badTwo D S sel).card ≤
      63 * S.card ^ 4 + D.card * S.card ^ 4 := by
  classical
  have hexists :
      ∀ P : Finset G, ∃ u v e e' s s' : G,
        P ∈ badTwo D S sel →
          u ≠ v ∧
            P = {u, v} ∧
              u ∈ goodOne D S ∧
                v ∈ goodOne D S ∧
                  e ∈ D ∧
                    e' ∈ D ∧
                      s ∈ S ∧
                        s' ∈ S ∧
                          pairTarget sel P = (e + s) + (e' + s') ∧
                            ({e, e'} : Finset G) ≠ P := by
    intro P
    by_cases hP : P ∈ badTwo D S sel
    · have hPdata := Finset.mem_filter.mp hP
      have hPpow := Finset.mem_powersetCard.mp hPdata.1
      obtain ⟨u, v, huv, hPuv⟩ := Finset.card_eq_two.mp hPpow.2
      obtain ⟨e, heD, e', he'D, s, hsS, s', hs'S, heq, hne⟩ :=
        hPdata.2
      refine ⟨u, v, e, e', s, s', fun _ =>
        ⟨huv, hPuv, ?_, ?_, heD, he'D, hsS, hs'S, heq, hne⟩⟩
      · exact hPpow.1 (by simp [hPuv])
      · exact hPpow.1 (by simp [hPuv])
    · exact ⟨0, 0, 0, 0, 0, 0, fun h => (hP h).elim⟩
  choose u v e e' s s' hdata using hexists
  let key : Finset G → (G × G) × (G × G) :=
    fun P => ((sel (u P), sel (v P)), (s P, s' P))
  let keys : Finset ((G × G) × (G × G)) :=
    (S.product S).product (S.product S)
  have hkey_mem :
      ∀ P ∈ badTwo D S sel, key P ∈ keys := by
    intro P hP
    obtain ⟨_, _, huGood, hvGood, _, _, hsS, hs'S, _, _⟩ :=
      hdata P hP
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
          ⟨hsel (u P) (Finset.mem_sdiff.mp huGood).1,
            hsel (v P) (Finset.mem_sdiff.mp hvGood).1⟩,
        Finset.mem_product.mpr ⟨hsS, hs'S⟩⟩
  have hcanonical_sum :
      ∀ P ∈ badTwo D S sel,
        ∑ x ∈ P, x = u P + v P := by
    intro P hP
    obtain ⟨huv, hPuv, _, _, _, _, _, _, _, _⟩ := hdata P hP
    calc
      ∑ x ∈ P, x =
          ∑ x ∈ ({u P, v P} : Finset G), x :=
        congrArg (fun R : Finset G => ∑ x ∈ R, x) hPuv
      _ = u P + v P := Finset.sum_pair huv
  have hcanonical_target :
      ∀ P ∈ badTwo D S sel,
        pairTarget sel P =
          (u P + sel (u P)) + (v P + sel (v P)) := by
    intro P hP
    obtain ⟨huv, hPuv, _, _, _, _, _, _, _, _⟩ := hdata P hP
    calc
      pairTarget sel P =
          ∑ x ∈ ({u P, v P} : Finset G), (x + sel x) :=
        congrArg
          (fun R : Finset G => ∑ x ∈ R, (x + sel x)) hPuv
      _ = (u P + sel (u P)) + (v P + sel (v P)) :=
        Finset.sum_pair huv
  have hordered_balance :
      ∀ P ∈ badTwo D S sel,
        u P + v P - e P - e' P =
          s P + s' P - sel (u P) - sel (v P) := by
    intro P hP
    obtain ⟨huv, hPuv, _, _, _, _, _, _, heq, _⟩ := hdata P hP
    have heq' :
        (u P + sel (u P)) + (v P + sel (v P)) =
          (e P + s P) + (e' P + s' P) := by
      rw [← hcanonical_target P hP]
      exact heq
    calc
      u P + v P - e P - e' P =
          ((u P + sel (u P)) + (v P + sel (v P))) -
              ((e P + s P) + (e' P + s' P)) +
            (s P + s' P - sel (u P) - sel (v P)) := by
              abel
      _ = s P + s' P - sel (u P) - sel (v P) := by
        rw [heq']
        simp
  have hfinset_balance :
      ∀ P ∈ badTwo D S sel, e P ≠ e' P →
        (∑ x ∈ P, x) - ∑ x ∈ ({e P, e' P} : Finset G), x =
          s P + s' P - sel (u P) - sel (v P) := by
    intro P hP heNe
    calc
      (∑ x ∈ P, x) - ∑ x ∈ ({e P, e' P} : Finset G), x =
          u P + v P - (e P + e' P) := by
            rw [hcanonical_sum P hP, Finset.sum_pair heNe]
      _ = u P + v P - e P - e' P := by abel
      _ = s P + s' P - sel (u P) - sel (v P) :=
        hordered_balance P hP
  have hkey_offset :
      ∀ {P Q : Finset G}, key P = key Q →
        s P + s' P - sel (u P) - sel (v P) =
          s Q + s' Q - sel (u Q) - sel (v Q) := by
    intro P Q hPQ
    exact congrArg
      (fun k : (G × G) × (G × G) =>
        k.2.1 + k.2.2 - k.1.1 - k.1.2) hPQ
  let fibre : (G × G) × (G × G) → Finset (Finset G) :=
    fun k => (badTwo D S sel).filter fun P => key P = k
  have hfibre_bound :
      ∀ k ∈ keys, (fibre k).card ≤ 63 + D.card := by
    intro k hk
    let repeated := (fibre k).filter fun P => e P = e' P
    let distinct := (fibre k).filter fun P => e P ≠ e' P
    have hrepeated_bound : repeated.card ≤ D.card := by
      apply Finset.card_le_card_of_injOn e
      · intro P hP
        have hPfibre := (Finset.mem_filter.mp hP).1
        have hPbad := (Finset.mem_filter.mp hPfibre).1
        exact (hdata P hPbad).2.2.2.2.1
      · intro P hP Q hQ hePQ
        have hPfibre := (Finset.mem_filter.mp hP).1
        have hQfibre := (Finset.mem_filter.mp hQ).1
        have hPbad := (Finset.mem_filter.mp hPfibre).1
        have hQbad := (Finset.mem_filter.mp hQfibre).1
        have hPrepeated := (Finset.mem_filter.mp hP).2
        have hQrepeated := (Finset.mem_filter.mp hQ).2
        have hPkey := (Finset.mem_filter.mp hPfibre).2
        have hQkey := (Finset.mem_filter.mp hQfibre).2
        have hoffset :=
          hkey_offset (hPkey.trans hQkey.symm)
        have hbalance :=
          (hordered_balance P hPbad).trans
            (hoffset.trans (hordered_balance Q hQbad).symm)
        have hsum_uv : u P + v P = u Q + v Q := by
          calc
            u P + v P =
                (u P + v P - e P - e' P) + e P + e' P := by
                  abel
            _ = (u Q + v Q - e Q - e' Q) + e P + e' P := by
              rw [hbalance]
            _ = u Q + v Q := by
              rw [← hPrepeated, ← hQrepeated, hePQ]
              abel
        obtain ⟨huvP, hPuv, huGoodP, hvGoodP, _, _, _, _, _, _⟩ :=
          hdata P hPbad
        obtain ⟨huvQ, hQuv, huGoodQ, hvGoodQ, _, _, _, _, _, _⟩ :=
          hdata Q hQbad
        have hPpower : P ∈ D.powerset := by
          rw [Finset.mem_powerset]
          intro x hx
          rw [hPuv] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (Finset.mem_sdiff.mp huGoodP).1
          · exact (Finset.mem_sdiff.mp hvGoodP).1
        have hQpower : Q ∈ D.powerset := by
          rw [Finset.mem_powerset]
          intro x hx
          rw [hQuv] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (Finset.mem_sdiff.mp huGoodQ).1
          · exact (Finset.mem_sdiff.mp hvGoodQ).1
        apply hD P hPpower Q hQpower
        calc
          ∑ x ∈ P, x = u P + v P := hcanonical_sum P hPbad
          _ = u Q + v Q := hsum_uv
          _ = ∑ x ∈ Q, x := (hcanonical_sum Q hQbad).symm
    have hdisjoint :
        ∀ P ∈ distinct,
          Disjoint P ({e P, e' P} : Finset G) := by
      intro P hP
      have hPfibre := (Finset.mem_filter.mp hP).1
      have hPbad := (Finset.mem_filter.mp hPfibre).1
      have heNe := (Finset.mem_filter.mp hP).2
      obtain
        ⟨huv, hPuv, huGood, hvGood, heD, he'D, hsS, hs'S, _, hne⟩ :=
          hdata P hPbad
      rw [Finset.disjoint_left]
      intro x hxP hxQ
      have hPcard : P.card = 2 :=
        (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp hPbad).1).2
      have hPerase_card : (P.erase x).card = 1 := by
        rw [Finset.card_erase_of_mem hxP, hPcard]
      obtain ⟨a, hPerase⟩ := Finset.card_eq_one.mp hPerase_card
      have haErase : a ∈ P.erase x := by simp [hPerase]
      have hax : a ≠ x := (Finset.mem_erase.mp haErase).1
      have hPxa : P = {x, a} := by
        rw [← Finset.insert_erase hxP, hPerase]
      let Q : Finset G := {e P, e' P}
      have hQcard : Q.card = 2 := by simp [Q, heNe]
      have hxQ' : x ∈ Q := hxQ
      have hQerase_card : (Q.erase x).card = 1 := by
        rw [Finset.card_erase_of_mem hxQ', hQcard]
      obtain ⟨b, hQerase⟩ := Finset.card_eq_one.mp hQerase_card
      have hbErase : b ∈ Q.erase x := by simp [hQerase]
      have hbx : b ≠ x := (Finset.mem_erase.mp hbErase).1
      have hQxb : Q = {x, b} := by
        rw [← Finset.insert_erase hxQ', hQerase]
      have hsumP : u P + v P = x + a := by
        calc
          u P + v P = ∑ z ∈ P, z :=
            (hcanonical_sum P hPbad).symm
          _ = ∑ z ∈ ({x, a} : Finset G), z :=
            congrArg (fun R : Finset G => ∑ z ∈ R, z) hPxa
          _ = x + a := Finset.sum_pair hax.symm
      have hsumQ : e P + e' P = x + b := by
        calc
          e P + e' P =
              ∑ z ∈ ({e P, e' P} : Finset G), z :=
            by
              symm
              exact Finset.sum_pair heNe
          _ = ∑ z ∈ ({x, b} : Finset G), z :=
            congrArg (fun R : Finset G => ∑ z ∈ R, z) hQxb
          _ = x + b := Finset.sum_pair hbx.symm
      have hbalance' :
          x + a - x - b =
            s P + s' P - sel (u P) - sel (v P) := by
        calc
          x + a - x - b =
              (u P + v P) - (e P + e' P) := by
                rw [hsumP, hsumQ]
                abel
          _ = u P + v P - e P - e' P := by abel
          _ = s P + s' P - sel (u P) - sel (v P) :=
            hordered_balance P hPbad
      let w := sel (u P) + sel (v P) - s P - s' P
      have hawb : a + w = b := by
        dsimp [w]
        calc
          a + (sel (u P) + sel (v P) - s P - s' P) =
              a - (s P + s' P - sel (u P) - sel (v P)) := by
                abel
          _ = b := by rw [← hbalance']; abel
      have hseluS : sel (u P) ∈ S :=
        hsel (u P) (Finset.mem_sdiff.mp huGood).1
      have hselvS : sel (v P) ∈ S :=
        hsel (v P) (Finset.mem_sdiff.mp hvGood).1
      have hwTwo : w ∈ twoSsub S := by
        unfold twoSsub
        rw [Finset.mem_sub]
        refine ⟨sel (u P) + sel (v P) - s P, ?_, s' P, hs'S, rfl⟩
        rw [Finset.mem_sub]
        exact ⟨sel (u P) + sel (v P),
          Finset.mem_add.mpr ⟨sel (u P), hseluS, sel (v P), hselvS, rfl⟩,
          s P, hsS, rfl⟩
      have hwNe : w ≠ 0 := by
        intro hw
        have hab : a = b := by simpa [hw] using hawb
        apply hne
        calc
          ({e P, e' P} : Finset G) = {x, b} := hQxb
          _ = {x, a} := by rw [hab]
          _ = P := hPxa.symm
      have haGood : a ∈ goodOne D S := by
        have hPsub : P ⊆ goodOne D S := by
          intro z hz
          rw [hPuv] at hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact huGood
          · exact hvGood
        exact hPsub (by simp [hPxa])
      have hbD : b ∈ D := by
        have hQsub : Q ⊆ D := by
          intro z hz
          simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact heD
          · exact he'D
        exact hQsub (by simp [hQxb])
      exact (Finset.mem_sdiff.mp haGood).2
        (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp haGood).1, w,
            Finset.mem_sdiff.mpr ⟨hwTwo, by simpa using hwNe⟩,
            by simpa [hawb] using hbD⟩)
    have hdistinct_bound : distinct.card ≤ 63 := by
      let equiv : Fin distinct.card ≃ distinct := distinct.equivFin.symm
      let P : Fin distinct.card → Finset G := fun i => equiv i
      let Q : Fin distinct.card → Finset G :=
        fun i => {e (P i), e' (P i)}
      have hPJ (i : Fin distinct.card) : P i ∈ distinct := by
        change (equiv i : Finset G) ∈ distinct
        exact (equiv i).property
      have hPbad (i : Fin distinct.card) : P i ∈ badTwo D S sel := by
        exact (Finset.mem_filter.mp
          (Finset.mem_filter.mp (hPJ i)).1).1
      have hPcard (i : Fin distinct.card) : (P i).card = 2 := by
        exact (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp (hPbad i)).1).2
      have hQcard (i : Fin distinct.card) : (Q i).card = 2 := by
        have heNe := (Finset.mem_filter.mp (hPJ i)).2
        exact Finset.card_pair heNe
      have hPsubD (i : Fin distinct.card) : P i ⊆ D := by
        obtain ⟨_, hPuv, huGood, hvGood, _, _, _, _, _, _⟩ :=
          hdata (P i) (hPbad i)
        intro z hz
        rw [hPuv] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (Finset.mem_sdiff.mp huGood).1
        · exact (Finset.mem_sdiff.mp hvGood).1
      have hQsubD (i : Fin distinct.card) : Q i ⊆ D := by
        obtain ⟨_, _, _, _, heD, he'D, _, _, _, _⟩ :=
          hdata (P i) (hPbad i)
        intro z hz
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact heD
        · exact he'D
      apply two_families_pairs P Q
      · intro i
        exact (hPcard i).le
      · intro i
        exact (hQcard i).le
      · intro i
        exact hdisjoint (P i) (hPJ i)
      · intro i j hij
        by_contra hcross
        simp only [not_or, not_not] at hcross
        have hkey_i :
            key (P i) = k :=
          (Finset.mem_filter.mp
            (Finset.mem_filter.mp (hPJ i)).1).2
        have hkey_j :
            key (P j) = k :=
          (Finset.mem_filter.mp
            (Finset.mem_filter.mp (hPJ j)).1).2
        have hoffset := hkey_offset (hkey_i.trans hkey_j.symm)
        have hbalance :
            (∑ x ∈ P i, x) - ∑ x ∈ Q i, x =
              (∑ x ∈ P j, x) - ∑ x ∈ Q j, x :=
          (hfinset_balance (P i) (hPbad i)
              (Finset.mem_filter.mp (hPJ i)).2).trans
            (hoffset.trans
              (hfinset_balance (P j) (hPbad j)
                (Finset.mem_filter.mp (hPJ j)).2).symm)
        have hsum :
            ∑ x ∈ P i ∪ Q j, x =
              ∑ x ∈ Q i ∪ P j, x := by
          rw [Finset.sum_union hcross.1,
            Finset.sum_union hcross.2.symm]
          calc
            (∑ x ∈ P i, x) + ∑ x ∈ Q j, x =
                ((∑ x ∈ P i, x) - ∑ x ∈ Q i, x) +
                  ((∑ x ∈ Q i, x) + ∑ x ∈ Q j, x) := by
                    abel
            _ = ((∑ x ∈ P j, x) - ∑ x ∈ Q j, x) +
                  ((∑ x ∈ Q i, x) + ∑ x ∈ Q j, x) := by
                    rw [hbalance]
            _ = (∑ x ∈ Q i, x) + ∑ x ∈ P j, x := by
              abel
        have hunion :
            P i ∪ Q j = Q i ∪ P j := by
          apply hD
          · rw [Finset.mem_powerset]
            exact Finset.union_subset (hPsubD i) (hQsubD j)
          · rw [Finset.mem_powerset]
            exact Finset.union_subset (hQsubD i) (hPsubD j)
          · exact hsum
        have hPne : P i ≠ P j := by
          intro h
          apply hij
          apply equiv.injective
          exact Subtype.ext h
        have hnotSubset : ¬ P i ⊆ P j := by
          intro hsub
          apply hPne
          exact Finset.eq_of_subset_of_card_le hsub (by
            rw [hPcard i, hPcard j])
        obtain ⟨x, hxi, hxj⟩ := Finset.not_subset.mp hnotSubset
        have hxunion : x ∈ Q i ∪ P j := by
          rw [← hunion]
          exact Finset.mem_union_left _ hxi
        rcases Finset.mem_union.mp hxunion with hxQi | hxPj
        · exact (Finset.disjoint_left.mp (hdisjoint (P i) (hPJ i)))
            hxi hxQi
        · exact hxj hxPj
    have hsplit :
        repeated.card + distinct.card = (fibre k).card := by
      simpa [repeated, distinct] using
        Finset.card_filter_add_card_filter_not
          (s := fibre k) (p := fun P => e P = e' P)
    omega
  have hbad_subset :
      badTwo D S sel ⊆ keys.biUnion fibre := by
    intro P hP
    exact Finset.mem_biUnion.mpr
      ⟨key P, hkey_mem P hP,
        Finset.mem_filter.mpr ⟨hP, rfl⟩⟩
  calc
    (badTwo D S sel).card ≤ (keys.biUnion fibre).card :=
      Finset.card_le_card hbad_subset
    _ ≤ keys.card * (63 + D.card) := by
      apply Finset.card_biUnion_le_card_mul
      exact hfibre_bound
    _ = 63 * S.card ^ 4 + D.card * S.card ^ 4 := by
      simp [keys]
      ring

/-- Package the concrete `goodTwo` system in O4's exact second-removal type.

Bedert printed step: the complement definition at `main.tex:552-555`
together with `smallbaad` at `main.tex:599-621`.
Campaign sharpened arm: this is the second-removal seam underlying (A1.6).
Blind arm: reconstructed display (2) uses the resulting good-pair family.

The conclusion is deliberately the existing O4 declaration, without a
parallel reformulation. -/
theorem goodTwo_hasSecondRemovalBound_proposed
    (D S : Finset G) (sel : G → G)
    (hD : DissociatedF D)
    (hsel : ∀ d ∈ D, sel d ∈ S) :
    HasSecondRemovalBound D S (goodTwo D S sel) := by
  constructor
  · exact Finset.sdiff_subset
  · have hsubset :
        ((goodOne D S).powersetCard 2 \ goodTwo D S sel) ⊆
          badTwo D S sel := by
      intro P hP
      have hPdata := Finset.mem_sdiff.mp hP
      by_contra hPbad
      exact hPdata.2
        (Finset.mem_sdiff.mpr ⟨hPdata.1, hPbad⟩)
    exact (Finset.card_le_card hsubset).trans
      (badTwo_card_le_proposed D S sel hD hsel)

/-- A good pair has only its two ordered canonical representations inside
`A ∩ (D + S)`.

Bedert printed step: Lemma `goodlemma`, `main.tex:557-572`.
Campaign sharpened arm: canonical endpoints remain explicit in
(A1.6)-(A1.7).
Blind arm: the oriented repair supporting reconstructed display (2) relies on
the same good-pair uniqueness.

The source-fibre uniqueness premise is the direct output shape of O7a's
`source_selector_from_simultaneous_proposed`.

Freeze note: `hsel` is not load-bearing in the source derivation. The
goodlemma proof (`main.tex:557-572`) uses only the fibre memberships of the
decomposition witnesses of `x` and `y` plus the `hsim` uniqueness; the
selector's own fibre membership never enters. It is kept, per the O5/O6
freeze precedent on non-load-bearing hypotheses, as interface documentation:
both conjuncts arrive together from O7a's packaged output. -/
theorem good_pair_unique_inside_proposed
    (A D S : Finset G) (sel : G → G)
    (hsel : ∀ d ∈ D, sel d ∈ S ∧ d + sel d ∈ A)
    (hsim :
      ∀ d ∈ D, ∀ d' ∈ D,
        ∀ x ∈ S, d + x ∈ A →
          ∀ y ∈ S, d' + y ∈ A →
            x + y = sel d + sel d' →
              x = sel d ∧ y = sel d') :
    ∀ P ∈ goodTwo D S sel,
      ∀ x ∈ A ∩ (D + S), ∀ y ∈ A ∩ (D + S),
        x + y = pairTarget sel P →
          ∃ u v : G,
            u ≠ v ∧
              P = {u, v} ∧
                ((x = u + sel u ∧ y = v + sel v) ∨
                  (x = v + sel v ∧ y = u + sel u)) := by
  classical
  intro P hP x hx y hy hxy
  have hPdata := Finset.mem_sdiff.mp hP
  have hPpow := Finset.mem_powersetCard.mp hPdata.1
  obtain ⟨u, v, huv, hPuv⟩ := Finset.card_eq_two.mp hPpow.2
  have huGood : u ∈ goodOne D S := hPpow.1 (by simp [hPuv])
  have hvGood : v ∈ goodOne D S := hPpow.1 (by simp [hPuv])
  have huD : u ∈ D := (Finset.mem_sdiff.mp huGood).1
  have hvD : v ∈ D := (Finset.mem_sdiff.mp hvGood).1
  have hxdata := Finset.mem_inter.mp hx
  have hydata := Finset.mem_inter.mp hy
  obtain ⟨e, heD, s, hsS, hesx⟩ := Finset.mem_add.mp hxdata.2
  obtain ⟨e', he'D, s', hs'S, heysy⟩ := Finset.mem_add.mp hydata.2
  have hEP : ({e, e'} : Finset G) = P := by
    by_contra hne
    apply hPdata.2
    rw [badTwo, Finset.mem_filter]
    refine ⟨hPdata.1, e, heD, e', he'D, s, hsS, s', hs'S, ?_, hne⟩
    calc
      pairTarget sel P = x + y := hxy.symm
      _ = (e + s) + (e' + s') := by rw [hesx, heysy]
  have hEPuv : ({e, e'} : Finset G) = {u, v} := hEP.trans hPuv
  have hset :
      ({e, e'} : Set G) = {u, v} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun R : Finset G => (↑R : Set G)) hEPuv
  have horient :
      (e = u ∧ e' = v) ∨ (e = v ∧ e' = u) :=
    Set.pair_eq_pair_iff.mp hset
  have heNe : e ≠ e' := by
    rcases horient with h | h
    · simpa [h.1, h.2] using huv
    · simpa [h.1, h.2] using huv.symm
  have htarget :
      pairTarget sel P =
        (e + sel e) + (e' + sel e') := by
    calc
      pairTarget sel P =
          ∑ z ∈ ({e, e'} : Finset G), (z + sel z) :=
        congrArg
          (fun R : Finset G => ∑ z ∈ R, (z + sel z)) hEP.symm
      _ = (e + sel e) + (e' + sel e') := Finset.sum_pair heNe
  have htotal :
      (e + s) + (e' + s') = pairTarget sel P := by
    rw [hesx, heysy]
    exact hxy
  have hshift : s + s' = sel e + sel e' := by
    calc
      s + s' =
          ((e + s) + (e' + s')) - e - e' := by
            abel
      _ = pairTarget sel P - e - e' := by rw [htotal]
      _ = sel e + sel e' := by rw [htarget]; abel
  have hesA : e + s ∈ A := by rw [hesx]; exact hxdata.1
  have heysA : e' + s' ∈ A := by rw [heysy]; exact hydata.1
  have hselected :=
    hsim e heD e' he'D s hsS hesA s' hs'S heysA hshift
  refine ⟨u, v, huv, hPuv, ?_⟩
  rcases horient with h | h
  · left
    constructor
    · calc
        x = e + s := hesx.symm
        _ = u + sel u := by rw [hselected.1, h.1]
    · calc
        y = e' + s' := heysy.symm
        _ = v + sel v := by rw [hselected.2, h.2]
  · right
    constructor
    · calc
        x = e + s := hesx.symm
        _ = v + sel v := by rw [hselected.1, h.1]
    · calc
        y = e' + s' := heysy.symm
        _ = u + sel u := by rw [hselected.2, h.2]

/-- `IsUSF A` supplies a noncanonical ordered repair of a good pair.

Bedert printed step: `main.tex:635-644` chooses a second representation in
`A^2` because the canonical sum is not unique.
Campaign sharpened arm: (A1.7) records the noncanonical equation before
orientation.
Blind arm: the supporting display after reconstructed display (2) records the
same nontrivial representation.

Noncanonical means that, for the two endpoints of `P`, neither canonical
ordering equals `(x,y)`.

Freeze note (vacuity audit): `hUSF` is load-bearing, and `hsel`'s `∈ A`
component with it. The intended fill instantiates `¬ HasUniqueSum A
(pairTarget sel P)` at the canonical representation, whose membership in
`A` comes from `hsel`; without `IsUSF A` the canonical sum may be unique
and the existential conclusion is unprovable. The exhibited decomposition
`P = {u, v}` is symmetric under swapping `u` and `v`, as is the negated
disjunction, so the existential over decompositions is equivalent to the
universal one; no junk-decomposition loophole exists. -/
theorem alternative_representation_from_isUSF_proposed
    (A D S : Finset G) (sel : G → G)
    (hUSF : IsUSF A)
    (hsel : ∀ d ∈ D, sel d ∈ S ∧ d + sel d ∈ A)
    {P : Finset G} (hP : P ∈ goodTwo D S sel) :
    ∃ x ∈ A, ∃ y ∈ A,
      x + y = pairTarget sel P ∧
        ∃ u v : G,
          u ≠ v ∧
            P = {u, v} ∧
              ¬ ((x = u + sel u ∧ y = v + sel v) ∨
                (x = v + sel v ∧ y = u + sel u)) := by
  classical
  have hPbase :
      P ∈ (goodOne D S).powersetCard 2 :=
    (Finset.mem_sdiff.mp hP).1
  have hPpow := Finset.mem_powersetCard.mp hPbase
  obtain ⟨u, v, huv, hPuv⟩ := Finset.card_eq_two.mp hPpow.2
  have huD : u ∈ D :=
    (Finset.mem_sdiff.mp (hPpow.1 (by simp [hPuv]))).1
  have hvD : v ∈ D :=
    (Finset.mem_sdiff.mp (hPpow.1 (by simp [hPuv]))).1
  have htarget :
      pairTarget sel P =
        (u + sel u) + (v + sel v) := by
    calc
      pairTarget sel P =
          ∑ z ∈ ({u, v} : Finset G), (z + sel z) :=
        congrArg
          (fun R : Finset G => ∑ z ∈ R, (z + sel z)) hPuv
      _ = (u + sel u) + (v + sel v) := Finset.sum_pair huv
  by_contra hno
  push_neg at hno
  apply hUSF (pairTarget sel P)
  refine ⟨u + sel u, (hsel u huD).2,
    v + sel v, (hsel v hvD).2, htarget.symm, ?_⟩
  intro x hx y hy hxy
  exact hno x hx y hy hxy u v huv hPuv

/-- Choose and orient all repairs so their first endpoints lie outside
`D + S`, returning O4's exact representation-choice predicate.

Bedert printed step: `main.tex:635-643` orients one noncanonical repair per
good pair with its first endpoint in `A \ (D + S)`.
Campaign sharpened arm: (A1.7)-(A1.8) uses this oriented total repair system
to define the fibres `N(a)`.
Blind arm: the supporting display after reconstructed display (2) independently
uses the same orientation.

This is the O4-ready seam and the one-step chain's global consumption point
for `IsUSF`. Classical choice belongs to the eventual proof body, not the
statement.

Freeze note (vacuity audit): `hUSF` is load-bearing. The canonical
representation of a good pair has both endpoints in `A ∩ (D + S)`, so the
required `chosenX ρ P ∈ A \ (D + S)` can never be met canonically; only
the `IsUSF` repair, oriented via good-pair uniqueness, supplies it. If
`goodTwo` is empty the second component is vacuous, matching charter
Section 9: nonemptiness is derived downstream from the cap, never assumed
here. -/
theorem exists_oriented_representation_choice_from_isUSF_proposed
    (A D S : Finset G) (sel : G → G)
    (hUSF : IsUSF A)
    (hsel : ∀ d ∈ D, sel d ∈ S ∧ d + sel d ∈ A)
    (hsim :
      ∀ d ∈ D, ∀ d' ∈ D,
        ∀ x ∈ S, d + x ∈ A →
          ∀ y ∈ S, d' + y ∈ A →
            x + y = sel d + sel d' →
              x = sel d ∧ y = sel d') :
    ∃ ρ : RepresentationChoice G,
      IsOrientedRepresentationChoice
        A D S (goodTwo D S sel) sel ρ := by
  classical
  have hrepair :
      ∀ P : Finset G, ∃ z : G × G,
        P ∈ goodTwo D S sel →
          z.1 ∈ A \ (D + S) ∧
            z.2 ∈ A ∧
              z.1 + z.2 = pairTarget sel P := by
    intro P
    by_cases hP : P ∈ goodTwo D S sel
    · obtain
        ⟨x, hxA, y, hyA, hxy, u, v, huv, hPuv, hnoncanonical⟩ :=
          alternative_representation_from_isUSF_proposed
            A D S sel hUSF hsel hP
      have hnotBoth : ¬ (x ∈ D + S ∧ y ∈ D + S) := by
        rintro ⟨hxDS, hyDS⟩
        obtain ⟨a, b, hab, hPab, hcanonical⟩ :=
          good_pair_unique_inside_proposed A D S sel hsel hsim
            P hP x (Finset.mem_inter.mpr ⟨hxA, hxDS⟩)
            y (Finset.mem_inter.mpr ⟨hyA, hyDS⟩) hxy
        have hpairs : ({a, b} : Finset G) = {u, v} :=
          hPab.symm.trans hPuv
        have hsets : ({a, b} : Set G) = {u, v} := by
          simpa only [Finset.coe_insert, Finset.coe_singleton] using
            congrArg (fun R : Finset G => (↑R : Set G)) hpairs
        have horient :
            (a = u ∧ b = v) ∨ (a = v ∧ b = u) :=
          Set.pair_eq_pair_iff.mp hsets
        apply hnoncanonical
        rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcanonical
        · exact hcanonical.elim Or.inr Or.inl
      by_cases hxDS : x ∈ D + S
      · have hyDS : y ∉ D + S := by
          intro hy
          exact hnotBoth ⟨hxDS, hy⟩
        exact ⟨(y, x), fun _ =>
          ⟨Finset.mem_sdiff.mpr ⟨hyA, hyDS⟩, hxA,
            by rw [add_comm]; exact hxy⟩⟩
      · exact ⟨(x, y), fun _ =>
          ⟨Finset.mem_sdiff.mpr ⟨hxA, hxDS⟩, hyA, hxy⟩⟩
    · exact ⟨(0, 0), fun h => (hP h).elim⟩
  choose repair hrepair using hrepair
  let ρ : RepresentationChoice G := fun P => repair P
  refine ⟨ρ, hsel, ?_⟩
  intro P hP
  have hPbase :
      P ∈ (goodOne D S).powersetCard 2 :=
    (Finset.mem_sdiff.mp hP).1
  have hPpow := Finset.mem_powersetCard.mp hPbase
  have hPD : P ⊆ D := by
    intro u hu
    exact (Finset.mem_sdiff.mp (hPpow.1 hu)).1
  have hrepairP := hrepair P hP
  refine ⟨Finset.mem_powersetCard.mpr ⟨hPD, hPpow.2⟩, ?_⟩
  simpa [ρ, chosenX, chosenY] using hrepairP

end ObjectLayer
end BedertLab
