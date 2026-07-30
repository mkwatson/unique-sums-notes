/-
# Object layer, O5W: fixed-discrepancy multiplicity wall

FROZEN 2026-07-24 by the Claude freeze arm — fill sorries only; BLOCKED if
unprovable as written. Statements changed at freeze: NONE (all three theorem
statements are byte-identical to the Sol proposal; only this status header
was updated).

## Freeze record (2026-07-24, Claude freeze arm)

Checklist run (reference/claim-checklists.md, counting-lemma items;
verification-battery freeze-gate addendum):

* Quantifier audit: theorem 1's `∃ base shift` precedes the `∀ a`; this is
  sound because `retained a ⊆ fibreN G2 ρ a` and `fibreN` filters on
  `chosenX ρ P = a`, so the fibres are pairwise disjoint and each spoke `P`
  is constrained by at most one `a`; the `base P ∈ D ∧ shift P ∈ S ∧
  chosenY ρ P = base P + shift P` conjuncts are `a`-independent. Theorem 2
  is a per-fibre bound (one fixed `δ`), matching arcB-s3 Lemma 1.1; the
  adapter's fibre sweep over `t_a + (S - S)` is where the `63 |S|²` global
  loss appears, matching display (1.8) — no per-fibre/global confusion.
* Seam audit (byte-level): the adapter's hypothesis list and conclusion are
  byte-identical to O5Banks `inward_successful_spokes_local_proposed`
  (mechanical diff: the only difference between the two declarations is the
  theorem name). `63` equals the certified `two_families_pairs` constant.
* Derivability line-check: each conclusion re-derived on paper from exactly
  the stated hypotheses (theorem 1 via `hretained` + `hρ.2`'s
  `P ∈ D.powersetCard 2` and `pairTarget` identity + classical choice on
  the `chosenY ρ P ∈ D + S` filter + `hsecond.1` for `leaf ∈ goodOne`;
  theorem 2 via `two_families_pairs` on singletons with `hcross` from
  `DissociatedF` — the equal-discrepancy rearrangement
  `leaf_i + base_j = base_i + leaf_j` with all four elements distinct is a
  two-subset sum collision; theorem 3 by fibre partition, (1.8)-(1.9), and
  `hretained.2` + `hinward` giving `q_a < 6 |inward a|`).
* Sign audit: `leaf - base` matches arcB-s3 (1.5) `δ_i = d_i - e_i` and
  main.tex:753-756 `d_i(a)-e_i(a) = t' + s_i(a) - s_{d_i(a)}` term for
  term under `leaf = d_i`, `base = e_i`, `shift = s_i`,
  `sel leaf = s_{d_i}`, `t' = a - (center a + sel (center a))`.
* Junk-value audit: no division and no ℕ subtraction in any statement
  (the only division, `fibreCount / 6`, is real and appears only inside
  the byte-frozen statement-6 conclusion shape); `base`/`shift` take
  arbitrary junk values off the constrained filter sets.
* Vacuity audit: all hypothesis sets are satisfiable (`G2 = ∅` satisfies
  every hypothesis and every conclusion nonvacuously via `I = fun _ => ∅`,
  `base = shift = fun _ => 0`; `J = ∅` gives `0 ≤ 63`); degenerate spokes
  (`leaf P = center`, forcing `P` a singleton) are consistent with every
  conjunct and break nothing.
* Non-load-bearing hypotheses noted (kept deliberately, no deletion):
  theorem 1 uses only the `.2` half of `hρ` (the equation is pure algebra
  plus `pairTarget`); `hρ` is a bundled Prop and is kept whole for
  interface consistency with O5Banks.

All eight ambiguity flags below were adjudicated at freeze and are honored
by the statements as written; none required a change. Flag 7 ruling: the
`HasSecondRemovalBound.1` projection (`G2 ⊆ (goodOne D S).powersetCard 2`,
O4Star.lean) IS the intended O5 seam; no new persistent primitive is
required; the charter re-scope trigger is NOT pulled.

Known packaging residual (not a math gap, recorded for the fill/integration
arm): this file imports O5Banks, so O5Banks statement 6's own `sorry`
cannot cite the adapter without an import cycle. The three theorems use
only O1-O4 + TwoFamilies vocabulary; at integration, re-parent this file's
import to `O4Star` (or transplant the fills) so statement 6 closes by a
one-line `exact`. That restructure is outside this freeze's permitted
edits.

Statement skeletons only. Every theorem body is `sorry`.

This file isolates the sole remaining wall in
`inward_successful_spokes_local_proposed`: choose the noncanonical
`chosenY = e + r` decomposition, bound every nonzero fixed-discrepancy
fibre by the certified Two Families constant `63`, and package the
zero-discrepancy spokes in the exact form consumed by O5Banks statement 6.

## AMBIGUITY FLAGS

1. The representation witnesses `base` and `shift` are total functions on
   `Finset G`, constrained only on inward retained spokes. A subtype-indexed
   dependent choice would be a different API.
2. The canonical leaf is fixed as `(sum P) - center a`, matching O5Banks
   statement 6. The decomposition also exposes `P = {center a, leaf}` so the
   pair-level multiplicity theorem does not silently assume leaf injectivity.
3. The discrepancy sign is `leaf - base`, matching `arcB-s3-attempt.md`
   (1.5)-(1.6). Reversing the sign gives an equivalent counting statement but
   a different adapter equation.
4. The Two Families application uses singleton families `{base P}` and
   `{leaf P}`. The certified theorem permits cardinality at most two; no
   separate singleton specialization is proposed.
5. The multiplicity theorem is stated for an arbitrary finite spoke family
   `J` carrying pair recovery data. The adapter applies it to each nonzero
   discrepancy fibre of the inward filter. Stating it directly for that
   filter would duplicate the decomposition hypotheses.
6. The adapter returns an existential `I`, byte-for-byte in the result shape
   of O5Banks statement 6. It does not expose the proposed implementation
   `I a = inward(a).filter (fun P => discrepancy P = 0)`.
7. `HasSecondRemovalBound.1` is used as the existing object-level primitive
   placing every `G2` pair in `(goodOne D S).powersetCard 2`. No new
   persistent primitive is required unless the freeze arm rejects that
   projection as the intended O5 seam.
8. The decomposition needs only the subset half of statement 6's
   `hretained`; the adapter retains the full conjunction because its
   cardinality half is exactly what converts inward dominance into
   `q_a / 6 <= |J(a)|`.
-/
import BedertLab.ObjectLayer.O4Star
import BedertLab.TwoFamilies

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Decompose every inward retained spoke into the object-level data used by
the `e = d` argument.

For `leaf = (sum P) - center a`, this chooses
`chosenY ρ P = base P + shift P` and derives
`leaf - base P = t_a + shift P - sel leaf`. It also records that the spoke is
the centre-leaf pair and that the leaf lies in `goodOne D S`.

Audit source: `arcB-s3-attempt.md` (1.3)-(1.6), the decomposition underlying
(1.8)-(1.9); Bedert author LaTeX `main.tex:716-724,748-756`.
O5Banks statement-6 hypotheses served: `hsecond` supplies good-pair
membership, `hρ` supplies the translated endpoint equation, and the subset
half of `hretained` pins the centre and fibre. -/
theorem inward_spoke_discrepancy_decomposition_proposed
    (A D S : Finset G) (G2 : Finset (Finset G))
    (sel center : G → G) (ρ : RepresentationChoice G)
    (retained : G → Finset (Finset G))
    (hsecond : HasSecondRemovalBound D S G2)
    (hρ : IsOrientedRepresentationChoice A D S G2 sel ρ)
    (hretained :
      ∀ a ∈ starFibres A D S G2 ρ,
        retained a ⊆
          (fibreN G2 ρ a).filter (fun P => center a ∈ P)) :
    ∃ base shift : Finset G → G,
      ∀ a ∈ starFibres A D S G2 ρ,
        ∀ P ∈
            (retained a).filter (fun P => chosenY ρ P ∈ D + S),
          base P ∈ D ∧
            shift P ∈ S ∧
              chosenY ρ P = base P + shift P ∧
                (let leaf := (∑ x ∈ P, x) - center a;
                  leaf ∈ goodOne D S ∧
                    P = {center a, leaf} ∧
                      leaf - base P =
                        (a - (center a + sel (center a))) +
                          shift P - sel leaf) := by
  classical
  have hchoice :
      ∀ P : Finset G, ∃ z : G × G,
        chosenY ρ P ∈ D + S →
          z.1 ∈ D ∧ z.2 ∈ S ∧ chosenY ρ P = z.1 + z.2 := by
    intro P
    by_cases hP : chosenY ρ P ∈ D + S
    · obtain ⟨d, hd, s, hs, hsum⟩ := Finset.mem_add.mp hP
      exact ⟨(d, s), fun _ => ⟨hd, hs, hsum.symm⟩⟩
    · exact ⟨(0, 0), fun h => False.elim (hP h)⟩
  choose w hw using hchoice
  let base : Finset G → G := fun P => (w P).1
  let shift : Finset G → G := fun P => (w P).2
  refine ⟨base, shift, ?_⟩
  intro a ha P hP
  have hPdata := Finset.mem_filter.mp hP
  have hdecomp := hw P hPdata.2
  have hPfibre := hretained a ha hPdata.1
  have hPfibre_data := Finset.mem_filter.mp hPfibre
  have hPN_data := Finset.mem_filter.mp hPfibre_data.1
  have hPG2 : P ∈ G2 := hPN_data.1
  have hchosenX : chosenX ρ P = a := hPN_data.2
  have hcenterP : center a ∈ P := hPfibre_data.2
  have hPgood := hsecond.1 hPG2
  have hPsub : P ⊆ goodOne D S :=
    (Finset.mem_powersetCard.mp hPgood).1
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hPgood).2
  have herase_card : (P.erase (center a)).card = 1 := by
    rw [Finset.card_erase_of_mem hcenterP, hPcard]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp herase_card
  have hv_erase : v ∈ P.erase (center a) := by simp [hv]
  have hv_ne : v ≠ center a := (Finset.mem_erase.mp hv_erase).1
  have hP_eq : P = {center a, v} := by
    rw [← Finset.insert_erase hcenterP, hv]
  have hv_good : v ∈ goodOne D S := hPsub (by simp [hP_eq])
  have hleaf_eq : (∑ x ∈ P, x) - center a = v := by
    rw [hP_eq]
    simp [hv_ne.symm]
  have htarget' :
      a + chosenY ρ P =
        (center a + sel (center a)) + (v + sel v) := by
    calc
      a + chosenY ρ P =
          chosenX ρ P + chosenY ρ P := by rw [hchosenX]
      _ = pairTarget sel P := (hρ.2 P hPG2).2.2.2
      _ = (center a + sel (center a)) + (v + sel v) := by
        simp [pairTarget, hP_eq, hv_ne.symm]
  refine ⟨hdecomp.1, hdecomp.2.1, hdecomp.2.2, ?_⟩
  dsimp only
  refine ⟨hleaf_eq ▸ hv_good, ?_, ?_⟩
  · rw [hleaf_eq, hP_eq]
  · rw [hleaf_eq]
    dsimp [base, shift] at hdecomp ⊢
    rw [hdecomp.2.2] at htarget'
    calc
      v - (w P).1 =
          ((center a + sel (center a)) + (v + sel v)) -
            ((center a + sel (center a)) + sel v + (w P).1) := by
              abel
      _ = (a + ((w P).1 + (w P).2)) -
            ((center a + sel (center a)) + sel v + (w P).1) := by
              rw [htarget']
      _ = (a - (center a + sel (center a))) +
            (w P).2 - sel v := by
              abel

/-- A family of centre-leaf spokes with one fixed nonzero discrepancy has
cardinality at most `63`.

The fill must invoke the certified
`BedertLab.two_families_pairs : k ≤ 63` on the singleton families
`{base P}` and `{leaf P}`. Dissociativity supplies the cross-intersection
condition after comparing two equal discrepancies; this statement must not
re-prove the pair-level Two Families theorem.

Audit source: the fixed-discrepancy lemma preceding
`arcB-s3-attempt.md` (1.8), and Bedert author LaTeX
`main.tex:753-762`.
O5Banks statement-6 hypotheses served: `hD` is the dissociativity input;
the pair recovery and membership facts are the object-level consequences of
its `hsecond`, `hρ`, and `hretained` hypotheses supplied by the decomposition
lemma above. -/
theorem fixed_discrepancy_pair_multiplicity_le_proposed
    (D : Finset G) (J : Finset (Finset G))
    (center δ : G) (base leaf : Finset G → G)
    (hD : DissociatedF D)
    (hbase : ∀ P ∈ J, base P ∈ D)
    (hleaf : ∀ P ∈ J, leaf P ∈ D)
    (hrecover : ∀ P ∈ J, P = {center, leaf P})
    (hδ : δ ≠ 0)
    (hfixed : ∀ P ∈ J, leaf P - base P = δ) :
    J.card ≤ 63 := by
  classical
  let e : Fin J.card ≃ J := J.equivFin.symm
  let P : Fin J.card → Finset G := fun i => e i
  have hPJ (i : Fin J.card) : P i ∈ J := by
    change (e i : Finset G) ∈ J
    exact (e i).property
  have hbase_leaf (i : Fin J.card) : base (P i) ≠ leaf (P i) := by
    intro heq
    apply hδ
    calc
      δ = leaf (P i) - base (P i) := (hfixed (P i) (hPJ i)).symm
      _ = 0 := by rw [heq]; simp
  apply two_families_pairs
      (fun i => {base (P i)}) (fun i => {leaf (P i)})
  · intro i
    simp
  · intro i
    simp
  · intro i
    rw [Finset.disjoint_left]
    intro x hxbase hxleaf
    simp only [Finset.mem_singleton] at hxbase hxleaf
    exact hbase_leaf i (hxbase.symm.trans hxleaf)
  · intro i j hij
    by_contra hcross
    simp only [not_or, not_not] at hcross
    have hbase_i_leaf_j : base (P i) ≠ leaf (P j) := by
      intro heq
      exact (Finset.not_disjoint_iff.mpr
        ⟨base (P i), by simp, by simp [heq]⟩) hcross.1
    have hbase_j_leaf_i : base (P j) ≠ leaf (P i) := by
      intro heq
      exact (Finset.not_disjoint_iff.mpr
        ⟨base (P j), by simp, by simp [heq]⟩) hcross.2
    let T₁ : Finset G := {leaf (P i), base (P j)}
    let T₂ : Finset G := {base (P i), leaf (P j)}
    have hT₁ : T₁ ∈ D.powerset := by
      rw [Finset.mem_powerset]
      intro x hx
      simp only [T₁, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hleaf (P i) (hPJ i)
      · exact hbase (P j) (hPJ j)
    have hT₂ : T₂ ∈ D.powerset := by
      rw [Finset.mem_powerset]
      intro x hx
      simp only [T₂, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hbase (P i) (hPJ i)
      · exact hleaf (P j) (hPJ j)
    have hdiff :
        leaf (P i) - base (P i) =
          leaf (P j) - base (P j) :=
      (hfixed (P i) (hPJ i)).trans (hfixed (P j) (hPJ j)).symm
    have hsum :
        leaf (P i) + base (P j) =
          base (P i) + leaf (P j) := by
      simpa [add_comm] using sub_eq_sub_iff_add_eq_add.mp hdiff
    have hT_eq : T₁ = T₂ := by
      apply hD T₁ hT₁ T₂ hT₂
      simpa [T₁, T₂, hbase_j_leaf_i.symm, hbase_i_leaf_j] using hsum
    have hbase_eq : base (P j) = base (P i) := by
      have hmem : base (P j) ∈ T₂ := by
        rw [← hT_eq]
        simp [T₁]
      simp only [T₂, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with heq | heq
      · exact heq
      · exact False.elim (hbase_leaf j heq)
    have hleaf_eq : leaf (P i) = leaf (P j) := by
      have hsum' := sub_eq_sub_iff_add_eq_add.mp hdiff
      rw [hbase_eq] at hsum'
      exact add_right_cancel hsum'
    have hP_eq : P i = P j := by
      rw [hrecover (P i) (hPJ i), hrecover (P j) (hPJ j), hleaf_eq]
    apply hij
    apply e.injective
    apply Subtype.ext
    exact hP_eq

/-- Exact statement-6 adapter from the discrepancy decomposition and the
fixed-discrepancy multiplicity bound.

The intended fill takes `I a` to be the zero-discrepancy inward spokes.
Every failed spoke has a nonzero discrepancy in
`t_a + (S - S)`; the preceding theorem bounds each fibre by `63`, giving
`|J(a) \ I(a)| ≤ 63 |S|²`, which is audited display
`arcB-s3-attempt.md` (1.8). The inward retained-spoke count then gives
the local lower bound (1.9).

Audit source: `arcB-s3-attempt.md` (1.8)-(1.9), with the decomposition and
pigeonhole argument in Bedert author LaTeX `main.tex:716-724,748-762`.
O5Banks statement-6 hypotheses served: all five hypotheses `hD`, `hsecond`,
`hρ`, `hretained`, and `hinward`; the conclusion is exactly the fact that
the body of `inward_successful_spokes_local_proposed` would invoke. -/
theorem inward_successful_spokes_local_from_multiplicity_proposed
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
  classical
  obtain ⟨base, shift, hdecomp⟩ :=
    inward_spoke_discrepancy_decomposition_proposed
      A D S G2 sel center ρ retained hsecond hρ
        (fun a ha => (hretained a ha).1)
  let inward : G → Finset (Finset G) := fun a =>
    (retained a).filter fun P => chosenY ρ P ∈ D + S
  let leaf : G → Finset G → G := fun a P =>
    (∑ x ∈ P, x) - center a
  let discrepancy : G → Finset G → G := fun a P =>
    leaf a P - base P
  let I : G → Finset (Finset G) := fun a =>
    (inward a).filter fun P => discrepancy a P = 0
  refine ⟨I, ?_, ?_, ?_⟩
  · intro a ha P hPI
    exact (Finset.mem_filter.mp hPI).1
  · intro a ha P hPI
    have hPIdata := Finset.mem_filter.mp hPI
    have hPdec :
        base P ∈ D ∧
          shift P ∈ S ∧
            chosenY ρ P = base P + shift P ∧
              leaf a P ∈ goodOne D S ∧
                P = {center a, leaf a P} ∧
                  discrepancy a P =
                    (a - (center a + sel (center a))) +
                      shift P - sel (leaf a P) := by
      simpa only [inward, leaf, discrepancy] using
        hdecomp a ha P hPIdata.1
    have hzero : discrepancy a P = 0 := hPIdata.2
    have hleaf_base : leaf a P = base P := by
      exact sub_eq_zero.mp hzero
    have hrhs_zero :
        (a - (center a + sel (center a))) +
              shift P - sel (leaf a P) =
            0 :=
      hPdec.2.2.2.2.2.symm.trans hzero
    have hshift_eq :
        sel (leaf a P) - (a - (center a + sel (center a))) =
          shift P := by
      calc
        sel (leaf a P) - (a - (center a + sel (center a))) =
            sel (leaf a P) - (a - (center a + sel (center a))) +
              ((a - (center a + sel (center a))) +
                shift P - sel (leaf a P)) := by
                  rw [hrhs_zero]
                  simp
        _ = shift P := by abel
    dsimp only
    change
      leaf a P ∈ goodOne D S ∧
        sel (leaf a P) - (a - (center a + sel (center a))) ∈ S ∧
          chosenY ρ P =
            leaf a P +
              (sel (leaf a P) - (a - (center a + sel (center a))))
    refine ⟨hPdec.2.2.2.1, ?_, ?_⟩
    · rw [hshift_eq]
      exact hPdec.2.1
    · calc
        chosenY ρ P = base P + shift P := hPdec.2.2.1
        _ = leaf a P + shift P := by rw [hleaf_base]
        _ = leaf a P +
            (sel (leaf a P) -
              (a - (center a + sel (center a)))) := by rw [hshift_eq]
  · intro a ha
    let J := inward a
    let Δ : Finset G → G := discrepancy a
    let failed := J.filter fun P => Δ P ≠ 0
    let t := a - (center a + sel (center a))
    let R := ({t} : Finset G) + (S - S)
    have hdecJ (P : Finset G) (hPJ : P ∈ J) :
        base P ∈ D ∧
          shift P ∈ S ∧
            chosenY ρ P = base P + shift P ∧
              leaf a P ∈ goodOne D S ∧
                P = {center a, leaf a P} ∧
                  Δ P = t + shift P - sel (leaf a P) := by
      simpa only [J, inward, Δ, discrepancy, leaf, t] using
        hdecomp a ha P hPJ
    have hR_card : R.card ≤ S.card ^ 2 := by
      calc
        R.card ≤ ({t} : Finset G).card * (S - S).card := by
          exact Finset.card_add_le
        _ = (S - S).card := by simp
        _ ≤ S.card * S.card := Finset.card_sub_le
        _ = S.card ^ 2 := by ring
    have hfailed_range : ∀ P ∈ failed, Δ P ∈ R := by
      intro P hPfailed
      have hPJ := (Finset.mem_filter.mp hPfailed).1
      have hPdec := hdecJ P hPJ
      have hleafD : leaf a P ∈ D :=
        (Finset.mem_sdiff.mp hPdec.2.2.2.1).1
      have hselS : sel (leaf a P) ∈ S :=
        (hρ.1 (leaf a P) hleafD).1
      change Δ P ∈ ({t} : Finset G) + (S - S)
      rw [Finset.mem_add]
      refine ⟨t, by simp, shift P - sel (leaf a P), ?_, ?_⟩
      · exact Finset.sub_mem_sub hPdec.2.1 hselS
      · simpa only [sub_eq_add_neg, add_assoc] using
          hPdec.2.2.2.2.2.symm
    have hfibre :
        ∀ δ ∈ R, (failed.filter fun P => Δ P = δ).card ≤ 63 := by
      intro δ _hδR
      by_cases hδ : δ = 0
      · subst δ
        have hempty : (failed.filter fun P => Δ P = 0) = ∅ := by
          ext P
          constructor
          · intro hP
            have hPdata := Finset.mem_filter.mp hP
            exact False.elim
              ((Finset.mem_filter.mp hPdata.1).2 hPdata.2)
          · intro hP
            simp at hP
        rw [hempty]
        simp
      · apply fixed_discrepancy_pair_multiplicity_le_proposed
          D (failed.filter fun P => Δ P = δ)
            (center a) δ base (leaf a) hD
        · intro P hP
          exact (hdecJ P
            (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1).1
        · intro P hP
          have hgood :=
            (hdecJ P
              (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1).2.2.2.1
          exact (Finset.mem_sdiff.mp hgood).1
        · intro P hP
          exact
            (hdecJ P
              (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1).2.2.2.2.1
        · exact hδ
        · intro P hP
          exact (Finset.mem_filter.mp hP).2
    let U := R.biUnion fun δ => failed.filter fun P => Δ P = δ
    have hfailed_sub : failed ⊆ U := by
      intro P hPfailed
      exact Finset.mem_biUnion.mpr
        ⟨Δ P, hfailed_range P hPfailed,
          Finset.mem_filter.mpr ⟨hPfailed, rfl⟩⟩
    have hfailed_card : failed.card ≤ 63 * S.card ^ 2 := by
      calc
        failed.card ≤ U.card := Finset.card_le_card hfailed_sub
        _ ≤ R.card * 63 := by
          apply Finset.card_biUnion_le_card_mul
          exact hfibre
        _ ≤ S.card ^ 2 * 63 := Nat.mul_le_mul_right 63 hR_card
        _ = 63 * S.card ^ 2 := by omega
    have hpartition : (I a).card + failed.card = J.card := by
      simpa only [I, J, inward, failed, Δ, discrepancy] using
        Finset.card_filter_add_card_filter_not
          (s := J) (p := fun P => Δ P = 0)
    have hinward' : 2 * J.card > (retained a).card := by
      simpa only [J, inward] using hinward a ha
    have hq_lt : fibreCount G2 ρ a < 6 * J.card := by
      have hq_retained := (hretained a ha).2
      omega
    have hq_real :
        (fibreCount G2 ρ a : ℝ) / 6 ≤ (J.card : ℝ) := by
      have hq_le : fibreCount G2 ρ a ≤ 6 * J.card :=
        Nat.le_of_lt hq_lt
      have hq_le' :
          (fibreCount G2 ρ a : ℝ) ≤ 6 * (J.card : ℝ) := by
        exact_mod_cast hq_le
      linarith
    have hfailed_real :
        (failed.card : ℝ) ≤ 63 * (S.card : ℝ) ^ 2 := by
      exact_mod_cast hfailed_card
    have hpartition_real :
        (J.card : ℝ) = ((I a).card : ℝ) + (failed.card : ℝ) := by
      exact_mod_cast hpartition.symm
    linarith

end ObjectLayer
end BedertLab
