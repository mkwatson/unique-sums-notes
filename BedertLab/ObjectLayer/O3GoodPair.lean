/-
# Object layer, O3: the first removal and the separation property

Charter: candidates/bedert-omega/object-layer-charter.md, phase O3 (first
half). Prose sources: Bedert main.tex `\eqref{B^1defin}` and `\eqref{B1small}`
(the original 2S - 2S removal), constant contract in
candidates/bedert-omega/constant-C-interface.md, and the certified
`two_families_pairs` (C₁ = 63) which the fill must consume for
`badOne_card_le`.

Definitions: `twoSsub S = S + S - S - S` (pointwise), `badOne D S` = the
elements of `D` translated back into `D` by a nonzero element of `2S - 2S`,
`goodOne D S = D \ badOne D S` (Bedert's G⁽¹⁾).

Statements:
* `sub_subset_twoSsub`: S - S ⊆ 2S - 2S when 0 ∈ S — the inclusion that
  lets O2's `uside_budget` consume `goodOne_sep`.
* `goodOne_sep`: two good elements whose difference lies in 2S - 2S are
  equal. This is the separation property O2's `havoid` needs (via the
  inclusion above), derived from the definition of the removal alone.
* `badOne_card_le`: |B⁽¹⁾| ≤ 63 · |S|⁴. The fill applies the certified
  Two Families pair lemma to the witness families {uᵢ}, {uᵢ + v} for each
  nonzero difference v, with dissociativity (`DissociatedF`) turning the
  cross-condition failure into a subset-sum collision.

FROZEN STATEMENTS: fill the sorries only; do not alter any statement or
definition. If a statement is unprovable as written, print BLOCKED with the
reason.
-/
import BedertLab.ObjectLayer.O1Defs
import BedertLab.TwoFamilies

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The pointwise difference set `2S - 2S = S + S - S - S`. -/
def twoSsub (S : Finset G) : Finset G := S + S - S - S

/-- Bedert's first bad set: elements of `D` moved back into `D` by a nonzero
element of `2S - 2S`. -/
def badOne (D S : Finset G) : Finset G :=
  D.filter fun u => ∃ v ∈ twoSsub S \ {0}, u + v ∈ D

/-- Bedert's good set `G⁽¹⁾`. -/
def goodOne (D S : Finset G) : Finset G := D \ badOne D S

/-- With `0 ∈ S`, single differences embed into `2S - 2S`. -/
theorem sub_subset_twoSsub (S : Finset G) (h0 : (0 : G) ∈ S) :
    S - S ⊆ twoSsub S := by
  intro x hx
  rw [Finset.mem_sub] at hx
  obtain ⟨r, hr, r', hr', rfl⟩ := hx
  unfold twoSsub
  rw [Finset.mem_sub]
  refine ⟨(r + 0) - r', ?_, 0, h0, by abel⟩
  rw [Finset.mem_sub]
  refine ⟨r + 0, ?_, r', hr', rfl⟩
  rw [Finset.mem_add]
  exact ⟨r, hr, 0, h0, rfl⟩

/-- Separation: good elements are not translates of each other by `2S - 2S`. -/
theorem goodOne_sep (D S : Finset G) :
    ∀ u ∈ goodOne D S, ∀ v ∈ goodOne D S, u - v ∈ twoSsub S → u = v := by
  intro u hu v hv huv
  by_contra huv_ne
  have huD : u ∈ D := (Finset.mem_sdiff.mp hu).1
  have hvD : v ∈ D := (Finset.mem_sdiff.mp hv).1
  have hv_good : v ∉ badOne D S := (Finset.mem_sdiff.mp hv).2
  apply hv_good
  rw [badOne, Finset.mem_filter]
  refine ⟨hvD, u - v, Finset.mem_sdiff.mpr ⟨huv, ?_⟩, ?_⟩
  · simpa using sub_ne_zero.mpr huv_ne
  · have hv_add : v + (u - v) = u := by abel
    simpa only [hv_add] using huD

/-- The original first-removal bound `|B⁽¹⁾| ≤ C₁ |S|⁴` with `C₁ = 63`. -/
theorem badOne_card_le (D S : Finset G) (hD : DissociatedF D) :
    (badOne D S).card ≤ 63 * S.card ^ 4 := by
  have witness_card_le (w : G) (hw : w ≠ 0) :
      (D.filter fun u => u + w ∈ D).card ≤ 63 := by
    let W := D.filter fun u => u + w ∈ D
    let e : Fin W.card ≃ W := W.equivFin.symm
    let u : Fin W.card → G := fun i => e i
    have huW (i : Fin W.card) : u i ∈ W := by
      change (e i : G) ∈ W
      exact (e i).property
    have huD (i : Fin W.card) : u i ∈ D :=
      (Finset.mem_filter.mp (huW i)).1
    have huDw (i : Fin W.card) : u i + w ∈ D :=
      (Finset.mem_filter.mp (huW i)).2
    have hu_injective : Function.Injective u := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact hij
    change W.card ≤ 63
    apply two_families_pairs
        (fun i => {u i}) (fun i => {u i + w})
    · intro i
      simp
    · intro i
      simp
    · intro i
      rw [Finset.disjoint_left]
      intro x hxu hxuw
      simp only [Finset.mem_singleton] at hxu hxuw
      subst x
      apply hw
      simpa using hxuw
    · intro i j hij
      by_contra hcross
      simp only [not_or, not_not] at hcross
      have hij_ne : u i ≠ u j + w := by
        intro heq
        exact (Finset.not_disjoint_iff.mpr
          ⟨u i, by simp, by simp [heq]⟩) hcross.1
      have hji_ne : u j ≠ u i + w := by
        intro heq
        exact (Finset.not_disjoint_iff.mpr
          ⟨u j, by simp, by simp [heq]⟩) hcross.2
      let T₁ : Finset G := {u i, u j + w}
      let T₂ : Finset G := {u j, u i + w}
      have hT₁ : T₁ ∈ D.powerset := by
        rw [Finset.mem_powerset]
        intro x hx
        simp only [T₁, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact huD i
        · exact huDw j
      have hT₂ : T₂ ∈ D.powerset := by
        rw [Finset.mem_powerset]
        intro x hx
        simp only [T₂, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact huD j
        · exact huDw i
      have hsum :
          ∑ x ∈ T₁, x = ∑ x ∈ T₂, x := by
        simp [T₁, T₂, hij_ne, hji_ne]
        abel
      have hT_eq : T₁ = T₂ := hD T₁ hT₁ T₂ hT₂ hsum
      have hui_mem : u i ∈ T₂ := by
        rw [← hT_eq]
        simp [T₁]
      simp only [T₂, Finset.mem_insert, Finset.mem_singleton] at hui_mem
      rcases hui_mem with hui_uj | hui_uiw
      · exact (hu_injective.ne hij) hui_uj
      · apply hw
        simpa using hui_uiw
  let U := (twoSsub S \ {0}).biUnion fun w =>
    D.filter fun u => u + w ∈ D
  have hbad_subset : badOne D S ⊆ U := by
    intro u hu
    rw [badOne, Finset.mem_filter] at hu
    obtain ⟨huD, w, hw, huwD⟩ := hu
    exact Finset.mem_biUnion.mpr
      ⟨w, hw, Finset.mem_filter.mpr ⟨huD, huwD⟩⟩
  have htwoSsub_card : (twoSsub S).card ≤ S.card ^ 4 := by
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
  calc
    (badOne D S).card ≤ U.card := Finset.card_le_card hbad_subset
    _ ≤ (twoSsub S \ {0}).card * 63 := by
      apply Finset.card_biUnion_le_card_mul
      intro w hw
      exact witness_card_le w (by simpa using (Finset.mem_sdiff.mp hw).2)
    _ ≤ (twoSsub S).card * 63 := by
      exact Nat.mul_le_mul_right 63 (Finset.card_le_card Finset.sdiff_subset)
    _ ≤ S.card ^ 4 * 63 := by gcongr
    _ = 63 * S.card ^ 4 := by omega

end ObjectLayer
end BedertLab
