/-
# Object layer, O2: the u-side target budget

Charter: candidates/bedert-omega/object-layer-charter.md, phase O2. This is the
budget half of the hostile-referee report's "single most load-bearing
unverified fact." The prose sources are:

* candidates/bedert-omega/conjecture-51-v2.md sec 1 (the closed choice object;
  S_u is display (1.2), i.e. main.tex `\eqref{S_ddefin}`);
* referee-report-2.md MAJOR-2 (the u-side budget, true as written);
* arcB-s3-attempt.md (3.2)-(3.3) (primary derivation).

The two statements below are the object-level forms:

* `uside_budget`: if the elements of `D₀` have pairwise differences outside
  `S - S` (except 0) — the property of Bedert's good set G^(1), since
  S - S ⊆ 2S - 2S — then the pairs (u, r), r ∈ S_u, inject into A via
  u + r, so ∑_u |S_u| ≤ |A|.
* `fibre_sum_eq`: for any selector s_u ∈ S_u, the target fibres
  F_t = {u ∈ D₀ : s_u - t ∈ S_u} satisfy ∑_{t ∈ S-S} |F_t| = ∑_u |S_u|
  (the change of variables r = s_u - t is a bijection).

Together: ∑_t |F_t| ≤ |A|, the budget consumed by `inwardBank_core`'s
`hbudget`. The connection "G^(1) differences avoid 2S - 2S ⊇ S - S" remains a
prose fact of the O3 layer and is NOT claimed here.

FROZEN STATEMENTS: fill the sorries only; do not alter any statement. If a
statement is unprovable as written, print BLOCKED with the reason.
-/
import BedertLab.ObjectLayer.O1Defs

open Pointwise

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The u-side budget: separated bases inject their spoke sets into `A`. -/
theorem uside_budget (A D₀ S : Finset G) (Su : G → Finset G)
    (hSu : ∀ u ∈ D₀, Su u ⊆ S)
    (hmem : ∀ u ∈ D₀, ∀ r ∈ Su u, u + r ∈ A)
    (havoid : ∀ u ∈ D₀, ∀ v ∈ D₀, u - v ∈ S - S → u = v) :
    ∑ u ∈ D₀, (Su u).card ≤ A.card := by
  let f : (Σ _ : G, G) → G := fun x => x.1 + x.2
  have hinj : Set.InjOn f (D₀.sigma Su) := by
    rintro ⟨u, r⟩ hur ⟨v, r'⟩ hvr' huv
    change ⟨u, r⟩ ∈ D₀.sigma Su at hur
    change ⟨v, r'⟩ ∈ D₀.sigma Su at hvr'
    rw [Finset.mem_sigma] at hur hvr'
    change u + r = v + r' at huv
    have huv_mem : u - v ∈ S - S := by
      have huv_eq : u - v = r' - r := by
        calc
          u - v = (u + r) - (v + r) := by abel
          _ = (v + r') - (v + r) := congrArg (fun x => x - (v + r)) huv
          _ = r' - r := by abel
      rw [huv_eq]
      exact Finset.sub_mem_sub (hSu v hvr'.1 hvr'.2) (hSu u hur.1 hur.2)
    have huv_base : u = v := havoid u hur.1 v hvr'.1 huv_mem
    subst v
    have hrr' : r = r' := by
      exact add_left_cancel huv
    subst r'
    rfl
  have himage : (D₀.sigma Su).image f ⊆ A := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨⟨u, r⟩, hur, rfl⟩ := hx
    rw [Finset.mem_sigma] at hur
    exact hmem u hur.1 r hur.2
  calc
    ∑ u ∈ D₀, (Su u).card = (D₀.sigma Su).card :=
      (Finset.card_sigma D₀ Su).symm
    _ = ((D₀.sigma Su).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ A.card := Finset.card_le_card himage

/-- Fibre change of variables: summing the target fibres over all labels
recovers the total spoke mass. -/
theorem fibre_sum_eq (D₀ S : Finset G) (Su : G → Finset G) (sel : G → G)
    (hSu : ∀ u ∈ D₀, Su u ⊆ S)
    (hsel : ∀ u ∈ D₀, sel u ∈ Su u) :
    ∑ t ∈ S - S, (D₀.filter fun u => sel u - t ∈ Su u).card
      = ∑ u ∈ D₀, (Su u).card := by
  have hcard (u : G) (hu : u ∈ D₀) :
      ((S - S).filter fun t => sel u - t ∈ Su u).card = (Su u).card := by
    refine Finset.card_nbij' (fun t => sel u - t) (fun r => sel u - r) ?_ ?_ ?_ ?_
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · intro r hr
      change sel u - r ∈ (S - S).filter fun t => sel u - t ∈ Su u
      rw [Finset.mem_filter]
      exact ⟨Finset.sub_mem_sub (hSu u hu (hsel u hu)) (hSu u hu hr), by simpa⟩
    · intro t ht
      simp
    · intro r hr
      simp
  calc
    ∑ t ∈ S - S, (D₀.filter fun u => sel u - t ∈ Su u).card =
        ∑ t ∈ S - S, ∑ u ∈ D₀.filter (fun u => sel u - t ∈ Su u), 1 := by
          simp
    _ = ∑ u ∈ D₀,
        ∑ t ∈ (S - S).filter (fun t => sel u - t ∈ Su u), 1 := by
          apply Finset.sum_comm'
          intro t u
          simp only [Finset.mem_filter]
          tauto
    _ = ∑ u ∈ D₀, ((S - S).filter fun t => sel u - t ∈ Su u).card := by
          simp
    _ = ∑ u ∈ D₀, (Su u).card := by
          exact Finset.sum_congr rfl hcard

end ObjectLayer
end BedertLab
