/-
# Object layer, O1: frozen definitions

Charter: candidates/bedert-omega/object-layer-charter.md. These definitions are
TRUST BOUNDARIES for the whole object-layer campaign (hostile-referee finding 2):
every later object-level theorem quotes them. They were frozen by the claim-type
checklist on 2026-07-23.

* `HasUniqueSum A s` / `IsUSF A`: literal transcription of "A has no unique sum"
  (Bedert, main.tex introduction): s has a unique sum in A when it has exactly
  one unordered representation a + b with a, b in A; A is USF when no s has one.
  Stated without a nonemptiness clause; theorems that need `A.Nonempty` or
  `0 < dimA A` carry them explicitly (note-v3 sec 1 domain conventions).
* `DissociatedF D`: distinct subset sums, the form used by the campaign
  (2^d <= p bridge, frontier.py semantics). `dissociatedF_iff_addDissociated`
  ties it to Mathlib's `AddDissociated`, so Mathlib's API is available and the
  definition cannot silently drift from the literature.
* `dimA A`: the largest cardinality of a subset of A with distinct subset sums.
* `KA A`: |A| / dimA A as a rational. Division-by-zero yields the junk value 0
  when dimA A = 0 (e.g. A = ∅ or A = {0}); every theorem about KA must assume
  `0 < dimA A`.

Guard theorems (kernel-checked, no native_decide) pin the definitions against
vacuity and sign errors. FROZEN: fills may not alter any statement in this
file; print BLOCKED instead.
-/
import Mathlib

namespace BedertLab
namespace ObjectLayer

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- `s` has a unique sum in `A`: exactly one unordered representation. -/
def HasUniqueSum (A : Finset G) (s : G) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a + b = s ∧
    ∀ c ∈ A, ∀ d ∈ A, c + d = s → (c = a ∧ d = b) ∨ (c = b ∧ d = a)

/-- Bedert's no-unique-sum condition. -/
def IsUSF (A : Finset G) : Prop := ∀ s : G, ¬ HasUniqueSum A s

/-- Distinct subset sums (Finset form of `AddDissociated`). -/
def DissociatedF (D : Finset G) : Prop :=
  ∀ T₁ ∈ D.powerset, ∀ T₂ ∈ D.powerset, ∑ x ∈ T₁, x = ∑ x ∈ T₂, x → T₁ = T₂

instance (A : Finset G) (s : G) : Decidable (HasUniqueSum A s) := by
  unfold HasUniqueSum; infer_instance

instance (D : Finset G) : Decidable (DissociatedF D) := by
  unfold DissociatedF; infer_instance

/-- The dissociativity dimension: the largest size of a subset with distinct
subset sums. -/
def dimA (A : Finset G) : ℕ :=
  ((A.powerset.filter fun D => DissociatedF D).image Finset.card).sup id

/-- Bedert's K(A) as a rational; junk value 0 when `dimA A = 0`. -/
def KA (A : Finset G) : ℚ := (A.card : ℚ) / (dimA A : ℚ)

set_option linter.unusedSectionVars false in
/-- Bridge to Mathlib: our Finset predicate is Mathlib's `AddDissociated`. -/
theorem dissociatedF_iff_addDissociated (D : Finset G) :
    DissociatedF D ↔ AddDissociated (↑D : Set G) := by
  constructor
  · intro h T₁ hT₁ T₂ hT₂ hsum
    apply h T₁ (Finset.mem_powerset.mpr (Finset.coe_subset.mp hT₁))
      T₂ (Finset.mem_powerset.mpr (Finset.coe_subset.mp hT₂)) hsum
  · intro h T₁ hT₁ T₂ hT₂ hsum
    apply h (Finset.coe_subset.mpr (Finset.mem_powerset.mp hT₁))
      (Finset.coe_subset.mpr (Finset.mem_powerset.mp hT₂)) hsum

/-- Guard: the full group `ZMod 5` has no unique sum. -/
theorem guard_univ_usf : IsUSF (Finset.univ : Finset (ZMod 5)) := by
  intro s
  fin_cases s <;> decide

/-- Guard: a singleton is never USF (its double is a unique sum). -/
theorem guard_singleton_not_usf : ¬ IsUSF ({1} : Finset (ZMod 5)) := by
  intro h
  exact h 2 (by decide)

/-- Guard: `{1, 2}` has distinct subset sums in `ZMod 7`. -/
theorem guard_dissociated_pair : DissociatedF ({1, 2} : Finset (ZMod 7)) := by
  decide

/-- Guard: `{1, 2, 3}` does not (1 + 2 = 3). -/
theorem guard_not_dissociated_triple :
    ¬ DissociatedF ({1, 2, 3} : Finset (ZMod 7)) := by
  decide

/-- Guard: `{0}` is not dissociated, so `dimA {0} = 0` (the KA junk case). -/
theorem guard_dim_zero_singleton : dimA ({0} : Finset (ZMod 5)) = 0 := by
  decide

end ObjectLayer
end BedertLab
