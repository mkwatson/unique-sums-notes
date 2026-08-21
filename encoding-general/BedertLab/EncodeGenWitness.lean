import BedertLab.EncodeGen

/-!
# Predicate-polymorphic witness kernel

The checker reduces any caller-supplied decidable predicate on finite subsets
of a finite abelian group.  Its correctness theorem is independent of the
particular predicate.
-/

namespace BedertLab.EncodeGenWitness

/-- Boolean witness checker for an arbitrary decidable subset predicate. -/
def checkWitness (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (predicate : Finset G → Prop) [DecidablePred predicate] (subset : Finset G) : Bool :=
  decide (predicate subset)

/-- The generalized witness checker accepts exactly valid witnesses. -/
theorem checkWitness_eq_true_iff (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (predicate : Finset G → Prop) [DecidablePred predicate]
    (subset : Finset G) :
    checkWitness G predicate subset = true ↔ predicate subset := by
  simp [checkWitness]

/-- Rejection by the generalized witness checker is exact. -/
theorem checkWitness_eq_false_iff (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (predicate : Finset G → Prop) [DecidablePred predicate]
    (subset : Finset G) :
    checkWitness G predicate subset = false ↔ ¬ predicate subset := by
  simp [checkWitness]

#print axioms checkWitness
#print axioms checkWitness_eq_true_iff
#print axioms checkWitness_eq_false_iff

end BedertLab.EncodeGenWitness
