import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Powerset

/-!
# Predicate-polymorphic exponential reference encoding

This module generalizes the membership-only reference encoding to an arbitrary
decidable predicate on finite subsets of a finite abelian group.  It remains an
exponential specification: one full blocking clause is emitted for each subset
which does not satisfy the predicate.
-/

namespace BedertLab.EncodeGen

/-- A signed membership literal. `positive = true` means membership. -/
structure Literal (G : Type*) where
  index : G
  positive : Bool
deriving DecidableEq, Repr

/-- A clause is a disjunction and a CNF is a conjunction of clauses. -/
abbrev Clause (G : Type*) := Finset (Literal G)
abbrev CNF (G : Type*) := Finset (Clause G)

/-- Evaluate one signed literal under a membership assignment. -/
def evalLiteral {G : Type*} (assignment : G → Bool) (literal : Literal G) : Bool :=
  if literal.positive then assignment literal.index else !(assignment literal.index)

/-- Propositional satisfaction for the finite-set representation of CNF. -/
def Satisfies {G : Type*} [DecidableEq G]
    (assignment : G → Bool) (cnf : CNF G) : Prop :=
  ∀ clause ∈ cnf, ∃ literal ∈ clause, evalLiteral assignment literal = true

instance satisfiesDecidable {G : Type*} [DecidableEq G]
    (assignment : G → Bool) (cnf : CNF G) : Decidable (Satisfies assignment cnf) := by
  unfold Satisfies
  infer_instance

/-- Decode membership variables as a finite subset of the group. -/
def decode (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (assignment : G → Bool) : Finset G :=
  Finset.univ.filter fun element => assignment element

/-- The unique full clause falsified by exactly the membership pattern `subset`. -/
def blockingClause (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (subset : Finset G) : Clause G :=
  Finset.univ.image fun element => ⟨element, decide (element ∉ subset)⟩

/-- Exponential reference encoder for an arbitrary decidable subset predicate. -/
def encode (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (predicate : Finset G → Prop) [DecidablePred predicate] : CNF G :=
  ((Finset.univ : Finset (Finset G)).filter fun subset => ¬ predicate subset).image
    (blockingClause G)

/-- A blocking clause is false exactly on the subset that it names. -/
theorem eval_blockingClause_false_iff (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (assignment : G → Bool) (subset : Finset G) :
    (¬ ∃ literal ∈ blockingClause G subset, evalLiteral assignment literal = true) ↔
      decode G assignment = subset := by
  classical
  constructor
  · intro h
    ext element
    rw [decode, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hmem :
        { index := element, positive := decide (element ∉ subset) } ∈
          blockingClause G subset := by
      exact Finset.mem_image.mpr ⟨element, Finset.mem_univ element, rfl⟩
    have heval :
        evalLiteral assignment
          { index := element, positive := decide (element ∉ subset) } ≠ true :=
      fun htrue => h ⟨_, hmem, htrue⟩
    by_cases hsubset : element ∈ subset <;>
      simp [evalLiteral, hsubset] at heval ⊢
    · exact heval
    · exact heval
  · intro h hexists
    obtain ⟨literal, hliteral, heval⟩ := hexists
    obtain ⟨element, _, rfl⟩ := Finset.mem_image.mp hliteral
    simp only [Finset.ext_iff] at h
    by_cases hsubset : element ∈ subset
    · have hdecode : element ∈ decode G assignment := (h element).2 hsubset
      have htrue : assignment element = true := by
        simpa [decode] using hdecode
      simp [evalLiteral, hsubset, htrue] at heval
    · have hnotDecode : element ∉ decode G assignment :=
        fun hdecode => hsubset ((h element).1 hdecode)
      have hfalse : assignment element = false := by
        simpa [decode] using hnotDecode
      simp [evalLiteral, hsubset, hfalse] at heval

/-- Pointwise faithfulness of the exponential reference encoder. -/
theorem satisfies_encode_iff (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (predicate : Finset G → Prop) [DecidablePred predicate] (assignment : G → Bool) :
    Satisfies assignment (encode G predicate) ↔ predicate (decode G assignment) := by
  classical
  constructor
  · intro hs
    by_contra hbad
    have hmem : decode G assignment ∈
        ((Finset.univ : Finset (Finset G)).filter fun subset => ¬ predicate subset) := by
      simp [hbad]
    have hclause : blockingClause G (decode G assignment) ∈ encode G predicate := by
      rw [encode]
      exact Finset.mem_image.mpr ⟨decode G assignment, hmem, rfl⟩
    obtain ⟨literal, _, hliteral⟩ := hs _ hclause
    exact (eval_blockingClause_false_iff G assignment (decode G assignment)).2 rfl
      ⟨literal, by assumption, hliteral⟩
  · intro hpredicate clause hclause
    rw [encode] at hclause
    obtain ⟨subset, hsubset, rfl⟩ := Finset.mem_image.mp hclause
    have hbad : ¬ predicate subset := (Finset.mem_filter.mp hsubset).2
    by_contra hnone
    have heq := (eval_blockingClause_false_iff G assignment subset).1 hnone
    exact hbad (heq ▸ hpredicate)

/-- Existential equisatisfiability of the exponential reference encoder. -/
theorem exists_model_iff_exists_predicate (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (predicate : Finset G → Prop) [DecidablePred predicate] :
    (∃ assignment : G → Bool, Satisfies assignment (encode G predicate)) ↔
      ∃ subset : Finset G, predicate subset := by
  constructor
  · rintro ⟨assignment, hs⟩
    exact ⟨decode G assignment, (satisfies_encode_iff G predicate assignment).mp hs⟩
  · rintro ⟨subset, hsubset⟩
    let assignment : G → Bool := fun element => decide (element ∈ subset)
    refine ⟨assignment, (satisfies_encode_iff G predicate assignment).2 ?_⟩
    simpa [decode, assignment]

#print axioms Literal
#print axioms Clause
#print axioms CNF
#print axioms evalLiteral
#print axioms Satisfies
#print axioms satisfiesDecidable
#print axioms decode
#print axioms blockingClause
#print axioms encode
#print axioms eval_blockingClause_false_iff
#print axioms satisfies_encode_iff
#print axioms exists_model_iff_exists_predicate

end BedertLab.EncodeGen
