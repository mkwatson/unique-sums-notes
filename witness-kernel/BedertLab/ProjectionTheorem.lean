import BedertLab.EncodeSpec

/-!
# Existential projection for encodings with auxiliary variables

This module is a semantic boundary.  It deliberately says nothing about the
clause representation used by a production encoder.  Membership variables and
auxiliary variables are separated by `Sum`, and encoder correctness means that
existentially choosing the auxiliary block is equivalent to the reference
predicate on the membership block.
-/

namespace BedertLab.ProjectionTheorem

/-- Restrict a total assignment to its membership-variable block. -/
def restrictMembership {Membership Auxiliary : Type}
    (assignment : Sum Membership Auxiliary → Bool) : Membership → Bool :=
  fun x => assignment (Sum.inl x)

/-- Restrict a total assignment to its auxiliary-variable block. -/
def restrictAuxiliary {Membership Auxiliary : Type}
    (assignment : Sum Membership Auxiliary → Bool) : Auxiliary → Bool :=
  fun x => assignment (Sum.inr x)

/-- Combine independently chosen membership and auxiliary assignments. -/
def combine {Membership Auxiliary : Type}
    (membership : Membership → Bool) (auxiliary : Auxiliary → Bool) :
    Sum Membership Auxiliary → Bool :=
  Sum.elim membership auxiliary

/-- The frozen semantic API for an encoder with existential temporary variables.

This is the same quantifier shape as a `withTemps` encoding: after the visible
assignment is fixed, the temporary block may be chosen existentially. -/
def ProjectsTo {Membership Auxiliary : Type}
    (production : (Sum Membership Auxiliary → Bool) → Prop)
    (reference : (Membership → Bool) → Prop) : Prop :=
  ∀ membership, (∃ auxiliary, production (combine membership auxiliary)) ↔
    reference membership

/-- Soundness under projection: every production model yields a reference model. -/
theorem project_model {Membership Auxiliary : Type}
    {production : (Sum Membership Auxiliary → Bool) → Prop}
    {reference : (Membership → Bool) → Prop}
    (correct : ProjectsTo production reference)
    {assignment : Sum Membership Auxiliary → Bool}
    (model : production assignment) :
    reference (restrictMembership assignment) := by
  apply (correct (restrictMembership assignment)).mp
  refine ⟨restrictAuxiliary assignment, ?_⟩
  have hcombine :
      combine (restrictMembership assignment) (restrictAuxiliary assignment) =
        assignment := by
    funext x
    cases x <;> rfl
  rw [hcombine]
  exact model

/-- Completeness by extension: every reference model has a production extension. -/
theorem extend_model {Membership Auxiliary : Type}
    {production : (Sum Membership Auxiliary → Bool) → Prop}
    {reference : (Membership → Bool) → Prop}
    (correct : ProjectsTo production reference)
    {membership : Membership → Bool}
    (model : reference membership) :
    ∃ auxiliary, production (combine membership auxiliary) :=
  (correct membership).mpr model

/-- Model existence is preserved exactly by existential projection. -/
theorem exists_model_iff {Membership Auxiliary : Type}
    {production : (Sum Membership Auxiliary → Bool) → Prop}
    {reference : (Membership → Bool) → Prop}
    (correct : ProjectsTo production reference) :
    (∃ assignment, production assignment) ↔ ∃ membership, reference membership := by
  constructor
  · rintro ⟨assignment, model⟩
    exact ⟨restrictMembership assignment, project_model correct model⟩
  · rintro ⟨membership, model⟩
    obtain ⟨auxiliary, model⟩ := extend_model correct model
    exact ⟨combine membership auxiliary, model⟩

/-- With no auxiliary variables, existential projection reduces to ordinary
pointwise equivalence.  The impossible auxiliary assignment is supplied
explicitly, so this is a proved vacuity witness rather than an assertion. -/
theorem projectsTo_empty_iff {Membership : Type}
    (production : (Sum Membership Empty → Bool) → Prop)
    (reference : (Membership → Bool) → Prop) :
    ProjectsTo production reference ↔
      ∀ membership, production (combine membership Empty.elim) ↔
        reference membership := by
  constructor
  · intro correct membership
    constructor
    · intro model
      exact (correct membership).mp ⟨Empty.elim, model⟩
    · intro model
      obtain ⟨auxiliary, productionModel⟩ := (correct membership).mpr model
      have auxiliaryEq : auxiliary = Empty.elim := by
        funext x
        exact Empty.elim x
      rw [auxiliaryEq] at productionModel
      exact productionModel
  · intro pointwise membership
    constructor
    · rintro ⟨auxiliary, model⟩
      have auxiliaryEq : auxiliary = Empty.elim := by
        funext x
        exact Empty.elim x
      exact (pointwise membership).mp (by simpa [auxiliaryEq] using model)
    · intro model
      exact ⟨Empty.elim, (pointwise membership).mpr model⟩

/-- Pair auxiliaries have one variable for every ordered pair of membership
variables.  Production may later restrict this type to canonical unordered
pairs without changing the projection API. -/
abbrev PairVariable (Membership : Type) := Membership × Membership

/-- The Tseitin meaning of all pair variables: `y_(a,b) ↔ x_a ∧ x_b`. -/
def PairConsistent {Membership : Type}
    (assignment : Sum Membership (PairVariable Membership) → Bool) : Prop :=
  ∀ a b, assignment (Sum.inr (a, b)) =
    (assignment (Sum.inl a) && assignment (Sum.inl b))

/-- The canonical auxiliary assignment for pair variables. -/
def pairWitness {Membership : Type} (membership : Membership → Bool) :
    PairVariable Membership → Bool :=
  fun pair => membership pair.1 && membership pair.2

/-- Pair definitions alone project exactly to the visible predicate. -/
def PairProduction {Membership : Type}
    (reference : (Membership → Bool) → Prop)
    (assignment : Sum Membership (PairVariable Membership) → Bool) : Prop :=
  reference (restrictMembership assignment) ∧ PairConsistent assignment

/-- The production pair block has a canonical extension and cannot restrict the
set of visible models. -/
theorem pair_projectsTo {Membership : Type}
    (reference : (Membership → Bool) → Prop) :
    ProjectsTo (PairProduction reference) reference := by
  intro membership
  constructor
  · rintro ⟨auxiliary, model, _⟩
    simpa [PairProduction, restrictMembership, combine] using model
  · intro model
    refine ⟨pairWitness membership, ?_, ?_⟩
    · simpa [PairProduction, restrictMembership, combine] using model
    · intro a b
      rfl

/-- Pair definitions for an arbitrary encoder-owned pair index type.  Endpoint
maps make this directly usable by compact encoders that allocate only canonical
unordered, off-diagonal pairs. -/
def PairConsistentFor {Membership Pair : Type}
    (left right : Pair → Membership)
    (assignment : Sum Membership Pair → Bool) : Prop :=
  ∀ pair, assignment (Sum.inr pair) =
    (assignment (Sum.inl (left pair)) && assignment (Sum.inl (right pair)))

/-- Canonical witnesses for an encoder-owned pair index type. -/
def pairWitnessFor {Membership Pair : Type}
    (left right : Pair → Membership) (membership : Membership → Bool) :
    Pair → Bool :=
  fun pair => membership (left pair) && membership (right pair)

/-- Pair-definition production predicate for an arbitrary pair index block. -/
def PairProductionFor {Membership Pair : Type}
    (left right : Pair → Membership)
    (reference : (Membership → Bool) → Prop)
    (assignment : Sum Membership Pair → Bool) : Prop :=
  reference (restrictMembership assignment) ∧
    PairConsistentFor left right assignment

/-- Arbitrarily indexed pair definitions have exact existential projection. -/
theorem pairFor_projectsTo {Membership Pair : Type}
    (left right : Pair → Membership)
    (reference : (Membership → Bool) → Prop) :
    ProjectsTo (PairProductionFor left right reference) reference := by
  intro membership
  constructor
  · rintro ⟨auxiliary, model, _⟩
    simpa [PairProductionFor, restrictMembership, combine] using model
  · intro model
    refine ⟨pairWitnessFor left right membership, ?_, ?_⟩
    · simpa [PairProductionFor, restrictMembership, combine] using model
    · intro pair
      rfl

/-- Exact pair-variable index block used by the campaign's pinned production
encoder (`usf_encode.py`; see the repository README for provenance):
canonical integer representatives `a < b`, hence no diagonal and no duplicate
orientation. -/
abbrev ProductionPairVariable (n : ℕ) :=
  {pair : ZMod n × ZMod n // pair.1.val < pair.2.val}

/-- Left endpoint of a production pair variable. -/
def productionPairLeft {n : ℕ} (pair : ProductionPairVariable n) : ZMod n :=
  pair.1.1

/-- Right endpoint of a production pair variable. -/
def productionPairRight {n : ℕ} (pair : ProductionPairVariable n) : ZMod n :=
  pair.1.2

/-- The exact production pair-variable block projects without restricting any
membership assignment. -/
theorem productionPair_projectsTo (n : ℕ)
    (reference : (ZMod n → Bool) → Prop) :
    ProjectsTo
      (PairProductionFor productionPairLeft productionPairRight reference)
      reference :=
  pairFor_projectsTo productionPairLeft productionPairRight reference

/-- Frozen remaining obligation for the exact-cardinality part of production.

For the campaign's pinned production encoder (`usf_encode.py`; see the
repository README for provenance), `counterSat` must denote the conjunction of
the Sinz `atMost k` counter on the membership literals and the Sinz
`atMost (n-k)` counter on their negations.  Proving this predicate supplies both
directions: counters can be constructed for every assignment of cardinality
`k`, and every satisfying counter assignment has cardinality `k`. -/
def SequentialCounterCorrect {Membership Counter : Type}
    [Fintype Membership] [DecidableEq Membership]
    (k : ℕ) (counterSat : (Sum Membership Counter → Bool) → Prop) : Prop :=
  ∀ membership,
    (∃ counter, counterSat (combine membership counter)) ↔
      (Finset.univ.filter fun x => membership x).card = k

/-- Variables of the production encoding: visible membership variables, then
pair variables, then sequential-counter variables. -/
abbrev ProductionVariable (n : ℕ) (Counter : Type) :=
  Sum (ZMod n) (Sum (ProductionPairVariable n) Counter)

/-- Frozen production-equivalence statement.  This is intentionally a semantic
obligation on the real production formula, not clause equality with the
exponential reference formula. -/
def ProductionEquivalent (n k : ℕ) [NeZero n] (Counter : Type)
    (production : (ProductionVariable n Counter → Bool) → Prop) : Prop :=
  ProjectsTo production fun membership =>
    BedertLab.EncodeSpec.Satisfies membership
      (BedertLab.EncodeSpec.encode n k)

/- The frozen reference theorem is printed immediately before the production
typecheck theorem and again at the end of the module. -/
#print axioms BedertLab.EncodeSpec.satisfies_encode_iff

/-- Completion test: the correct production statement composes with the
untouched frozen reference theorem and has both implications. -/
theorem production_equivalence_typecheck {n k : ℕ} [NeZero n]
    {Counter : Type}
    {production : (ProductionVariable n Counter → Bool) → Prop}
    (correct : ProductionEquivalent n k Counter production)
    (membership : ZMod n → Bool) :
    (∃ auxiliary, production (combine membership auxiliary)) ↔
      BedertLab.EncodeSpec.Target k (BedertLab.EncodeSpec.decode membership) := by
  rw [correct membership]
  exact BedertLab.EncodeSpec.satisfies_encode_iff membership

/-- Number of violated pair definitions, used as a firing negative control. -/
def pairViolationCount {Membership : Type} [Fintype Membership]
    [DecidableEq Membership]
    (assignment : Sum Membership (PairVariable Membership) → Bool) : ℕ :=
  (Finset.univ.filter fun pair =>
    assignment (Sum.inr pair) !=
      (assignment (Sum.inl pair.1) && assignment (Sum.inl pair.2))).card

/-- One visible true variable and one inconsistent false pair variable. -/
def inconsistentOne : Sum (Fin 1) (PairVariable (Fin 1)) → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- The deliberately wrong assertion exercised by the negative control. -/
def WrongPairProjectionClaim : Prop :=
  PairConsistent inconsistentOne

instance : Decidable WrongPairProjectionClaim := by
  unfold WrongPairProjectionClaim PairConsistent
  infer_instance

/-- Negative control: the wrong claim that arbitrary auxiliaries preserve the
pair definitions is refuted in-kernel, and exactly one definition fires. -/
theorem inconsistentOne_control :
    ¬ WrongPairProjectionClaim ∧
      pairViolationCount inconsistentOne = 1 := by
  decide

#print axioms restrictMembership
#print axioms restrictAuxiliary
#print axioms combine
#print axioms ProjectsTo
#print axioms project_model
#print axioms extend_model
#print axioms exists_model_iff
#print axioms projectsTo_empty_iff
#print axioms PairVariable
#print axioms PairConsistent
#print axioms pairWitness
#print axioms PairProduction
#print axioms pair_projectsTo
#print axioms PairConsistentFor
#print axioms pairWitnessFor
#print axioms PairProductionFor
#print axioms pairFor_projectsTo
#print axioms ProductionPairVariable
#print axioms productionPairLeft
#print axioms productionPairRight
#print axioms productionPair_projectsTo
#print axioms SequentialCounterCorrect
#print axioms ProductionVariable
#print axioms ProductionEquivalent
#print axioms production_equivalence_typecheck
#print axioms pairViolationCount
#print axioms inconsistentOne
#print axioms WrongPairProjectionClaim
#print axioms instDecidableWrongPairProjectionClaim
#print axioms inconsistentOne_control

#print axioms BedertLab.EncodeSpec.satisfies_encode_iff

end BedertLab.ProjectionTheorem
