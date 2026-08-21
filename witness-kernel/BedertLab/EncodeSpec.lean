import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.ZMod.Basic

/-!
# Reference CNF specification for cyclic USF search

This is deliberately an exponential reference encoder.  It uses only membership
variables and excludes every membership pattern which fails the exact-cardinality
and ordered-representation predicate.  Its purpose is a small, auditable semantic
specification against which production encoders can be tested.
-/

namespace BedertLab.EncodeSpec

/- The two predicates below are a byte-for-byte semantic restatement of the
frozen `ObjectLayer.O1Defs` trust boundary.  Importing that legacy module pulls
the forbidden broad `Mathlib` import into this process and exhausts this host. -/

/-- One unordered representation of `s`, expressed by its two orientations. -/
def HasUniqueSum {n : ℕ} [NeZero n] (A : Finset (ZMod n)) (s : ZMod n) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a + b = s ∧
    ∀ c ∈ A, ∀ d ∈ A, c + d = s → (c = a ∧ d = b) ∨ (c = b ∧ d = a)

/-- No group element has exactly one unordered representation. -/
def IsUSF {n : ℕ} [NeZero n] (A : Finset (ZMod n)) : Prop :=
  ∀ s : ZMod n, ¬ HasUniqueSum A s

instance {n : ℕ} [NeZero n] (A : Finset (ZMod n)) (s : ZMod n) :
    Decidable (HasUniqueSum A s) := by
  unfold HasUniqueSum
  infer_instance

instance {n : ℕ} [NeZero n] (A : Finset (ZMod n)) : Decidable (IsUSF A) := by
  unfold IsUSF
  infer_instance

/-- A signed membership literal.  `positive = true` means membership. -/
structure Literal (n : ℕ) [NeZero n] where
  index : ZMod n
  positive : Bool
deriving DecidableEq, Repr

/-- A clause is a disjunction and a CNF is a conjunction of clauses. -/
abbrev Clause (n : ℕ) [NeZero n] := Finset (Literal n)
abbrev CNF (n : ℕ) [NeZero n] := Finset (Clause n)

/-- Evaluate one signed literal under a membership assignment. -/
def evalLiteral {n : ℕ} [NeZero n] (assignment : ZMod n → Bool)
    (literal : Literal n) : Bool :=
  if literal.positive then assignment literal.index else !(assignment literal.index)

/-- Propositional satisfaction for the concrete list-of-clauses representation. -/
def Satisfies {n : ℕ} [NeZero n] (assignment : ZMod n → Bool) (cnf : CNF n) : Prop :=
  ∀ clause ∈ cnf, ∃ literal ∈ clause, evalLiteral assignment literal = true

/-- Decode membership variables as a finite subset of the cyclic group. -/
def decode {n : ℕ} [NeZero n] (assignment : ZMod n → Bool) : Finset (ZMod n) :=
  Finset.univ.filter fun i => assignment i

/-- Ordered representation count as the cardinality of the ordered-pair fibre. -/
def orderedRepresentationCount {n : ℕ} [NeZero n]
    (A : Finset (ZMod n)) (s : ZMod n) : ℕ :=
  (A ×ˢ A).filter (fun pair => pair.1 + pair.2 = s) |>.card

/-- The ordered-count formulation requested by the search specification. -/
def OrderedUSF {n : ℕ} [NeZero n] (A : Finset (ZMod n)) : Prop :=
  ∀ s : ZMod n,
    orderedRepresentationCount A s ≠ 1 ∧ orderedRepresentationCount A s ≠ 2

/-- The exact mathematical predicate represented by the reference instance. -/
def Target {n : ℕ} [NeZero n] (k : ℕ) (A : Finset (ZMod n)) : Prop :=
  A.card = k ∧ IsUSF A

instance {n : ℕ} [NeZero n] (k : ℕ) (A : Finset (ZMod n)) : Decidable (Target k A) := by
  unfold Target
  infer_instance

/-- The unique full clause falsified by exactly the membership pattern `A`. -/
def blockingClause {n : ℕ} [NeZero n] (A : Finset (ZMod n)) : Clause n :=
  Finset.univ.image fun i => ⟨i, decide (i ∉ A)⟩

/-- Exponential reference encoding: exclude exactly all bad membership patterns. -/
def encode (n k : ℕ) [NeZero n] : CNF n :=
  ((Finset.univ : Finset (Finset (ZMod n))).filter fun A => ¬ Target k A).image
    blockingClause

theorem eval_blockingClause_false_iff {n : ℕ} [NeZero n]
    (assignment : ZMod n → Bool) (A : Finset (ZMod n)) :
    (¬ ∃ literal ∈ blockingClause A, evalLiteral assignment literal = true) ↔
      decode assignment = A := by
  classical
  constructor
  · intro h
    ext i
    rw [decode, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hmem : { index := i, positive := decide (i ∉ A) } ∈ blockingClause A := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hi : evalLiteral assignment { index := i, positive := decide (i ∉ A) } ≠ true :=
      fun heval => h ⟨_, hmem, heval⟩
    by_cases hA : i ∈ A <;> simp [evalLiteral, hA] at hi ⊢
    · exact hi
    · exact hi
  · intro h hexists
    obtain ⟨literal, hliteral, heval⟩ := hexists
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hliteral
    simp only [Finset.ext_iff] at h
    by_cases hA : i ∈ A
    · have hiDecode : i ∈ decode assignment := (h i).2 hA
      have hiTrue : assignment i = true := by simpa [decode] using hiDecode
      simp [evalLiteral, hA, hiTrue] at heval
    · have hiNotDecode : i ∉ decode assignment := fun hi => hA ((h i).1 hi)
      have hiFalse : assignment i = false := by simpa [decode] using hiNotDecode
      simp [evalLiteral, hA, hiFalse] at heval

theorem satisfies_encode_iff {n k : ℕ} [NeZero n] (assignment : ZMod n → Bool) :
    Satisfies assignment (encode n k) ↔ Target k (decode assignment) := by
  classical
  constructor
  · intro hs
    by_contra hbad
    have hmem : decode assignment ∈
        ((Finset.univ : Finset (Finset (ZMod n))).filter fun A => ¬ Target k A) := by
      simp [hbad]
    have hclause : blockingClause (decode assignment) ∈ encode n k := by
      rw [encode]
      exact Finset.mem_image.mpr ⟨decode assignment, hmem, rfl⟩
    obtain ⟨literal, _, hliteral⟩ := hs _ hclause
    exact (eval_blockingClause_false_iff assignment (decode assignment)).2 rfl
      ⟨literal, by assumption, hliteral⟩
  · intro htarget clause hclause
    rw [encode] at hclause
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hclause
    have hbad : ¬ Target k A := by
      exact (Finset.mem_filter.mp hA).2
    by_contra hnone
    have heq := (eval_blockingClause_false_iff assignment A).1 hnone
    exact hbad (heq ▸ htarget)

theorem exists_model_iff_exists_target (n k : ℕ) [NeZero n] :
    (∃ assignment : ZMod n → Bool, Satisfies assignment (encode n k)) ↔
      ∃ A : Finset (ZMod n), Target k A := by
  constructor
  · rintro ⟨assignment, hs⟩
    exact ⟨decode assignment, (satisfies_encode_iff assignment).mp hs⟩
  · rintro ⟨A, hA⟩
    let assignment : ZMod n → Bool := fun i => decide (i ∈ A)
    refine ⟨assignment, (satisfies_encode_iff assignment).2 ?_⟩
    simpa [decode, assignment]

#print axioms Literal
#print axioms HasUniqueSum
#print axioms IsUSF
#print axioms instDecidableHasUniqueSum
#print axioms instDecidableIsUSF
#print axioms Clause
#print axioms CNF
#print axioms evalLiteral
#print axioms Satisfies
#print axioms decode
#print axioms orderedRepresentationCount
#print axioms OrderedUSF
#print axioms Target
#print axioms instDecidableTarget
#print axioms blockingClause
#print axioms encode
#print axioms eval_blockingClause_false_iff
#print axioms satisfies_encode_iff
#print axioms exists_model_iff_exists_target

end BedertLab.EncodeSpec
