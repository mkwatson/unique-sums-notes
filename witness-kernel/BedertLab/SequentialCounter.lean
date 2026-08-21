import BedertLab.ProjectionTheorem

/-!
# Frozen production sequential-counter boundary

This module freezes the exact clause semantics emitted by the campaign's
pinned production encoder (`usf_encode.py`; see the repository README for
provenance).  It deliberately separates that statement from
Codel's `(k + 1) × n` presentation: the two are Sinz variants with the same
existential semantics, but their clauses and auxiliary index sets are not
definitionally equal.
-/

namespace BedertLab.SequentialCounter

open BedertLab.ProjectionTheorem

/-- One `n × k` signal table, matching the allocation order
`s[i][j] = new()` in the production Python encoder. -/
abbrev Signal (n k : ℕ) := Fin n × Fin k

/-- Visible input `i`, interpreted in DIMACS order `i + 1`. -/
def input {n k : ℕ} (assignment : Sum (ZMod n) (Signal n k) → Bool)
    (i : Fin n) : Bool :=
  assignment (Sum.inl (i.val : ZMod n))

/-- Signal `s[i][j]`. -/
def signal {n k : ℕ} (assignment : Sum (ZMod n) (Signal n k) → Bool)
    (i : Fin n) (j : Fin k) : Bool :=
  assignment (Sum.inr (i, j))

/-- Exact propositional semantics of `seq_counter_atmost(cnf, lits, k)`.

The three branches are byte-for-byte structural counterparts of the Python
branches `k >= n`, `k == 0`, and `0 < k < n`.  In the final branch the five
conjuncts correspond respectively to the initial input clause, the remaining
initial-row unit clauses, propagation of column zero, propagation/advance of
later columns, and the overflow clauses. -/
def AtMostSat (n k : ℕ)
    (assignment : Sum (ZMod n) (Signal n k) → Bool) : Prop :=
  if k ≥ n then True
  else if hk : k = 0 then
    ∀ i : Fin n, input assignment i = false
  else if hn : n = 0 then False
  else
    let zeroN : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let zeroK : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    let lastK : Fin k := ⟨k - 1, by omega⟩
    (input assignment zeroN = true → signal assignment zeroN zeroK = true) ∧
    (∀ j : Fin k, 0 < j.val → signal assignment zeroN j = false) ∧
    (∀ i : Fin n, 0 < i.val →
      (input assignment i = true → signal assignment i zeroK = true) ∧
      (signal assignment ⟨i.val - 1, by omega⟩ zeroK = true →
        signal assignment i zeroK = true)) ∧
    (∀ i : Fin n, 0 < i.val → ∀ j : Fin k, 0 < j.val →
      (input assignment i = true ∧
          signal assignment ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ = true →
        signal assignment i j = true) ∧
      (signal assignment ⟨i.val - 1, by omega⟩ j = true →
        signal assignment i j = true)) ∧
    (∀ i : Fin n, 0 < i.val →
      input assignment i = true →
        signal assignment ⟨i.val - 1, by omega⟩ lastK = false)

/-- Frozen single-counter theorem, in Codel's existential-extension shape.

This is an obligation until a theorem of this type is proved.  Its right side
is `≤ k`, exactly the AMK constraint proved by Codel's `sc_amk_encodes_amk`. -/
def AtMostCorrect (n k : ℕ) [NeZero n] : Prop :=
  ∀ membership : ZMod n → Bool,
    (∃ counter : Signal n k → Bool,
      AtMostSat n k (combine membership counter)) ↔
      (Finset.univ.filter fun x => membership x).card ≤ k

/-- The two production counters are the positive AMK table and the negative
AMK table. -/
abbrev ExactCounter (n k : ℕ) := Sum (Signal n k) (Signal n (n - k))

def positiveAssignment {n k : ℕ}
    (assignment : Sum (ZMod n) (ExactCounter n k) → Bool) :
    Sum (ZMod n) (Signal n k) → Bool
  | Sum.inl x => assignment (Sum.inl x)
  | Sum.inr s => assignment (Sum.inr (Sum.inl s))

def negativeAssignment {n k : ℕ}
    (assignment : Sum (ZMod n) (ExactCounter n k) → Bool) :
    Sum (ZMod n) (Signal n (n - k)) → Bool
  | Sum.inl x => !(assignment (Sum.inl x))
  | Sum.inr s => assignment (Sum.inr (Sum.inr s))

/-- Exact conjunction emitted at the end of `encode(p,k)`. -/
def ExactSat (n k : ℕ)
    (assignment : Sum (ZMod n) (ExactCounter n k) → Bool) : Prop :=
  AtMostSat n k (positiveAssignment assignment) ∧
    AtMostSat n (n - k) (negativeAssignment assignment)

/-- Frozen theorem required by `ProjectionTheorem.SequentialCounterCorrect`. -/
def ExactCorrect (n k : ℕ) [NeZero n] : Prop :=
  SequentialCounterCorrect k (ExactSat n k)

/-- A deliberately inconsistent `k = 1`, `n = 2` assignment for the firing
control: `x₀` is true while `s₀₀` is false. -/
def tamperedTwo : Sum (ZMod 2) (Signal 2 1) → Bool
  | Sum.inl x => decide (x = 0)
  | Sum.inr _ => false

/-- Count the named initial clause when it is violated. -/
def initialViolationCount : ℕ :=
  if input tamperedTwo ⟨0, by omega⟩ = true ∧
      signal tamperedTwo ⟨0, by omega⟩ ⟨0, by omega⟩ = false then 1 else 0

theorem tamperedTwo_control :
    ¬ AtMostSat 2 1 tamperedTwo ∧ initialViolationCount = 1 := by
  simp [AtMostSat, input, signal, tamperedTwo, initialViolationCount]

#print axioms Signal
#print axioms input
#print axioms signal
#print axioms AtMostSat
#print axioms AtMostCorrect
#print axioms ExactCounter
#print axioms positiveAssignment
#print axioms negativeAssignment
#print axioms ExactSat
#print axioms ExactCorrect
#print axioms tamperedTwo
#print axioms initialViolationCount
#print axioms tamperedTwo_control

end BedertLab.SequentialCounter
