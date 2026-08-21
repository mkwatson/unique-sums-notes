import BedertLab.ByteBridgeAux
import BedertLab.SequentialCounterProof

/-!
# Production clause correspondence at `(11, 7)`

This module owns no byte parser.  It records the variable layout emitted by
the campaign's pinned production encoder (`usf_encode.py`; see the
repository README for provenance) and isolates the remaining structural
clause-family theorem from the byte-level parse equation.
-/

namespace BedertLab.ClauseCorrespondence

set_option maxRecDepth 10000

open BedertLab.ByteBridgeAux
open BedertLab.ProjectionTheorem
open BedertLab.SequentialCounter

/-- The 55 pair variables in encoder allocation order. -/
abbrev PairSlot117 := Fin 55

/-- Logical auxiliary variables emitted by `encode(11, 7)`: 55 pair variables,
then the positive `11 × 7` table, then the negative `11 × 4` table. -/
abbrev ProductionAux117 := Sum PairSlot117 (ExactCounter 11 7)

/-- Zero-based DIMACS auxiliary offset.  This is the allocation arithmetic in
`CNF.new`: pair block, positive row-major table, negative row-major table. -/
def auxiliaryOffset : ProductionAux117 → Fin 176
  | Sum.inl pair => ⟨pair.val, by omega⟩
  | Sum.inr (Sum.inl signal) =>
      ⟨55 + signal.1.val * 7 + signal.2.val, by omega⟩
  | Sum.inr (Sum.inr signal) =>
      ⟨132 + signal.1.val * 4 + signal.2.val, by omega⟩

/-- Inverse of the three encoder allocation blocks. -/
def auxiliaryAtOffset : Fin 176 → ProductionAux117 := fun offset =>
  if hpair : offset.val < 55 then
    Sum.inl ⟨offset.val, hpair⟩
  else if hpositive : offset.val < 132 then
    Sum.inr (Sum.inl
      (⟨(offset.val - 55) / 7, by omega⟩,
       ⟨(offset.val - 55) % 7, Nat.mod_lt _ (by omega)⟩))
  else
    Sum.inr (Sum.inr
      (⟨(offset.val - 132) / 4, by omega⟩,
       ⟨(offset.val - 132) % 4, Nat.mod_lt _ (by omega)⟩))

theorem auxiliaryAtOffset_leftInverse :
    Function.LeftInverse auxiliaryAtOffset auxiliaryOffset := by
  intro auxiliary
  rcases auxiliary with pair | counter
  · simp [auxiliaryOffset, auxiliaryAtOffset]
  · rcases counter with positive | negative
    · simp only [auxiliaryOffset, auxiliaryAtOffset]
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 3 <;> apply Fin.ext <;> simp <;> omega
    · simp only [auxiliaryOffset, auxiliaryAtOffset]
      rw [dif_neg (by omega), dif_neg (by omega)]
      congr 3 <;> apply Fin.ext <;> simp <;> omega

theorem auxiliaryAtOffset_rightInverse :
    Function.RightInverse auxiliaryAtOffset auxiliaryOffset := by
  intro offset
  apply Fin.ext
  simp only [auxiliaryAtOffset]
  split_ifs with hpair hpositive
  · simp [auxiliaryOffset]
  · simp [auxiliaryOffset]
    omega
  · simp [auxiliaryOffset]
    omega

/-- Exact auxiliary-index equivalence for DIMACS variables 12 through 187. -/
def auxiliaryIndexEquiv : ProductionAux117 ≃ Fin 176 where
  toFun := auxiliaryOffset
  invFun := auxiliaryAtOffset
  left_inv := auxiliaryAtOffset_leftInverse
  right_inv := auxiliaryAtOffset_rightInverse

/-- Lift a logically indexed production assignment to the parser's unbounded
auxiliary-offset representation. Values outside the declared 176-offset block
are irrelevant to every well-formed `(11,187)` CNF. -/
def parserAssignment
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) :
    Variable 11 187 → Bool
  | Sum.inl membership => assignment (Sum.inl membership)
  | Sum.inr offset =>
      if h : offset < 176 then
        assignment (Sum.inr (auxiliaryAtOffset ⟨offset, h⟩))
      else false

/-- Restrict a full production assignment to the visible and counter blocks. -/
def counterAssignment
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) :
    Sum (ZMod 11) (ExactCounter 11 7) → Bool
  | Sum.inl membership => assignment (Sum.inl membership)
  | Sum.inr counter => assignment (Sum.inr (Sum.inr counter))

/-- A structural family is a clause set together with the exact intended
pair-and-counter semantics.  Boundary (1) only has to identify the parsed set
with `clauses`; no byte computation occurs here. -/
structure ProductionFamilies117 where
  clauses : CNF 11 187
  pairSat : (Sum (ZMod 11) ProductionAux117 → Bool) → Prop
  clause_semantics : ∀ assignment,
    Satisfies (parserAssignment assignment) clauses ↔
      pairSat assignment ∧ ExactSat 11 7 (counterAssignment assignment)

/-- Clause correspondence, exposed separately so a structural family proof can
be composed without unfolding the byte parser. -/
theorem satisfies_iff_pair_and_exact (families : ProductionFamilies117)
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) :
    Satisfies (parserAssignment assignment) families.clauses ↔
      families.pairSat assignment ∧
        ExactSat 11 7 (counterAssignment assignment) :=
  families.clause_semantics assignment

/-- Exact reduction of the remaining bytes-to-spec goal.  A parse equation, a
cardinality fact, a structural clause-set equality, and the already-proved
family projection fact close `Production117BytesToSpec` in one application. -/
theorem production117BytesToSpec_of_parse_and_families
    {productionBytes : List Char} (families : ProductionFamilies117)
    (parsed : parseDIMACSCharsAux 11 187 productionBytes = some families.clauses)
    (card : families.clauses.card = 482)
    (projects : ProjectsToReference families.clauses (fun membership =>
      BedertLab.EncodeSpec.Satisfies membership
        (BedertLab.EncodeSpec.encode 11 7))) :
    Production117BytesToSpec productionBytes := by
  exact ⟨families.clauses, parsed, card, projects⟩

/-- Swapping offsets 55 and 56 changes the positive table coordinates `(0,0)`
and `(0,1)`. -/
def swappedOffset (offset : Fin 176) : Fin 176 :=
  if offset = 55 then 56 else if offset = 56 then 55 else offset

def indexTamperFiringCount : ℕ :=
  ((Finset.univ.filter fun offset : Fin 176 =>
    auxiliaryAtOffset (swappedOffset offset) ≠ auxiliaryAtOffset offset).card)

theorem swapped_index_map_control : indexTamperFiringCount = 2 := by
  decide

#print axioms PairSlot117
#print axioms ProductionAux117
#print axioms auxiliaryOffset
#print axioms auxiliaryAtOffset
#print axioms auxiliaryAtOffset_leftInverse
#print axioms auxiliaryAtOffset_rightInverse
#print axioms auxiliaryIndexEquiv
#print axioms parserAssignment
#print axioms counterAssignment
#print axioms ProductionFamilies117
#print axioms satisfies_iff_pair_and_exact
#print axioms production117BytesToSpec_of_parse_and_families
#print axioms swappedOffset
#print axioms indexTamperFiringCount
#print axioms swapped_index_map_control

end BedertLab.ClauseCorrespondence
