import BedertLab.ClauseCorrespondence

/-!
# Structural family certificate for the production `(11, 7)` encoder

This additive module reconstructs frozen encoder schemas.  The pair-definition
block is certified first; later blocks can be unioned with it without changing
the frozen bridge modules.
-/

namespace BedertLab.FamilyCertificate

open BedertLab.ByteBridgeAux
open BedertLab.ClauseCorrespondence
open BedertLab.ProjectionTheorem

set_option maxRecDepth 10000

/-- Pair endpoints in the encoder's sum-fibre order, then Python encounter
order within each fibre (`usf_encode.py`, `encode`, lines 73--93). -/
def pairEndpointNats : Array (ℕ × ℕ) := #[
  (1, 10), (2, 9), (3, 8), (4, 7), (5, 6),
  (0, 1), (2, 10), (3, 9), (4, 8), (5, 7),
  (0, 2), (3, 10), (4, 9), (5, 8), (6, 7),
  (0, 3), (1, 2), (4, 10), (5, 9), (6, 8),
  (0, 4), (1, 3), (5, 10), (6, 9), (7, 8),
  (0, 5), (1, 4), (2, 3), (6, 10), (7, 9),
  (0, 6), (1, 5), (2, 4), (7, 10), (8, 9),
  (0, 7), (1, 6), (2, 5), (3, 4), (8, 10),
  (0, 8), (1, 7), (2, 6), (3, 5), (9, 10),
  (0, 9), (1, 8), (2, 7), (3, 6), (4, 5),
  (0, 10), (1, 9), (2, 8), (3, 7), (4, 6)]

theorem pairEndpointNats_size : pairEndpointNats.size = 55 := by
  rfl

def pairEndpoints (slot : PairSlot117) : Fin 11 × Fin 11 :=
  let endpoints := pairEndpointNats[slot.val]'(by
    rw [pairEndpointNats_size]
    exact slot.isLt)
  (⟨endpoints.1, by
      fin_cases slot <;> decide⟩,
   ⟨endpoints.2, by
      fin_cases slot <;> decide⟩)

def pairLeft (slot : PairSlot117) : ZMod 11 := pairEndpoints slot |>.1.val

def pairRight (slot : PairSlot117) : ZMod 11 := pairEndpoints slot |>.2.val

def pairEndpoint (slot : PairSlot117) : ProductionPairVariable 11 :=
  ⟨(pairLeft slot, pairRight slot), by
    fin_cases slot <;> decide⟩

theorem pairEndpoint_bijective : Function.Bijective pairEndpoint := by
  decide +kernel

/-- The 55 allocation slots are exactly the canonical production pairs. -/
noncomputable def pairSlotEquiv : PairSlot117 ≃ ProductionPairVariable 11 :=
  Equiv.ofBijective pairEndpoint pairEndpoint_bijective

def membershipLiteral (x : ZMod 11) (positive : Bool) : Literal 11 187 :=
  ⟨Sum.inl x, positive⟩

def pairLiteral (slot : PairSlot117) (positive : Bool) : Literal 11 187 :=
  ⟨Sum.inr slot.val, positive⟩

/-- The three Tseitin clauses for `y_slot ↔ (x_left ∧ x_right)`. -/
def pairClause (slot : PairSlot117) : Fin 3 → Clause 11 187
  | 0 => {pairLiteral slot false, membershipLiteral (pairLeft slot) true}
  | 1 => {pairLiteral slot false, membershipLiteral (pairRight slot) true}
  | 2 => {membershipLiteral (pairLeft slot) false,
      membershipLiteral (pairRight slot) false, pairLiteral slot true}

def pairClauses : CNF 11 187 :=
  Finset.univ.biUnion fun slot : PairSlot117 =>
    Finset.univ.image (pairClause slot)

theorem parserAssignment_membership
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) (x : ZMod 11) :
    parserAssignment assignment (Sum.inl x) = assignment (Sum.inl x) := rfl

theorem parserAssignment_pair
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) (slot : PairSlot117) :
    parserAssignment assignment (Sum.inr slot.val) =
      assignment (Sum.inr (Sum.inl slot)) := by
  unfold parserAssignment
  change (if h : slot.val < 176 then
      assignment (Sum.inr (auxiliaryAtOffset ⟨slot.val, h⟩)) else false) = _
  rw [dif_pos (by omega)]
  have hinverse := auxiliaryAtOffset_leftInverse (Sum.inl slot)
  simpa [auxiliaryOffset] using congrArg assignment (congrArg Sum.inr hinverse)

def ClauseSatisfied
    (assignment : Variable 11 187 → Bool) (clause : Clause 11 187) : Prop :=
  ∃ literal ∈ clause, evalLiteral assignment literal = true

theorem pairClause_all_iff
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool)
    (slot : PairSlot117) :
    (∀ tag : Fin 3,
      ClauseSatisfied (parserAssignment assignment) (pairClause slot tag)) ↔
      assignment (Sum.inr (Sum.inl slot)) =
        (assignment (Sum.inl (pairLeft slot)) &&
          assignment (Sum.inl (pairRight slot))) := by
  cases tag : assignment (Sum.inr (Sum.inl slot)) <;>
    cases left : assignment (Sum.inl (pairLeft slot)) <;>
    cases right : assignment (Sum.inl (pairRight slot)) <;>
    simp [ClauseSatisfied, pairClause, pairLiteral, membershipLiteral, evalLiteral,
      parserAssignment_membership, parserAssignment_pair, tag, left, right,
      Fin.forall_fin_succ]

def PairSat117
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) : Prop :=
  ∀ slot, assignment (Sum.inr (Sum.inl slot)) =
    (assignment (Sum.inl (pairLeft slot)) &&
      assignment (Sum.inl (pairRight slot)))

theorem satisfies_pairClauses_iff
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool) :
    Satisfies (parserAssignment assignment) pairClauses ↔
      PairSat117 assignment := by
  rw [PairSat117]
  constructor
  · intro hs slot
    apply (pairClause_all_iff assignment slot).mp
    intro tag
    apply hs (pairClause slot tag)
    simp [pairClauses]
  · intro hp clause hclause
    simp only [pairClauses, Finset.mem_biUnion] at hclause
    obtain ⟨slot, _, hclause⟩ := hclause
    simp only [Finset.mem_image] at hclause
    obtain ⟨tag, _, rfl⟩ := hclause
    exact (pairClause_all_iff assignment slot).mpr (hp slot) tag

theorem pairClauses_card : pairClauses.card = 165 := by
  decide +kernel

/-- A concrete duplicate-collapse guard for the whole pair block, rather than
three independent per-schema counts. -/
theorem pairClauses_no_duplicate_collapse :
    pairClauses.card = 55 * 3 := by
  decide +kernel

def pairTamperedClauses : CNF 11 187 :=
  pairClauses.erase (pairClause 0 0)

theorem pair_tamper_firing_count :
    pairClauses.card - pairTamperedClauses.card = 1 := by
  decide +kernel

#print axioms pairEndpointNats
#print axioms pairEndpointNats_size
#print axioms pairEndpoints
#print axioms pairLeft
#print axioms pairRight
#print axioms pairEndpoint
#print axioms pairEndpoint_bijective
#print axioms pairSlotEquiv
#print axioms membershipLiteral
#print axioms pairLiteral
#print axioms pairClause
#print axioms pairClauses
#print axioms parserAssignment_membership
#print axioms parserAssignment_pair
#print axioms ClauseSatisfied
#print axioms pairClause_all_iff
#print axioms PairSat117
#print axioms satisfies_pairClauses_iff
#print axioms pairClauses_card
#print axioms pairClauses_no_duplicate_collapse
#print axioms pairTamperedClauses
#print axioms pair_tamper_firing_count

end BedertLab.FamilyCertificate
