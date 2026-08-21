import BedertLab.FamilyCertificate

/-!
# Completion of the production `(11, 7)` clause-family certificate

This module is additive.  Every imported production boundary remains frozen.
-/

namespace BedertLab.FamilyCertificateTwo

open BedertLab.ByteBridgeAux
open BedertLab.ClauseCorrespondence
open BedertLab.FamilyCertificate
open BedertLab.ProjectionTheorem
open BedertLab.SequentialCounter

set_option maxRecDepth 20000

def counterLiteral (counter : ExactCounter 11 7) (positive : Bool) : Literal 11 187 :=
  ⟨Sum.inr (auxiliaryOffset (Sum.inr counter)).val, positive⟩

theorem parserAssignment_counter
    (assignment : Sum (ZMod 11) ProductionAux117 → Bool)
    (counter : ExactCounter 11 7) :
    parserAssignment assignment
        (Sum.inr (auxiliaryOffset (Sum.inr counter)).val) =
      assignment (Sum.inr (Sum.inr counter)) := by
  unfold parserAssignment
  change (if h : (auxiliaryOffset (Sum.inr counter)).val < 176 then
      assignment (Sum.inr (auxiliaryAtOffset
        ⟨(auxiliaryOffset (Sum.inr counter)).val, h⟩)) else false) = _
  rw [dif_pos (by have := (auxiliaryOffset (Sum.inr counter)).isLt; omega)]
  simpa using congrArg assignment
    (congrArg Sum.inr (auxiliaryAtOffset_leftInverse (Sum.inr counter)))

def inputLiteral (negative : Bool) (i : Fin 11) (positive : Bool) : Literal 11 187 :=
  membershipLiteral i (if negative then !positive else positive)

def signalLiteral (negative : Bool) (i : Fin 11)
    (j : Fin (if negative then 4 else 7)) (positive : Bool) : Literal 11 187 := by
  cases negative
  · exact counterLiteral (Sum.inl (i, j)) positive
  · exact counterLiteral (Sum.inr (i, j)) positive

def sinzInitial (negative : Bool) : Clause 11 187 :=
  {inputLiteral negative 0 false, signalLiteral negative 0 0 true}

def sinzInitialUnits (negative : Bool) : CNF 11 187 :=
  (Finset.univ.filter fun j : Fin (if negative then 4 else 7) => 0 < j.val).image
    fun j => {signalLiteral negative 0 j false}

def sinzColumnZero (negative : Bool) : CNF 11 187 :=
  (Finset.univ.filter fun i : Fin 11 => 0 < i.val).biUnion fun i =>
    {{inputLiteral negative i false, signalLiteral negative i 0 true},
     {signalLiteral negative ⟨i.val - 1, by omega⟩ 0 false,
       signalLiteral negative i 0 true}}

def sinzMiddle (negative : Bool) : CNF 11 187 :=
  (Finset.univ.filter fun i : Fin 11 => 0 < i.val).biUnion fun i =>
    (Finset.univ.filter fun j : Fin (if negative then 4 else 7) => 0 < j.val).biUnion
      fun j =>
        {{inputLiteral negative i false,
            signalLiteral negative ⟨i.val - 1, by omega⟩
              ⟨j.val - 1, by omega⟩ false,
            signalLiteral negative i j true},
         {signalLiteral negative ⟨i.val - 1, by omega⟩ j false,
            signalLiteral negative i j true}}

def sinzOverflow (negative : Bool) : CNF 11 187 :=
  (Finset.univ.filter fun i : Fin 11 => 0 < i.val).image fun i =>
    {inputLiteral negative i false,
      signalLiteral negative ⟨i.val - 1, by omega⟩
        ⟨(if negative then 3 else 6), by split <;> omega⟩ false}

def sinzClauses (negative : Bool) : CNF 11 187 :=
  insert (sinzInitial negative)
    (sinzInitialUnits negative ∪ sinzColumnZero negative ∪
      sinzMiddle negative ∪ sinzOverflow negative)

theorem positiveSinz_card : (sinzClauses false).card = 157 := by
  decide +kernel

theorem negativeSinz_card : (sinzClauses true).card = 94 := by
  decide +kernel

def pairSlotsForSum (s : ZMod 11) : Finset PairSlot117 :=
  Finset.univ.filter fun slot => pairLeft slot + pairRight slot = s

def half (s : ZMod 11) : ZMod 11 := s * 6

def usfDiagonalClause (s : ZMod 11) : Clause 11 187 :=
  insert (membershipLiteral (half s) false)
    ((pairSlotsForSum s).image fun slot => pairLiteral slot true)

def usfPairClause (s : ZMod 11) (slot : PairSlot117) : Clause 11 187 :=
  insert (membershipLiteral (half s) true)
    (insert (pairLiteral slot false)
      (((pairSlotsForSum s).erase slot).image fun other => pairLiteral other true))

def usfClauses : CNF 11 187 :=
  Finset.univ.biUnion fun s : ZMod 11 =>
    insert (usfDiagonalClause s)
      ((pairSlotsForSum s).image fun slot => usfPairClause s slot)

theorem pairSlotsForSum_card (s : ZMod 11) : (pairSlotsForSum s).card = 5 := by
  fin_cases s <;> decide +kernel

theorem usfClauses_card : usfClauses.card = 66 := by
  decide +kernel

def productionClauses : CNF 11 187 :=
  pairClauses ∪ usfClauses ∪ sinzClauses false ∪ sinzClauses true

def tamperedUsfClauses : CNF 11 187 :=
  usfClauses.erase (usfDiagonalClause 0)

theorem usf_tamper_firing_count :
    usfClauses.card - tamperedUsfClauses.card = 1 := by
  decide +kernel

#print axioms counterLiteral
#print axioms parserAssignment_counter
#print axioms inputLiteral
#print axioms signalLiteral
#print axioms sinzClauses
#print axioms positiveSinz_card
#print axioms negativeSinz_card
#print axioms pairSlotsForSum
#print axioms half
#print axioms usfClauses
#print axioms pairSlotsForSum_card
#print axioms usfClauses_card
#print axioms productionClauses
#print axioms tamperedUsfClauses
#print axioms usf_tamper_firing_count

end BedertLab.FamilyCertificateTwo
