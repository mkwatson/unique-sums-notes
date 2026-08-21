import BedertLab.ParsePath

/-!
# Resumable state for the frozen DIMACS tokenizer

The frozen tokenizer stores both the current token and the completed-token
accumulator in reverse order.  `ScannerState` exposes exactly those two hidden
accumulators, so scanning can be split at arbitrary byte boundaries without
changing the parser trust boundary.
-/

namespace BedertLab.ScannerState

open BedertLab.ByteBridge
open BedertLab.ByteBridgeAux
open BedertLab.ChainClose

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The two accumulators hidden in `DIMACSParser.tokenize`.  Both fields are
stored in the same reverse orientation as the frozen implementation. -/
structure State where
  currentRev : List Char
  tokensRev : List (List Char)
deriving DecidableEq, Repr

/-- Consume one character, preserving the frozen tokenizer's accumulator
orientation. -/
def step (state : State) (char : Char) : State :=
  if DIMACSParser.isSpace char then
    match state.currentRev with
    | [] => state
    | _ => ⟨[], state.currentRev.reverse :: state.tokensRev⟩
  else
    ⟨char :: state.currentRev, state.tokensRev⟩

/-- Expose finalized tokens in input order. -/
def finish (state : State) : List (List Char) :=
  match state.currentRev with
  | [] => state.tokensRev.reverse
  | _ => (state.currentRev.reverse :: state.tokensRev).reverse

/-- Scan a resumable chunk. -/
def scan (state : State) (input : List Char) : State :=
  input.foldl step state

@[simp] theorem scan_nil (state : State) : scan state [] = state := by
  rfl

theorem scan_append (state : State) (left right : List Char) :
    scan state (left ++ right) = scan (scan state left) right := by
  simp [scan, List.foldl_append]

/-- Principal obligation: the frozen tokenizer is exactly finalization of the
resumable fold, for arbitrary hidden accumulators. -/
theorem tokenize_eq_finish_scan
    (input current : List Char) (tokens : List (List Char)) :
    DIMACSParser.tokenize input current tokens =
      finish (scan ⟨current, tokens⟩ input) := by
  induction input generalizing current tokens with
  | nil =>
      cases current <;> rfl
  | cons char chars ih =>
      rw [scan]
      simp only [List.foldl_cons]
      unfold step
      by_cases space : DIMACSParser.isSpace char = true
      · rw [if_pos space]
        cases current with
        | nil =>
            simpa [DIMACSParser.tokenize, space, scan] using
              (ih ([] : List Char) tokens)
        | cons head tail =>
            simpa [DIMACSParser.tokenize, space, scan] using
              (ih ([] : List Char) ((head :: tail).reverse :: tokens))
      · rw [if_neg space]
        simpa [DIMACSParser.tokenize, space, scan] using
          (ih (char :: current) tokens)

theorem tokenize_eq_finish_scan_empty (input : List Char) :
    DIMACSParser.tokenize input [] [] =
      finish (scan ⟨[], []⟩ input) := by
  exact tokenize_eq_finish_scan input [] []

/-- Clausewise composition interface for any split of an input stream. -/
theorem tokenize_append
    (left right current : List Char) (tokens : List (List Char)) :
    DIMACSParser.tokenize (left ++ right) current tokens =
      finish (scan (scan ⟨current, tokens⟩ left) right) := by
  rw [tokenize_eq_finish_scan, scan_append]

/-- Parsing integer tokens composes across a token-list boundary. -/
theorem parseInts_append (left right : List (List Char)) :
    DIMACSParser.parseInts (left ++ right) = (do
      let leftValues ← DIMACSParser.parseInts left
      let rightValues ← DIMACSParser.parseInts right
      some (leftValues ++ rightValues)) := by
  induction left with
  | nil => simp [DIMACSParser.parseInts]
  | cons token tokens ih =>
      simp only [List.cons_append, DIMACSParser.parseInts]
      rw [ih]
      cases DIMACSParser.parseInt token <;>
        cases DIMACSParser.parseInts tokens <;>
        cases DIMACSParser.parseInts right <;> rfl

/-- The hidden reverse accumulators of `splitClauses`. -/
structure ClauseState where
  currentRev : List Int
  clausesRev : List (List Int)
deriving DecidableEq, Repr

def clauseStep (state : ClauseState) (value : Int) : ClauseState :=
  if value = 0 then
    ⟨[], state.currentRev.reverse :: state.clausesRev⟩
  else
    ⟨value :: state.currentRev, state.clausesRev⟩

def clauseScan (state : ClauseState) (values : List Int) : ClauseState :=
  values.foldl clauseStep state

def clauseFinish (state : ClauseState) : Option (List (List Int)) :=
  match state.currentRev with
  | [] => some state.clausesRev.reverse
  | _ => none

theorem clauseScan_append (state : ClauseState) (left right : List Int) :
    clauseScan state (left ++ right) =
      clauseScan (clauseScan state left) right := by
  simp [clauseScan, List.foldl_append]

/-- The clause splitter is likewise the finalization of a resumable fold. -/
theorem splitClauses_eq_clauseFinish_scan
    (values current : List Int) (clauses : List (List Int)) :
    splitClauses values current clauses =
      clauseFinish (clauseScan ⟨current, clauses⟩ values) := by
  induction values generalizing current clauses with
  | nil =>
      cases current <;> rfl
  | cons value values ih =>
      simp only [clauseScan, List.foldl_cons]
      unfold clauseStep
      by_cases zero : value = 0
      · subst value
        simpa [splitClauses, clauseScan] using
          (ih ([] : List Int) (current.reverse :: clauses))
      · simpa [splitClauses, zero, clauseScan] using
          (ih (value :: current) clauses)

/-- Body parser with the frozen tokenizer replaced by its proved-equal
resumable presentation. -/
def parseBodyStepped (input : List Char) : Option (Nat × List (List Int)) := do
  match finish (scan ⟨[], []⟩ input) with
  | p :: cnf :: variableCount :: clauseCount :: values =>
      if p = ['p'] ∧ cnf = ['c', 'n', 'f'] then
        let variableCount ← DIMACSParser.parseNat variableCount
        let clauseCount ← DIMACSParser.parseNat clauseCount
        let values ← DIMACSParser.parseInts values
        let clauses ← splitClauses values [] []
        if clauses.length = clauseCount then
          some (variableCount, clauses)
        else
          none
      else
        none
  | _ => none

theorem parseBodyChars_eq_stepped (input : List Char) :
    parseBodyChars input = parseBodyStepped input := by
  unfold parseBodyChars parseBodyStepped
  rw [tokenize_eq_finish_scan_empty]
  rfl


#print axioms State
#print axioms step
#print axioms finish
#print axioms scan
#print axioms scan_nil
#print axioms scan_append
#print axioms tokenize_eq_finish_scan
#print axioms tokenize_eq_finish_scan_empty
#print axioms tokenize_append
#print axioms parseInts_append
#print axioms ClauseState
#print axioms clauseStep
#print axioms clauseScan
#print axioms clauseFinish
#print axioms clauseScan_append
#print axioms splitClauses_eq_clauseFinish_scan
#print axioms parseBodyStepped
#print axioms parseBodyChars_eq_stepped

end BedertLab.ScannerState
