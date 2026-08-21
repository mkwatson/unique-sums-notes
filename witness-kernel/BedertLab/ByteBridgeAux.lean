import BedertLab.ByteBridge
import BedertLab.ProjectionTheorem

/-!
# Auxiliary-aware strict DIMACS bridge

This module is additive: `ByteBridge.parseDIMACS` remains the visible-only trust
boundary.  Here the declared total variable count is an explicit parameter and
variables above the visible prefix retain their original DIMACS indices.
-/

namespace BedertLab.ByteBridgeAux

open BedertLab.ByteBridge
open BedertLab.EncodeSpec
open BedertLab.ProjectionTheorem

/-- Auxiliary variables use a zero-based offset from the end of the visible
prefix.  `literalOfInt` is the only constructor used by the parser, and admits
an offset only after checking the original index lies in `n+1..v`. -/
abbrev AuxiliaryIndex (_n _v : ℕ) := ℕ

/-- The visible prefix is mapped exactly as in `ByteBridge.literalOfInt`; the
remaining declared variables form a disjoint auxiliary block. -/
abbrev Variable (n v : ℕ) := Sum (ZMod n) (AuxiliaryIndex n v)

structure Literal (n v : ℕ) where
  index : Variable n v
  positive : Bool
deriving DecidableEq, Repr

abbrev Clause (n v : ℕ) := Finset (Literal n v)
abbrev CNF (n v : ℕ) := Finset (Clause n v)

/-- Convert one nonzero literal in `1..v`, splitting at the visible cutoff `n`. -/
def literalOfInt (n v : ℕ) [NeZero n] (value : Int) : Option (Literal n v) := do
  if value = 0 then none else
  let magnitude := value.natAbs
  if 1 ≤ magnitude ∧ magnitude ≤ v then
    if magnitude ≤ n then
      some ⟨Sum.inl ((magnitude - 1 : ℕ) : ZMod n), decide (0 < value)⟩
    else
      some ⟨Sum.inr (magnitude - n - 1),
        decide (0 < value)⟩
  else
    none

/-- Convert a clause while refusing repeated signed literals. -/
def clauseOfArray (n v : ℕ) [NeZero n]
    (values : Array Int) : Option (Clause n v) := do
  let literals ← values.toList.mapM (literalOfInt n v)
  if literals.Nodup then some literals.toFinset else none

/-- Strict conversion with an exact total-variable header, in-range literals,
and no duplicate clauses.  The visible cutoff may not exceed the header. -/
def rawToCNF (n v : ℕ) [NeZero n] (raw : RawDIMACS) : Option (CNF n v) := do
  if n > v then none else
  if raw.variableCount ≠ v then none else
  let clauses ← raw.clauses.toList.mapM (clauseOfArray n v)
  if clauses.Nodup then some clauses.toFinset else none

/-- Kernel-reducible DIMACS front end over the character bytes themselves. -/
def parseBodyChars (input : List Char) : Option (ℕ × List (List Int)) := do
  match ByteBridge.DIMACSParser.tokenize input [] [] with
  | p :: cnf :: variableCount :: clauseCount :: values =>
      if p = ['p'] ∧ cnf = ['c', 'n', 'f'] then
        let variableCount ← ByteBridge.DIMACSParser.parseNat variableCount
        let clauseCount ← ByteBridge.DIMACSParser.parseNat clauseCount
        let values ← ByteBridge.DIMACSParser.parseInts values
        let clauses ← splitClauses values [] []
        if clauses.length = clauseCount then
          some (variableCount, clauses)
        else
          none
      else
        none
  | _ => none

/-- Raw array wrapper matching the unchanged `ByteBridge.RawDIMACS` boundary. -/
def parseRawChars (input : List Char) : Option RawDIMACS := do
  let (variableCount, clauses) ← parseBodyChars input
  some ⟨variableCount, clauses.toArray.map List.toArray⟩

/-- Auxiliary-aware parser whose input is the literal DIMACS character stream. -/
def parseDIMACSCharsAux (n v : ℕ) [NeZero n]
    (input : List Char) : Option (CNF n v) := do
  rawToCNF n v (← parseRawChars input)

/-- Auxiliary-aware total parser.  Header/body consistency remains delegated to
the unchanged strict `ByteBridge.parseRaw`. -/
def parseDIMACSAux (n v : ℕ) [NeZero n] (input : String) : Option (CNF n v) := do
  rawToCNF n v (← parseRaw input)

def evalLiteral {n v : ℕ} [NeZero n]
    (assignment : Variable n v → Bool) (literal : Literal n v) : Bool :=
  assignment literal.index == literal.positive

def Satisfies {n v : ℕ} [NeZero n]
    (assignment : Variable n v → Bool) (cnf : CNF n v) : Prop :=
  ∀ clause ∈ cnf, ∃ literal ∈ clause, evalLiteral assignment literal = true

/-- The exact semantic shape consumed by the generic existential-projection API. -/
def ProjectsToReference {n v : ℕ} [NeZero n]
    (cnf : CNF n v) (reference : (ZMod n → Bool) → Prop) : Prop :=
  ProjectsTo (fun assignment => Satisfies assignment cnf) reference

theorem auxiliary_raw_accepted :
    (rawToCNF 3 5 ⟨5, #[#[1, -5]]⟩).isSome = true := by
  decide

theorem visible_cutoff_above_header_refused :
    parseDIMACSAux 5 3 "p cnf 3 1\n1 0\n" = none := by
  decide

theorem wrong_header_count_refused :
    parseDIMACSAux 3 5 "p cnf 4 1\n1 0\n" = none := by
  decide

theorem auxiliary_out_of_range_refused :
    rawToCNF 3 5 ⟨5, #[#[6]]⟩ = none := by
  decide

theorem auxiliary_duplicate_literal_refused :
    rawToCNF 3 5 ⟨5, #[#[4, 4]]⟩ = none := by
  decide

theorem clause_count_refused :
    parseDIMACSAux 3 5 "p cnf 5 2\n1 0\n" = none := by
  decide

/-- Byte-level auxiliary tamper control: changing the single auxiliary digit
`4` to `5` changes the parsed literal stream.  Exactly one flipped literal fires. -/
theorem auxiliary_literal_tamper_fires :
    parseBodyChars
        ['p', ' ', 'c', 'n', 'f', ' ', '5', ' ', '1', '\n',
          '1', ' ', '-', '4', ' ', '0', '\n'] ≠
      parseBodyChars
        ['p', ' ', 'c', 'n', 'f', ' ', '5', ' ', '1', '\n',
          '1', ' ', '-', '5', ' ', '0', '\n'] := by
  decide

/-- Instance-level bytes-to-spec target for the measured production header.
Supplying the literal production bytes and the sibling counter theorem reduces
the remaining work to proving this proposition for the parsed term. -/
def Production117BytesToSpec (productionBytes : List Char) : Prop :=
  ∃ cnf,
    parseDIMACSCharsAux 11 187 productionBytes = some cnf ∧
    cnf.card = 482 ∧
    ProjectsToReference cnf (fun membership =>
      BedertLab.EncodeSpec.Satisfies membership
        (BedertLab.EncodeSpec.encode 11 7))

/-- Once `Production117BytesToSpec` is discharged using the pair projection
theorem and the sibling `ExactCorrect 11 7`, it composes directly with the
frozen reference theorem. -/
theorem production117_composes {productionBytes : List Char}
    (correct : Production117BytesToSpec productionBytes) :
    ∃ cnf,
      parseDIMACSCharsAux 11 187 productionBytes = some cnf ∧
      cnf.card = 482 ∧
      ∀ membership,
        (∃ auxiliary, Satisfies (combine membership auxiliary) cnf) ↔
          BedertLab.EncodeSpec.Target 7
            (BedertLab.EncodeSpec.decode membership) := by
  obtain ⟨cnf, parsed, card, projected⟩ := correct
  refine ⟨cnf, parsed, card, ?_⟩
  intro membership
  rw [projected membership]
  exact BedertLab.EncodeSpec.satisfies_encode_iff membership

#print axioms AuxiliaryIndex
#print axioms Variable
#print axioms Literal
#print axioms Clause
#print axioms CNF
#print axioms literalOfInt
#print axioms clauseOfArray
#print axioms rawToCNF
#print axioms parseBodyChars
#print axioms parseRawChars
#print axioms parseDIMACSCharsAux
#print axioms parseDIMACSAux
#print axioms evalLiteral
#print axioms Satisfies
#print axioms ProjectsToReference
#print axioms auxiliary_raw_accepted
#print axioms visible_cutoff_above_header_refused
#print axioms wrong_header_count_refused
#print axioms auxiliary_out_of_range_refused
#print axioms auxiliary_duplicate_literal_refused
#print axioms clause_count_refused
#print axioms auxiliary_literal_tamper_fires
#print axioms Production117BytesToSpec
#print axioms production117_composes

end BedertLab.ByteBridgeAux
