import BedertLab.ByteBridge
import BedertLab.EncodeGenWitness

/-!
# Controls for the predicate-polymorphic encoding layer

The controls use the noncyclic Klein four group and an arbitrary decidable
predicate on its subsets.  The strict DIMACS tokenizer and raw parser are the
existing frozen byte front end; only the conversion from numbered variables to
the generalized literal type is new here.
-/

namespace BedertLab.EncodeGenControls

open BedertLab.EncodeGen
open BedertLab.EncodeGenWitness

set_option maxRecDepth 100000

/-- A duplicate-free DIMACS variable order covering the whole finite group. -/
structure Numbering (G : Type*) [Fintype G] [DecidableEq G] where
  values : Array G
  nodup : values.toList.Nodup
  complete : values.toList.toFinset = Finset.univ

/-- List-based strict DIMACS data, chosen so finite controls reduce in the kernel. -/
structure RawDIMACS where
  variableCount : Nat
  clauses : List (List Int)
deriving DecidableEq, Repr

/-- Decimal character spelling of a signed DIMACS integer. -/
def renderInt : Int → List Char
  | Int.ofNat value => Nat.toDigits 10 value
  | Int.negSucc value => '-' :: Nat.toDigits 10 (value + 1)

/-- Render one zero-terminated DIMACS clause. -/
def renderClause (clause : List Int) : List Char :=
  List.intercalate [' '] (clause.map renderInt ++ [['0']]) ++ ['\n']

/-- Render the list-based raw structure as a complete DIMACS character stream. -/
def renderDIMACSChars (raw : RawDIMACS) : List Char :=
  ['p', ' ', 'c', 'n', 'f', ' '] ++ Nat.toDigits 10 raw.variableCount ++ [' '] ++
    Nat.toDigits 10 raw.clauses.length ++ ['\n'] ++ (raw.clauses.map renderClause).flatten

/-- Convert a one-based signed DIMACS integer using an explicit variable order. -/
def literalOfInt {G : Type*} (numbering : Array G) (value : Int) : Option (Literal G) := do
  if value = 0 then none else
  let magnitude := value.natAbs
  let element ← numbering[magnitude - 1]?
  some ⟨element, decide (0 < value)⟩

/-- Convert one raw DIMACS clause, refusing duplicate generalized literals. -/
def clauseListOfInts {G : Type*} [DecidableEq G]
    (numbering : Array G) (values : List Int) : Option (List (Literal G)) := do
  let literals ← values.mapM (literalOfInt numbering)
  if literals.Nodup then some literals else none

/-- Array-valued wrapper for compatibility with the frozen raw parser. -/
def clauseListOfArray {G : Type*} [DecidableEq G]
    (numbering : Array G) (values : Array Int) : Option (List (Literal G)) :=
  clauseListOfInts numbering values.toList

/-- Finset-valued wrapper around the checked ordered clause stage. -/
def clauseOfArray {G : Type*} [DecidableEq G]
    (numbering : Array G) (values : Array Int) : Option (Clause G) := do
  some (← clauseListOfArray numbering values).toFinset

/-- Convert the frozen array boundary to the list-based reducible boundary. -/
def ofByteBridgeRaw (raw : BedertLab.ByteBridge.RawDIMACS) : RawDIMACS :=
  ⟨raw.variableCount, raw.clauses.toList.map Array.toList⟩

/-- Convert strict raw DIMACS into duplicate-free ordered generalized clauses. -/
def rawToClauseLists (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (numbering : Numbering G) (raw : RawDIMACS) :
    Option (List (List (Literal G))) := do
  if raw.variableCount ≠ numbering.values.size then none else
  let clauses ← raw.clauses.mapM (clauseListOfInts numbering.values)
  if clauses.Nodup then some clauses else none

/-- Convert strict raw DIMACS into a generalized CNF.

The explicit variable array must be a duplicate-free enumeration of the whole
group, and the DIMACS header must declare exactly that many variables.
-/
def rawToCNF (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (numbering : Numbering G) (raw : RawDIMACS) : Option (CNF G) := do
  let clauses ← rawToClauseLists G numbering raw
  some (clauses.map List.toFinset).toFinset

/-- Kernel-reducible strict DIMACS front end over the character stream. -/
def parseRawChars (input : List Char) : Option RawDIMACS :=
  match BedertLab.ByteBridge.DIMACSParser.tokenize input [] [] with
  | p :: cnf :: variableCount :: clauseCount :: values => do
      if p = ['p'] ∧ cnf = ['c', 'n', 'f'] then
        let parsedVariableCount ← BedertLab.ByteBridge.DIMACSParser.parseNat variableCount
        let parsedClauseCount ← BedertLab.ByteBridge.DIMACSParser.parseNat clauseCount
        let parsedValues ← BedertLab.ByteBridge.DIMACSParser.parseInts values
        let clauses ← BedertLab.ByteBridge.splitClauses parsedValues [] []
        if clauses.length = parsedClauseCount then
          some ⟨parsedVariableCount, clauses⟩
        else
          none
      else
        none
  | _ => none

/-- Character-stream parser retaining clause and literal order. -/
def parseDIMACSClauseListsChars (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (numbering : Numbering G) (input : List Char) : Option (List (List (Literal G))) :=
  match parseRawChars input with
  | none => none
  | some raw => rawToClauseLists G numbering raw

/-- Character-stream parser into the generalized CNF representation. -/
def parseDIMACSChars (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (numbering : Numbering G) (input : List Char) : Option (CNF G) := do
  let clauses ← parseDIMACSClauseListsChars G numbering input
  some (clauses.map List.toFinset).toFinset

/-- Strict DIMACS parser retaining clause and literal order for exact controls. -/
def parseDIMACSClauseLists (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (numbering : Numbering G) (input : String) : Option (List (List (Literal G))) :=
  match BedertLab.ByteBridge.parseRaw input with
  | none => none
  | some raw => rawToClauseLists G numbering (ofByteBridgeRaw raw)

/-- Strict DIMACS parser for membership variables indexed by an arbitrary
finite abelian group. -/
def parseDIMACS (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (numbering : Numbering G) (input : String) : Option (CNF G) := do
  let clauses ← parseDIMACSClauseLists G numbering input
  some (clauses.map List.toFinset).toFinset

/-- Deliberately wrong clause polarity, used only as a firing mutation. -/
def flippedBlockingClause (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (subset : Finset G) : Clause G :=
  Finset.univ.image fun element => ⟨element, decide (element ∈ subset)⟩

/-- Deliberately wrong exponential encoder, used only as a firing mutation. -/
def flippedEncode (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (predicate : Finset G → Prop) [DecidablePred predicate] : CNF G :=
  ((Finset.univ : Finset (Finset G)).filter fun subset => ¬ predicate subset).image
    (flippedBlockingClause G)

/-- The noncyclic finite abelian group used by every finite control. -/
abbrev KleinFour := ZMod 2 × ZMod 2

/-- Explicit DIMACS numbering for the Klein four group. -/
def kleinNumbering : Numbering KleinFour where
  values := #[(0, 0), (1, 0), (0, 1), (1, 1)]
  nodup := by decide
  complete := by decide

/-- An arbitrary decidable predicate: two elements, one of which is zero. -/
def anchoredPair (subset : Finset KleinFour) : Prop :=
  subset.card = 2 ∧ (0, 0) ∈ subset

instance anchoredPairDecidable (subset : Finset KleinFour) : Decidable (anchoredPair subset) := by
  unfold anchoredPair
  infer_instance

/-- Cardinality-off-by-one mutation of `anchoredPair`. -/
def anchoredSingleton (subset : Finset KleinFour) : Prop :=
  subset.card = 1 ∧ (0, 0) ∈ subset

instance anchoredSingletonDecidable (subset : Finset KleinFour) :
    Decidable (anchoredSingleton subset) := by
  unfold anchoredSingleton
  infer_instance

def validPair : Finset KleinFour := {(0, 0), (1, 0)}
def anchorSingleton : Finset KleinFour := {(0, 0)}
def nonAnchorPair : Finset KleinFour := {(1, 0), (0, 1)}

def assignmentOf {G : Type*} [DecidableEq G] (subset : Finset G) : G → Bool :=
  fun element => decide (element ∈ subset)

/-- The generalized witness kernel accepts a valid noncyclic-group fixture. -/
theorem witness_positive_control :
    checkWitness KleinFour anchoredPair validPair = true := by
  decide

/-- Mutation 1 fires: the cardinality-off-by-one predicate accepts a witness
which the intended predicate rejects. -/
theorem cardinality_mutation_fires :
    checkWitness KleinFour anchoredPair anchorSingleton = false ∧
      checkWitness KleinFour anchoredSingleton anchorSingleton = true := by
  decide

/-- Mutation 2 fires: deleting the clause for the empty bad subset creates a
false satisfying assignment. -/
theorem omitted_blocking_clause_mutation_fires :
    ¬ Satisfies (assignmentOf (∅ : Finset KleinFour))
        (encode KleinFour anchoredPair) ∧
      Satisfies (assignmentOf (∅ : Finset KleinFour))
        ((encode KleinFour anchoredPair).erase
          (blockingClause KleinFour (∅ : Finset KleinFour))) := by
  decide

/-- Mutation 3 fires: reversing every blocking-clause polarity accepts a bad
two-element subset whose complement satisfies the intended predicate. -/
theorem polarity_mutation_fires :
    ¬ Satisfies (assignmentOf nonAnchorPair) (encode KleinFour anchoredPair) ∧
      Satisfies (assignmentOf nonAnchorPair) (flippedEncode KleinFour anchoredPair) := by
  decide

/-- Ordered clauses used by the strict DIMACS round-trip control. -/
def kleinFixtureClauseLists : List (List (Literal KleinFour)) :=
  [
    [⟨(0, 0), true⟩, ⟨(1, 0), false⟩],
    [⟨(0, 1), false⟩, ⟨(1, 1), true⟩]
  ]

/-- The generalized CNF represented by `kleinFixtureClauseLists`. -/
def kleinFixtureCNF : CNF KleinFour :=
  (kleinFixtureClauseLists.map List.toFinset).toFinset

/-- Exact DIMACS bytes for `kleinFixtureCNF` under `kleinNumbering`. -/
def kleinFixtureDIMACS : String :=
  "p cnf 4 2\n1 -2 0\n-3 4 0\n"

/-- Literal character stream of `kleinFixtureDIMACS`, kept explicit for kernel reduction. -/
def kleinFixtureDIMACSChars : List Char :=
  ['p', ' ', 'c', 'n', 'f', ' ', '4', ' ', '2', '\n',
   '1', ' ', '-', '2', ' ', '0', '\n', '-', '3', ' ', '4', ' ', '0', '\n']

/-- Raw strict-DIMACS value represented by `kleinFixtureDIMACSChars`. -/
def kleinFixtureRaw : RawDIMACS :=
  ⟨4, [[1, -2], [-3, 4]]⟩

/-- The literal character stream reaches the intended strict raw DIMACS value. -/
theorem klein_dimacs_chars_to_raw_control :
    parseRawChars kleinFixtureDIMACSChars = some kleinFixtureRaw := by
  decide

/-- The generalized raw serializer emits the expected literal DIMACS stream. -/
theorem klein_dimacs_render_control :
    renderDIMACSChars kleinFixtureRaw = kleinFixtureDIMACSChars := by
  decide

/-- The strict raw value maps exactly to the intended generalized clauses. -/
theorem klein_raw_to_clause_lists_control :
    rawToClauseLists KleinFour kleinNumbering kleinFixtureRaw =
      some kleinFixtureClauseLists := by
  decide

/-- Exact byte-to-ordered-clause control on a noncyclic finite abelian group. -/
theorem klein_dimacs_clause_round_trip_control :
    parseDIMACSClauseListsChars KleinFour kleinNumbering kleinFixtureDIMACSChars =
      some kleinFixtureClauseLists := by
  simp [parseDIMACSClauseListsChars, klein_dimacs_chars_to_raw_control,
    klein_raw_to_clause_lists_control]

/-- Exact strict DIMACS-to-generalized-CNF round-trip control. -/
theorem klein_dimacs_round_trip_control :
    parseDIMACSChars KleinFour kleinNumbering (renderDIMACSChars kleinFixtureRaw) =
      some kleinFixtureCNF := by
  simp [klein_dimacs_render_control, parseDIMACSChars,
    klein_dimacs_clause_round_trip_control, kleinFixtureCNF]

/-- Mutation 4 fires: changing one literal index changes the parsed generalized CNF. -/
theorem dimacs_literal_mutation_fires :
    parseDIMACSClauseListsChars KleinFour kleinNumbering
      ['p', ' ', 'c', 'n', 'f', ' ', '4', ' ', '2', '\n',
       '1', ' ', '-', '3', ' ', '0', '\n', '-', '3', ' ', '4', ' ', '0', '\n'] ≠
      some kleinFixtureClauseLists := by
  decide

/-- Mutation 5 fires: corrupting the DIMACS header is rejected. -/
theorem dimacs_header_mutation_fires :
    parseDIMACSClauseLists KleinFour kleinNumbering "p cxf 4 2\n1 -2 0\n-3 4 0\n" =
      none := by
  decide

#print axioms literalOfInt
#print axioms Numbering
#print axioms RawDIMACS
#print axioms renderInt
#print axioms renderClause
#print axioms renderDIMACSChars
#print axioms clauseListOfInts
#print axioms clauseListOfArray
#print axioms clauseOfArray
#print axioms ofByteBridgeRaw
#print axioms rawToClauseLists
#print axioms rawToCNF
#print axioms parseRawChars
#print axioms parseDIMACSClauseListsChars
#print axioms parseDIMACSChars
#print axioms parseDIMACSClauseLists
#print axioms parseDIMACS
#print axioms flippedBlockingClause
#print axioms flippedEncode
#print axioms KleinFour
#print axioms kleinNumbering
#print axioms anchoredPair
#print axioms anchoredPairDecidable
#print axioms anchoredSingleton
#print axioms anchoredSingletonDecidable
#print axioms validPair
#print axioms anchorSingleton
#print axioms nonAnchorPair
#print axioms assignmentOf
#print axioms witness_positive_control
#print axioms cardinality_mutation_fires
#print axioms omitted_blocking_clause_mutation_fires
#print axioms polarity_mutation_fires
#print axioms kleinFixtureClauseLists
#print axioms kleinFixtureCNF
#print axioms kleinFixtureDIMACS
#print axioms kleinFixtureDIMACSChars
#print axioms kleinFixtureRaw
#print axioms klein_dimacs_chars_to_raw_control
#print axioms klein_dimacs_render_control
#print axioms klein_raw_to_clause_lists_control
#print axioms klein_dimacs_clause_round_trip_control
#print axioms klein_dimacs_round_trip_control
#print axioms dimacs_literal_mutation_fires
#print axioms dimacs_header_mutation_fires

end BedertLab.EncodeGenControls
