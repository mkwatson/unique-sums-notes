import BedertLab.EncodeSpec

/-!
# Strict DIMACS-to-EncodeSpec bridge

This module deliberately accepts only DIMACS files whose declared variables are
exactly the membership variables of `ZMod n`.  Production encodings with Tseitin
variables are refused rather than silently reducing their indices modulo `n`.
-/

namespace BedertLab.ByteBridge

open BedertLab.EncodeSpec
open Lean

namespace DIMACSParser

def isSpace : Char → Bool
  | ' ' | '\n' | '\r' | '\t' => true
  | _ => false

def tokenize : List Char → List Char → List (List Char) → List (List Char)
  | [], [], tokens => tokens.reverse
  | [], current, tokens => (current.reverse :: tokens).reverse
  | char :: chars, current, tokens =>
      if isSpace char then
        match current with
        | [] => tokenize chars [] tokens
        | _ => tokenize chars [] (current.reverse :: tokens)
      else
        tokenize chars (char :: current) tokens

def digit? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

def parseNatAux : List Char → Nat → Option Nat
  | [], value => some value
  | char :: chars, value => do parseNatAux chars (10 * value + (← digit? char))

def parseNat : List Char → Option Nat
  | [] => none
  | chars => parseNatAux chars 0

def parseInt : List Char → Option Int
  | [] => none
  | '-' :: [] => none
  | '-' :: chars => return -(Int.ofNat (← parseNat chars))
  | chars => return Int.ofNat (← parseNat chars)

def parseInts : List (List Char) → Option (List Int)
  | [] => some []
  | token :: tokens => return (← parseInt token) :: (← parseInts tokens)

def parseFile (input : String) : Option (Nat × Nat × List Int) := do
  match tokenize input.toList [] [] with
  | p :: cnf :: variableCount :: clauseCount :: values =>
      if p = "p".toList ∧ cnf = "cnf".toList then
        return (← parseNat variableCount, ← parseNat clauseCount, ← parseInts values)
      else none
  | _ => none

end DIMACSParser

/-- Split the flat literal stream at zero terminators, refusing an unterminated
final clause. Empty clauses are valid DIMACS clauses. -/
def splitClauses : List Int → List Int → List (List Int) → Option (List (List Int))
  | [], [], clauses => some clauses.reverse
  | [], _ :: _, _ => none
  | 0 :: values, current, clauses => splitClauses values [] (current.reverse :: clauses)
  | value :: values, current, clauses => splitClauses values (value :: current) clauses

/-- Raw DIMACS data before conversion to the certified CNF representation. -/
structure RawDIMACS where
  variableCount : Nat
  clauses : Array (Array Int)
deriving DecidableEq, Repr

/-- Parse the whole string. The underlying parser requires a header and exactly
the declared number of zero-terminated clauses; `<* eof` rejects trailing bytes. -/
def parseRaw (input : String) : Option RawDIMACS :=
  match DIMACSParser.parseFile input with
  | some (variableCount, clauseCount, values) => do
      let clauses ← splitClauses values [] []
      if clauses.length = clauseCount then
        some ⟨variableCount, clauses.toArray.map List.toArray⟩
      else
        none
  | none => none

/-- Convert one nonzero, in-range DIMACS integer to a membership literal. -/
def literalOfInt (n : Nat) [NeZero n] (value : Int) : Option (Literal n) := do
  if value = 0 then none else
  let magnitude := value.natAbs
  if 1 ≤ magnitude ∧ magnitude ≤ n then
    some ⟨(magnitude - 1 : Nat), decide (0 < value)⟩
  else
    none

/-- Convert a raw clause, refusing duplicate literals. -/
def clauseOfArray (n : Nat) [NeZero n] (values : Array Int) : Option (Clause n) := do
  let literals ← values.toList.mapM (literalOfInt n)
  if literals.Nodup then some literals.toFinset else none

/-- Strict conversion into `EncodeSpec.CNF`: the header must declare exactly
`n` variables, all literals must lie in `1..n`, and duplicate clauses are refused. -/
def rawToCNF (n : Nat) [NeZero n] (raw : RawDIMACS) : Option (CNF n) := do
  if raw.variableCount ≠ n then none else
  let clauses ← raw.clauses.toList.mapM (clauseOfArray n)
  if clauses.Nodup then some clauses.toFinset else none

/-- Total strict DIMACS parser into the certified representation. -/
def parseDIMACS (n : Nat) [NeZero n] (input : String) : Option (CNF n) := do
  rawToCNF n (← parseRaw input)

theorem malformed_header_refused :
    parseDIMACS 3 "p cxf 3 1\n1 0\n" = none := by
  decide

theorem out_of_range_refused :
    rawToCNF 3 ⟨3, #[#[4]]⟩ = none := by decide

theorem wrong_count_refused :
    parseDIMACS 3 "p cnf 3 2\n1 0\n" = none := by
  decide

theorem duplicate_literal_refused :
    rawToCNF 3 ⟨3, #[#[1, 1]]⟩ = none := by decide

theorem trailing_bytes_refused :
    parseDIMACS 3 "p cnf 3 1\n1 0\nX" = none := by
  decide

theorem valid_small_accepted :
    (rawToCNF 3 ⟨3, #[#[1, -2]]⟩).isSome = true := by decide

#print axioms RawDIMACS
#print axioms DIMACSParser.parseNat
#print axioms DIMACSParser.isSpace
#print axioms DIMACSParser.tokenize
#print axioms DIMACSParser.digit?
#print axioms DIMACSParser.parseNatAux
#print axioms DIMACSParser.parseInt
#print axioms DIMACSParser.parseInts
#print axioms DIMACSParser.parseFile
#print axioms splitClauses
#print axioms parseRaw
#print axioms literalOfInt
#print axioms clauseOfArray
#print axioms rawToCNF
#print axioms parseDIMACS
#print axioms malformed_header_refused
#print axioms out_of_range_refused
#print axioms wrong_count_refused
#print axioms duplicate_literal_refused
#print axioms trailing_bytes_refused
#print axioms valid_small_accepted

end BedertLab.ByteBridge
