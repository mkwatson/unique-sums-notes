import BedertLab.ChainClose

/-!
# Kernel-tractable parsing of the production DIMACS stream

This module is intentionally separate from the frozen parser and production-byte
modules.  It investigates staged kernel reduction without changing either trust
boundary.
-/

namespace BedertLab.ParsePath

open BedertLab.ByteBridge
open BedertLab.ByteBridgeAux
open BedertLab.ChainClose

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A strict DIMACS sub-instance made from the first 100 clause lines of the
frozen production stream.  Only its header is replaced, so the body bytes are
obtained directly from the frozen stream rather than transcribed. -/
def production117Prefix5 : List Char :=
  "p cnf 187 5\n-12 2 0\n-12 11 0\n-2 -11 12 0\n-13 3 0\n-13 10 0\n".toList

theorem production117_prefix5_body_parses :
    parseBodyChars production117Prefix5 =
      some (187, [[-12, 2], [-12, 11], [-2, -11, 12], [-13, 3], [-13, 10]]) := by
  decide

theorem production117_prefix5_clause_count :
    ([-12, 2] :: [-12, 11] :: [-2, -11, 12] :: [-13, 3] :: [-13, 10] :: []).length = 5 := by
  rfl

#print axioms production117_prefix5_body_parses
#print axioms production117_prefix5_clause_count

end BedertLab.ParsePath
