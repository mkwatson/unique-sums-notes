import BedertLab.EncodeSpec

/-!
# Kernel verification of retained USF witnesses

The executable predicate is the ordered-representation formulation from
`EncodeSpec`: every residue has ordered representation count different from
both one and two.  All witness and control theorems below are proved by kernel
reduction with `decide`.
-/

namespace BedertLab.WitnessKernel

open BedertLab.EncodeSpec

set_option maxRecDepth 100000

/-- Ordered-count USF predicate used by every theorem in this module. -/
def IsUSF {p : ℕ} [NeZero p] (A : Finset (ZMod p)) : Prop :=
  ∀ s : ZMod p,
    orderedRepresentationCount A s ≠ 1 ∧ orderedRepresentationCount A s ≠ 2

instance {p : ℕ} [NeZero p] (A : Finset (ZMod p)) : Decidable (IsUSF A) := by
  unfold IsUSF
  infer_instance

/-- The executable predicate is definitionally equivalent to the reference specification. -/
theorem isUSF_iff_encodeSpec {p : ℕ} [NeZero p] (A : Finset (ZMod p)) :
    IsUSF A ↔ OrderedUSF A := by
  rfl

/-- Number of residues whose ordered representation count fires the USF exclusion. -/
def firingCount {p : ℕ} [NeZero p] (A : Finset (ZMod p)) : ℕ :=
  (Finset.univ.filter fun s =>
    orderedRepresentationCount A s = 1 ∨ orderedRepresentationCount A s = 2).card

def published53 : Finset (ZMod 53) :=
  {0, 1, 5, 7, 14, 16, 18, 28, 32, 35, 36, 39, 43, 51}

def published59 : Finset (ZMod 59) :=
  {0, 1, 2, 3, 4, 5, 9, 10, 16, 25, 27, 32, 42, 44, 48}

def published61 : Finset (ZMod 61) :=
  {0, 1, 2, 3, 4, 6, 15, 21, 22, 24, 42, 49, 55, 56, 58}

def published67 : Finset (ZMod 67) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 11, 14, 15, 25, 26, 50, 53, 54}

def published71 : Finset (ZMod 71) :=
  {0, 1, 2, 3, 4, 5, 7, 8, 12, 31, 45, 46, 57, 59, 61, 64}

def published73 : Finset (ZMod 73) :=
  {0, 1, 2, 3, 4, 5, 8, 9, 13, 21, 23, 25, 29, 44, 45, 65}

def m53Exact14Witness : Finset (ZMod 53) :=
  {0, 1, 18, 21, 24, 25, 26, 27, 31, 32, 35, 42, 43, 46}

def m59NoUSF13SetWitness : Finset (ZMod 59) :=
  {0, 1, 10, 12, 14, 18, 22, 23, 31, 34, 38, 39, 40, 51, 58}

theorem published53_isUSF : IsUSF published53 := by decide
theorem published59_isUSF : IsUSF published59 := by decide
theorem published61_isUSF : IsUSF published61 := by decide
theorem published67_isUSF : IsUSF published67 := by decide
theorem published71_isUSF : IsUSF published71 := by decide
theorem published73_isUSF : IsUSF published73 := by decide

theorem m53_exact_14_witness_isUSF : IsUSF m53Exact14Witness := by decide
theorem m59_no_usf_13_set_witness_isUSF : IsUSF m59NoUSF13SetWitness := by decide

def falseGloss11 : Finset (ZMod 11) := {0, 1, 2, 4, 7}

/-- Negative control from the false-gloss retraction. -/
theorem falseGloss11_not_isUSF : ¬ IsUSF falseGloss11 := by decide

/-- Five residues fire the ordered multiplicity-one-or-two exclusion. -/
theorem falseGloss11_firingCount : firingCount falseGloss11 = 5 := by decide

/-- The published p=53 witness with 51 perturbed to 50. -/
def perturbed53 : Finset (ZMod 53) :=
  {0, 1, 5, 7, 14, 16, 18, 28, 32, 35, 36, 39, 43, 50}

theorem perturbed53_not_isUSF : ¬ IsUSF perturbed53 := by decide

/-- Twelve residues fire after the one-element perturbation. -/
theorem perturbed53_firingCount : firingCount perturbed53 = 12 := by decide

#print axioms IsUSF
#print axioms instDecidableIsUSF
#print axioms isUSF_iff_encodeSpec
#print axioms firingCount
#print axioms published53
#print axioms published59
#print axioms published61
#print axioms published67
#print axioms published71
#print axioms published73
#print axioms m53Exact14Witness
#print axioms m59NoUSF13SetWitness
#print axioms published53_isUSF
#print axioms published59_isUSF
#print axioms published61_isUSF
#print axioms published67_isUSF
#print axioms published71_isUSF
#print axioms published73_isUSF
#print axioms m53_exact_14_witness_isUSF
#print axioms m59_no_usf_13_set_witness_isUSF
#print axioms falseGloss11
#print axioms falseGloss11_not_isUSF
#print axioms falseGloss11_firingCount
#print axioms perturbed53
#print axioms perturbed53_not_isUSF
#print axioms perturbed53_firingCount

end BedertLab.WitnessKernel
