import Mathlib.Data.ZMod.Basic

/-!
# Double-cyclic descent laboratory

Every unique-sum claim in this file uses Bedert's **unordered-pair**
convention, with repetition allowed.  Swapping the two entries is not a new
representation.  `OrderedRepCount` is not used to infer any unordered claim.

`DoubleCyclicConjecture` below is copied unchanged from `Mg.lean`.  It remains
a conjectural proposition, never a theorem.
-/

namespace Dcyc

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- Unordered-pair unique-sum-free predicate, explicitly nonempty. -/
def IsUSF (A : Finset G) : Prop :=
  A.Nonempty ∧
    ∀ a ∈ A, ∀ b ∈ A,
      ∃ x ∈ A, ∃ y ∈ A,
        x + y = a + b ∧
          ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- Exact minimum for the unordered-pair predicate. -/
def HasMinUSFSize
    (G : Type*) [AddCommMonoid G] [DecidableEq G] [Fintype G] (n : ℕ) : Prop :=
  (∃ A : Finset G, IsUSF A ∧ A.card = n) ∧
    ∀ A : Finset G, IsUSF A → n ≤ A.card

/-- Cyclic wrapper carrying the nonzero modulus explicitly. -/
def HasMinCyclicUSFSize (modulus n : ℕ) (hmodulus : modulus ≠ 0) : Prop :=
  letI : NeZero modulus := ⟨hmodulus⟩
  HasMinUSFSize (ZMod modulus) n

/-- FROZEN: copied byte-for-byte at the declaration body from `Mg.lean`. -/
def DoubleCyclicConjecture : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), Odd p →
    ∀ n : ℕ,
      HasMinCyclicUSFSize p n hp.ne_zero ↔
        HasMinCyclicUSFSize (2 * p) n (Nat.mul_ne_zero (by decide) hp.ne_zero)

/-- A sum has exactly one representation modulo swapping, under the
unordered-pair convention. -/
def HasUniqueUnorderedRep (A : Finset G) (sum : G) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A,
    a + b = sum ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = sum →
        ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- Projection to the second factor. -/
def ProjectSecond
    {H K : Type*} [DecidableEq H] [DecidableEq K]
    (A : Finset (H × K)) : Finset K :=
  A.image Prod.snd

/-!
## Kernel-certified parity-fiber doubling obstruction

`A2x11` contains both parity lifts of every element of `B11`.  It is USF for
unordered pairs, but its projection has uniquely represented sums.  This is
the naive-projection obstruction inside `C₂ × Cₚ`, not merely in `C₁₂`.
-/

def B11 : Finset (ZMod 11) := {0, 1, 2, 4, 7}

def A2x11 : Finset (ZMod 2 × ZMod 11) :=
  {
    (0, 0), (0, 1), (0, 2), (0, 4), (0, 7),
    (1, 0), (1, 1), (1, 2), (1, 4), (1, 7)
  }

theorem A2x11_card : A2x11.card = 10 := by
  unfold A2x11
  decide

theorem A2x11_isUSF_unordered : IsUSF A2x11 := by
  unfold A2x11 IsUSF
  decide

theorem A2x11_projectSecond : ProjectSecond A2x11 = B11 := by
  unfold A2x11 B11 ProjectSecond
  decide

theorem B11_sum_one_unique_unordered :
    HasUniqueUnorderedRep B11 1 := by
  unfold B11 HasUniqueUnorderedRep
  decide

theorem B11_not_USF_unordered : ¬IsUSF B11 := by
  unfold B11 IsUSF
  decide

/-!
## Exchange-stuck doubled-shadow fixture

This finite statement uses the same unordered-pair predicate.  The full lift
of `B11` has no cardinality-preserving one-element USF exchange, and deleting
one lift is not USF.  It is an obstruction to an *unqualified* local-exchange
lemma only: its cardinality is ten, whereas the certified minimum in `C₂ × C₁₁`
has cardinality seven.
-/

theorem A2x11_no_USF_single_lift_deletion_unordered :
    ∀ a : ZMod 2 × ZMod 11, a ∈ A2x11 →
      ¬IsUSF (A2x11.erase a) := by
  letI (S : Finset (ZMod 2 × ZMod 11)) : Decidable (IsUSF S) := by
    unfold IsUSF
    infer_instance
  decide

/-!
## The proposed `4 ∣ |G|` branch needs a `3 ∤ |G|` guard

The unconditional claim is false: `C₁₂` has a three-element USF subgroup.
The two order-four groups do have minimum four.  The general corrected branch
still needs the mathematical classification excluding three-element USF sets
when there is no 3-torsion.
-/

theorem minUSFSize_C4_unordered :
    HasMinCyclicUSFSize 4 4 (by decide) := by
  letI : NeZero 4 := ⟨by decide⟩
  letI (A : Finset (ZMod 4)) : Decidable (IsUSF A) := by
    unfold IsUSF
    infer_instance
  unfold HasMinCyclicUSFSize HasMinUSFSize
  decide

theorem minUSFSize_C2xC2_unordered :
    HasMinUSFSize (ZMod 2 × ZMod 2) 4 := by
  letI : NeZero 2 := ⟨by decide⟩
  letI (A : Finset (ZMod 2 × ZMod 2)) : Decidable (IsUSF A) := by
    unfold IsUSF
    infer_instance
  unfold HasMinUSFSize
  decide

def C12ThreeWitness : Finset (ZMod 12) := {0, 4, 8}

theorem C12ThreeWitness_card : C12ThreeWitness.card = 3 := by
  unfold C12ThreeWitness
  decide

theorem C12ThreeWitness_isUSF_unordered : IsUSF C12ThreeWitness := by
  unfold C12ThreeWitness IsUSF
  decide

theorem C12_refutes_unconditional_four_branch :
    4 ∣ 12 ∧
      ∃ A : Finset (ZMod 12), IsUSF A ∧ A.card = 3 := by
  exact ⟨by decide, C12ThreeWitness, C12ThreeWitness_isUSF_unordered,
    C12ThreeWitness_card⟩

/-- Stable assembly interface for the corrected four-branch proof.  The open
mathematics is exactly the universal four-witness and lower-bound inputs. -/
theorem hasMinUSFSize_four_of_witness_and_lower
    [Fintype G]
    (hWitness : ∃ A : Finset G, IsUSF A ∧ A.card = 4)
    (hLower : ∀ A : Finset G, IsUSF A → 4 ≤ A.card) :
    HasMinUSFSize G 4 :=
  ⟨hWitness, hLower⟩

/-!
For a normalized three-set `{0,x,y}`, the represented sum `x` has only one
possible genuinely different unordered representation, namely `{y,y}`.
Symmetry gives `x = 2y` and `y = 2x`.  This is the algebraic core of the
classification of three-element USF sets as cosets of order-three subgroups.
-/

theorem normalized_three_USF_relations_unordered
    {H : Type*} [AddCommGroup H] [DecidableEq H]
    {x y : H} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hUSF : IsUSF ({0, x, y} : Finset H)) :
    x = y + y ∧ y = x + x := by
  have hxmem : x ∈ ({0, x, y} : Finset H) := by simp
  have hymem : y ∈ ({0, x, y} : Finset H) := by simp
  have hzero : (0 : H) ∈ ({0, x, y} : Finset H) := by simp
  obtain ⟨u, hu, v, hv, hsum, hnew⟩ :=
    hUSF.2 0 hzero x hxmem
  have hxyy : x = y + y := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with (rfl | rfl | rfl) <;>
      rcases hv with (rfl | rfl | rfl) <;>
      simp_all
  obtain ⟨u, hu, v, hv, hsum, hnew⟩ :=
    hUSF.2 0 hzero y hymem
  have hyxx : y = x + x := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with (rfl | rfl | rfl) <;>
      rcases hv with (rfl | rfl | rfl) <;>
      simp_all
  exact ⟨hxyy, hyxx⟩

theorem normalized_three_USF_has_three_torsion_unordered
    {H : Type*} [AddCommGroup H] [DecidableEq H]
    {x y : H} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hUSF : IsUSF ({0, x, y} : Finset H)) :
    x + x + x = 0 := by
  obtain ⟨hxyy, hyxx⟩ :=
    normalized_three_USF_relations_unordered hx hy hxy hUSF
  calc
    x + x + x = y + x := by rw [hyxx]
    _ = y + (y + y) := by rw [hxyy]
    _ = 0 := by
      have := congrArg (fun z => z - x) hyxx
      simp [hxyy, add_assoc] at this
      rw [← this]
      exact add_neg_cancel y

/-!
## What transfers from the factoring lane

The balanced-set proof chooses two witnesses for each point.  For USF, the
correct arity is different: choose an alternate pair for each pair of points.
The following closure lemma is the exact minimality component that survives.
It does not supply the determinant bound needed for projection constancy.
-/

structure UnorderedPairWitness (A : Finset G) where
  left : A → A → A
  right : A → A → A
  sum_eq : ∀ a b,
    (left a b : G) + (right a b : G) = (a : G) + (b : G)
  genuinely_new : ∀ a b,
    ¬(((left a b : G) = a ∧ (right a b : G) = b) ∨
      ((left a b : G) = b ∧ (right a b : G) = a))

def PairClosed
    {A : Finset G} (w : UnorderedPairWitness A) (E : Finset G) : Prop :=
  ∀ a : A, (a : G) ∈ E → ∀ b : A, (b : G) ∈ E →
    (w.left a b : G) ∈ E ∧ (w.right a b : G) ∈ E

def IsMinUSFSet (A : Finset G) : Prop :=
  IsUSF A ∧ ∀ T : Finset G, IsUSF T → A.card ≤ T.card

omit [DecidableEq G] in
theorem pairClosed_isUSF_unordered
    {A E : Finset G} (w : UnorderedPairWitness A)
    (hEA : E ⊆ A) (hE : E.Nonempty) (hClosed : PairClosed w E) :
    IsUSF E := by
  refine ⟨hE, ?_⟩
  intro a ha b hb
  let aA : A := ⟨a, hEA ha⟩
  let bA : A := ⟨b, hEA hb⟩
  obtain ⟨hleft, hright⟩ := hClosed aA ha bA hb
  exact ⟨w.left aA bA, hleft, w.right aA bA, hright,
    w.sum_eq aA bA, w.genuinely_new aA bA⟩

omit [DecidableEq G] in
theorem noProperPairClosed_of_min_unordered
    {A E : Finset G} (hA : IsMinUSFSet A)
    (w : UnorderedPairWitness A)
    (hEA : E ⊆ A) (hE : E.Nonempty) (hClosed : PairClosed w E) :
    E = A := by
  exact Finset.eq_of_subset_of_card_le hEA
    (hA.2 E (pairClosed_isUSF_unordered w hEA hE hClosed))

/-!
## Small kernel localization checks

`MeetsBothParityFibers` is purely about the `C₂` coordinate.  The following
claims say that a bounded unordered-USF set cannot meet both fibers.  They are
finite kernel computations, not a general proof of the descent.
-/

def MeetsBothParityFibers
    {H : Type*} [DecidableEq H]
    (A : Finset (ZMod 2 × H)) : Prop :=
  (∃ x : H, (0, x) ∈ A) ∧ (∃ x : H, (1, x) ∈ A)

theorem C2xC3_bounded_USF_localizes_unordered :
    ∀ A : Finset (ZMod 2 × ZMod 3),
      IsUSF A → A.card ≤ 3 → ¬MeetsBothParityFibers A := by
  letI : NeZero 2 := ⟨by decide⟩
  letI : NeZero 3 := ⟨by decide⟩
  letI (A : Finset (ZMod 2 × ZMod 3)) : Decidable (IsUSF A) := by
    unfold IsUSF
    infer_instance
  letI (A : Finset (ZMod 2 × ZMod 3)) :
      Decidable (MeetsBothParityFibers A) := by
    unfold MeetsBothParityFibers
    infer_instance
  decide

#print axioms A2x11_isUSF_unordered
#print axioms A2x11_projectSecond
#print axioms B11_sum_one_unique_unordered
#print axioms B11_not_USF_unordered
#print axioms A2x11_no_USF_single_lift_deletion_unordered
#print axioms minUSFSize_C4_unordered
#print axioms minUSFSize_C2xC2_unordered
#print axioms C12ThreeWitness_isUSF_unordered
#print axioms C12_refutes_unconditional_four_branch
#print axioms C2xC3_bounded_USF_localizes_unordered

end Dcyc
