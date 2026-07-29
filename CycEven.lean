import Mathlib

/-!
# Exact cyclic even-order boundary for ordered-count divergence

The frozen theorem at the end is copied verbatim from
`ArtifactQTargets.cyclicEven_orderedDivergence_iff`.  The proof uses Bedert's
unordered unique-sum convention for `IsUSF` and the canonical ordered count
defined below.
-/

namespace ArtifactQTargets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A sum with exactly one unordered representation in `A`. -/
def HasUniqueSum (A : Finset G) (s : G) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a + b = s ∧
    ∀ c ∈ A, ∀ d ∈ A, c + d = s →
      (c = a ∧ d = b) ∨ (c = b ∧ d = a)

/-- Bedert's no-unique-sum condition. -/
def IsUSF (A : Finset G) : Prop := ∀ s : G, ¬ HasUniqueSum A s

instance (A : Finset G) (s : G) : Decidable (HasUniqueSum A s) := by
  unfold HasUniqueSum
  infer_instance

def pairSum {G : Type*} [AddCommGroup G] (q : Sym2 G) : G :=
  Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ q

def pairFibre {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (s : G) : Finset (Sym2 G) :=
  A.sym2.filter fun q => pairSum q = s

def orderedRepresentationCount
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (s : G) : ℕ :=
  ∑ q ∈ pairFibre A s, if q.IsDiag then 1 else 2

private theorem hasUniqueSum_iff_pairFibre_card_eq_one
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (sum : G) :
    HasUniqueSum A sum ↔ (pairFibre A sum).card = 1 := by
  constructor
  · rintro ⟨a, ha, b, hb, hab, hunique⟩
    rw [Finset.card_eq_one]
    refine ⟨s(a, b), Finset.ext fun q => ?_⟩
    induction q using Sym2.ind with
    | _ c d =>
        simp only [pairFibre, Finset.mem_filter, Finset.mk_mem_sym2_iff,
          pairSum, Sym2.lift_mk, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hc, hd⟩, hcd⟩
          exact Sym2.eq_iff.mpr (hunique c hc d hd hcd)
        · intro hpair
          rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨ha, hb⟩, hab⟩
          · exact ⟨⟨hb, ha⟩, by simpa [add_comm] using hab⟩
  · intro hcount
    rw [Finset.card_eq_one] at hcount
    obtain ⟨q, hq⟩ := hcount
    induction q using Sym2.ind with
    | _ a b =>
        have hmem : s(a, b) ∈ pairFibre A sum := by
          rw [hq]
          simp
        have hab : a ∈ A ∧ b ∈ A ∧ a + b = sum := by
          have hmem' : (a ∈ A ∧ b ∈ A) ∧ a + b = sum := by
            simpa [pairFibre, pairSum] using hmem
          exact ⟨hmem'.1.1, hmem'.1.2, hmem'.2⟩
        refine ⟨a, hab.1, b, hab.2.1, hab.2.2, ?_⟩
        intro c hc d hd hcd
        have hcdmem : s(c, d) ∈ pairFibre A sum := by
          simp [pairFibre, pairSum, hc, hd, hcd]
        have heq : s(c, d) = s(a, b) := by
          rw [hq] at hcdmem
          simpa using hcdmem
        exact Sym2.eq_iff.mp heq

private theorem isUSF_iff_pairFibre_card_ne_one
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) :
    IsUSF A ↔ ∀ sum : G, (pairFibre A sum).card ≠ 1 := by
  constructor
  · intro hUSF sum hcount
    exact hUSF sum
      ((hasUniqueSum_iff_pairFibre_card_eq_one A sum).mpr hcount)
  · intro hcount sum hunique
    exact hcount sum
      ((hasUniqueSum_iff_pairFibre_card_eq_one A sum).mp hunique)

local instance {p : ℕ} [NeZero p] (A : Finset (ZMod p)) :
    Decidable (IsUSF A) := by
  unfold IsUSF
  infer_instance

/-! ## The uniform family for `m ≥ 6` -/

/--
The family
`{0, ..., m} \ {m - 2} ∪ {m + 2} ⊆ ZMod (2 * m)`,
equivalently `{0, ..., m - 3} ∪ {m - 1, m, m + 2}`.
-/
def cyclicEvenWitness (m : ℕ) [NeZero (2 * m)] :
    Finset (ZMod (2 * m)) :=
  Finset.univ.filter fun x =>
    (x.val ≤ m ∧ x.val ≠ m - 2) ∨ x.val = m + 2

private lemma natCast_mem_cyclicEvenWitness
    {m k : ℕ} [NeZero (2 * m)]
    (hm : 6 ≤ m) (hk : k ≤ m) (hne : k ≠ m - 2) :
    (k : ZMod (2 * m)) ∈ cyclicEvenWitness m := by
  have hklt : k < 2 * m := by omega
  simp [cyclicEvenWitness, ZMod.val_natCast_of_lt hklt, hk, hne]

private lemma extra_mem_cyclicEvenWitness
    {m : ℕ} [NeZero (2 * m)] (hm : 6 ≤ m) :
    ((m + 2 : ℕ) : ZMod (2 * m)) ∈ cyclicEvenWitness m := by
  have hlt : m + 2 < 2 * m := by omega
  rw [cyclicEvenWitness, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Or.inr ?_⟩
  exact ZMod.val_natCast_of_lt hlt

private lemma natCast_injective_below
    {m a b : ℕ} [NeZero (2 * m)]
    (ha : a < 2 * m) (hb : b < 2 * m)
    (h : (a : ZMod (2 * m)) = (b : ZMod (2 * m))) :
    a = b := by
  have hval := congrArg ZMod.val h
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hval

private lemma natSym2_ne
    {m a b c d : ℕ} [NeZero (2 * m)]
    (ha : a < 2 * m) (_hb : b < 2 * m)
    (hc : c < 2 * m) (hd : d < 2 * m)
    (hac : a ≠ c) (had : a ≠ d) :
    s((a : ZMod (2 * m)), (b : ZMod (2 * m))) ≠
      s((c : ZMod (2 * m)), (d : ZMod (2 * m))) := by
  intro h
  rcases Sym2.eq_iff.mp h with hdirect | hswap
  · exact hac (natCast_injective_below ha hc hdirect.1)
  · exact had (natCast_injective_below ha hd hswap.1)

private lemma natCast_pair_sum_eq_of_eq_val
    {m a b : ℕ} [NeZero (2 * m)] {s : ZMod (2 * m)}
    (h : a + b = s.val) :
    (a : ZMod (2 * m)) + (b : ZMod (2 * m)) = s := by
  rw [← Nat.cast_add, h]
  exact ZMod.natCast_zmod_val s

private lemma natCast_pair_sum_eq_of_eq_val_add_mod
    {m a b : ℕ} [NeZero (2 * m)] {s : ZMod (2 * m)}
    (h : a + b = s.val + 2 * m) :
    (a : ZMod (2 * m)) + (b : ZMod (2 * m)) = s := by
  rw [← Nat.cast_add, h, Nat.cast_add, ZMod.natCast_self, add_zero]
  exact ZMod.natCast_zmod_val s

private lemma two_le_pairFibre_card_of_nat_pairs
    {m a b c d : ℕ} {A : Finset (ZMod (2 * m))}
    {sum : ZMod (2 * m)}
    (ha : (a : ZMod (2 * m)) ∈ A)
    (hb : (b : ZMod (2 * m)) ∈ A)
    (hc : (c : ZMod (2 * m)) ∈ A)
    (hd : (d : ZMod (2 * m)) ∈ A)
    (hsum₁ : (a : ZMod (2 * m)) + (b : ZMod (2 * m)) = sum)
    (hsum₂ : (c : ZMod (2 * m)) + (d : ZMod (2 * m)) = sum)
    (hpairs :
      s((a : ZMod (2 * m)), (b : ZMod (2 * m))) ≠
        s((c : ZMod (2 * m)), (d : ZMod (2 * m)))) :
    2 ≤ (pairFibre A sum).card := by
  let q₁ : Sym2 (ZMod (2 * m)) :=
    s((a : ZMod (2 * m)), (b : ZMod (2 * m)))
  let q₂ : Sym2 (ZMod (2 * m)) :=
    s((c : ZMod (2 * m)), (d : ZMod (2 * m)))
  have hq₁ : q₁ ∈ pairFibre A sum := by
    simp [q₁, pairFibre, pairSum, ha, hb, hsum₁]
  have hq₂ : q₂ ∈ pairFibre A sum := by
    simp [q₂, pairFibre, pairSum, hc, hd, hsum₂]
  have hsub : {q₁, q₂} ⊆ pairFibre A sum := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hq₁
    · exact hq₂
  have hcard := Finset.card_le_card hsub
  have hqne : q₁ ≠ q₂ := by
    simpa [q₁, q₂] using hpairs
  simpa [hqne] using hcard

private theorem cyclicEvenWitness_pairFibre_card_ge_two
    {m : ℕ} [NeZero (2 * m)]
    (hm : 6 ≤ m) (sum : ZMod (2 * m)) :
    2 ≤ (pairFibre (cyclicEvenWitness m) sum).card := by
  let r := sum.val
  have hrlt : r < 2 * m := sum.val_lt
  have hzero : 0 < m := by omega
  by_cases hr0 : r = 0
  · subst r
    apply two_le_pairFibre_card_of_nat_pairs
        (a := 0) (b := 0) (c := m) (d := m)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact natCast_pair_sum_eq_of_eq_val (by omega)
    · exact natCast_pair_sum_eq_of_eq_val_add_mod (by omega)
    · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
  by_cases hr1 : r = 1
  · subst r
    apply two_le_pairFibre_card_of_nat_pairs
        (a := 0) (b := 1) (c := m - 1) (d := m + 2)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
    · exact extra_mem_cyclicEvenWitness hm
    · exact natCast_pair_sum_eq_of_eq_val (by omega)
    · exact natCast_pair_sum_eq_of_eq_val_add_mod (by omega)
    · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
  by_cases hrlow : r ≤ m
  · by_cases hrepair₁ : r = m - 2
    · subst r
      apply two_le_pairFibre_card_of_nat_pairs
          (a := 1) (b := m - 3) (c := 2) (d := m - 4)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
    by_cases hrepair₂ : r = m - 1
    · subst r
      apply two_le_pairFibre_card_of_nat_pairs
          (a := 0) (b := m - 1) (c := 2) (d := m - 3)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
    · apply two_le_pairFibre_card_of_nat_pairs
          (a := 0) (b := r) (c := 1) (d := r - 1)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
  · have hrhigh : m < r := by omega
    by_cases hrend : r = 2 * m - 1
    · subst r
      apply two_le_pairFibre_card_of_nat_pairs
          (a := m - 1) (b := m) (c := m - 3) (d := m + 2)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact extra_mem_cyclicEvenWitness hm
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
    by_cases hrepair₃ : r = 2 * m - 3
    · subst r
      apply two_le_pairFibre_card_of_nat_pairs
          (a := m - 3) (b := m) (c := m - 5) (d := m + 2)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact extra_mem_cyclicEvenWitness hm
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
    by_cases hrepair₄ : r = 2 * m - 2
    · subst r
      apply two_le_pairFibre_card_of_nat_pairs
          (a := m - 1) (b := m - 1) (c := m - 4) (d := m + 2)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact extra_mem_cyclicEvenWitness hm
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
    · apply two_le_pairFibre_card_of_nat_pairs
          (a := r - m) (b := m) (c := r - m + 1) (d := m - 1)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_mem_cyclicEvenWitness hm (by omega) (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natCast_pair_sum_eq_of_eq_val (by omega)
      · exact natSym2_ne (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)

theorem cyclicEvenWitness_isUSF
    {m : ℕ} [NeZero (2 * m)] (hm : 6 ≤ m) :
    IsUSF (cyclicEvenWitness m) := by
  intro sum hunique
  have hcount :
      (pairFibre (cyclicEvenWitness m) sum).card = 1 := by
    exact
      (hasUniqueSum_iff_pairFibre_card_eq_one
        (cyclicEvenWitness m) sum).mp hunique
  have htwo := cyclicEvenWitness_pairFibre_card_ge_two hm sum
  omega

theorem cyclicEvenWitness_ordered_zero
    {m : ℕ} [NeZero (2 * m)] (hm : 6 ≤ m) :
    orderedRepresentationCount (cyclicEvenWitness m) 0 = 2 := by
  let q₀ : Sym2 (ZMod (2 * m)) := s(0, 0)
  let qₘ : Sym2 (ZMod (2 * m)) :=
    s((m : ZMod (2 * m)), (m : ZMod (2 * m)))
  have hmlt : m < 2 * m := by omega
  have hmem0 :
      (0 : ZMod (2 * m)) ∈ cyclicEvenWitness m := by
    rw [cyclicEvenWitness, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Or.inl ⟨by simp, ?_⟩⟩
    rw [show ZMod.val (0 : ZMod (2 * m)) = 0 by simp]
    exact (Nat.sub_pos_of_lt (by omega : 2 < m)).ne
  have hmemm :
      (m : ZMod (2 * m)) ∈ cyclicEvenWitness m :=
    natCast_mem_cyclicEvenWitness (k := m) hm (by omega) (by omega)
  have hmmsum :
      (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
    calc
      (m : ZMod (2 * m)) + (m : ZMod (2 * m)) =
          ((m + m : ℕ) : ZMod (2 * m)) := by rw [Nat.cast_add]
      _ = ((2 * m : ℕ) : ZMod (2 * m)) := by congr 1; omega
      _ = 0 := ZMod.natCast_self (2 * m)
  have hfibre :
      pairFibre (cyclicEvenWitness m) 0 = {q₀, qₘ} := by
    ext q
    induction q using Sym2.ind with
    | _ a b =>
        simp only [pairFibre, Finset.mem_filter, Finset.mk_mem_sym2_iff,
          pairSum, Sym2.lift_mk, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨ha, hb⟩, hab⟩
          have hapred :
              (a.val ≤ m ∧ a.val ≠ m - 2) ∨ a.val = m + 2 :=
            (Finset.mem_filter.mp ha).2
          have hbpred :
              (b.val ≤ m ∧ b.val ≠ m - 2) ∨ b.val = m + 2 :=
            (Finset.mem_filter.mp hb).2
          have hvalzero : (a + b).val = 0 := by
            rw [hab]
            simp
          by_cases hlt : a.val + b.val < 2 * m
          · rw [ZMod.val_add_of_lt hlt] at hvalzero
            have hava : a.val = 0 := by omega
            have hbva : b.val = 0 := by omega
            left
            apply Sym2.eq_iff.mpr
            left
            exact ⟨(ZMod.val_eq_zero a).mp hava,
              (ZMod.val_eq_zero b).mp hbva⟩
          · have hle : 2 * m ≤ a.val + b.val := Nat.le_of_not_gt hlt
            rw [ZMod.val_add_of_le hle] at hvalzero
            have habvals : a.val + b.val = 2 * m := by
              have havlt := a.val_lt
              have hbvlt := b.val_lt
              omega
            have hava : a.val = m := by
              rcases hapred with ⟨hale, hane⟩ | haextra
              · rcases hbpred with ⟨hble, hbne⟩ | hbextra
                · omega
                · omega
              · rcases hbpred with ⟨hble, hbne⟩ | hbextra <;> omega
            have hbva : b.val = m := by
              rcases hapred with ⟨hale, hane⟩ | haextra
              · rcases hbpred with ⟨hble, hbne⟩ | hbextra
                · omega
                · omega
              · rcases hbpred with ⟨hble, hbne⟩ | hbextra <;> omega
            right
            apply Sym2.eq_iff.mpr
            left
            constructor
            · apply ZMod.val_injective (2 * m)
              rw [ZMod.val_natCast_of_lt hmlt]
              exact hava
            · apply ZMod.val_injective (2 * m)
              rw [ZMod.val_natCast_of_lt hmlt]
              exact hbva
        · intro hq
          rcases hq with hq | hq
          · rcases Sym2.eq_iff.mp hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              exact ⟨⟨hmem0, hmem0⟩, by simp⟩
          · rcases Sym2.eq_iff.mp hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              exact ⟨⟨hmemm, hmemm⟩, hmmsum⟩
  have hqne : q₀ ≠ qₘ := by
    intro h
    have h0m :
        (0 : ZMod (2 * m)) = (m : ZMod (2 * m)) := by
      rcases Sym2.eq_iff.mp h with hdirect | hswap
      · exact hdirect.1
      · exact hswap.1
    have hvals := congrArg ZMod.val h0m
    simp [ZMod.val_natCast_of_lt hmlt] at hvals
    omega
  rw [orderedRepresentationCount, hfibre]
  simp [q₀, qₘ, hqne]

/-! ## Kernel exhaustion below order twelve -/

private theorem int_finset_not_isUSF_of_nonempty
    (A : Finset ℤ) (hA : A.Nonempty) :
    ¬ IsUSF A := by
  let top := A.max' hA
  have htop : top ∈ A := Finset.max'_mem A hA
  have hunique : HasUniqueSum A (top + top) := by
    refine ⟨top, htop, top, htop, rfl, ?_⟩
    intro c hc d hd hsum
    have hcTop : c ≤ top := Finset.le_max' A c hc
    have hdTop : d ≤ top := Finset.le_max' A d hd
    have hct : c = top := by omega
    have hdt : d = top := by omega
    exact Or.inl ⟨hct, hdt⟩
  intro hUSF
  exact hUSF (top + top) hunique

private theorem no_orderedDivergence_C0 :
    ¬ (∃ A : Finset (ZMod 0),
      IsUSF A ∧
        ∃ x : ZMod 0, orderedRepresentationCount A x = 2) := by
  rintro ⟨A, hUSF, x, hx⟩
  have hA : A.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst A
    simp [orderedRepresentationCount, pairFibre] at hx
  exact int_finset_not_isUSF_of_nonempty A hA hUSF

private theorem no_orderedDivergence_C2 :
    ¬ (∃ A : Finset (ZMod 2),
      IsUSF A ∧
        ∃ x : ZMod 2, orderedRepresentationCount A x = 2) := by
  intro h
  apply
    (show ¬ (∃ A : Finset (ZMod 2),
      (∀ sum : ZMod 2, (pairFibre A sum).card ≠ 1) ∧
        ∃ x : ZMod 2, orderedRepresentationCount A x = 2) by decide)
  obtain ⟨A, hUSF, hx⟩ := h
  exact ⟨A, (isUSF_iff_pairFibre_card_ne_one A).mp hUSF, hx⟩

private theorem no_orderedDivergence_C4 :
    ¬ (∃ A : Finset (ZMod 4),
      IsUSF A ∧
        ∃ x : ZMod 4, orderedRepresentationCount A x = 2) := by
  intro h
  apply
    (show ¬ (∃ A : Finset (ZMod 4),
      (∀ sum : ZMod 4, (pairFibre A sum).card ≠ 1) ∧
        ∃ x : ZMod 4, orderedRepresentationCount A x = 2) by decide)
  obtain ⟨A, hUSF, hx⟩ := h
  exact ⟨A, (isUSF_iff_pairFibre_card_ne_one A).mp hUSF, hx⟩

private theorem no_orderedDivergence_C6 :
    ¬ (∃ A : Finset (ZMod 6),
      IsUSF A ∧
        ∃ x : ZMod 6, orderedRepresentationCount A x = 2) := by
  intro h
  apply
    (show ¬ (∃ A : Finset (ZMod 6),
      (∀ sum : ZMod 6, (pairFibre A sum).card ≠ 1) ∧
        ∃ x : ZMod 6, orderedRepresentationCount A x = 2) by decide)
  obtain ⟨A, hUSF, hx⟩ := h
  exact ⟨A, (isUSF_iff_pairFibre_card_ne_one A).mp hUSF, hx⟩

set_option maxRecDepth 100000 in
private theorem no_orderedDivergence_C8 :
    ¬ (∃ A : Finset (ZMod 8),
      IsUSF A ∧
        ∃ x : ZMod 8, orderedRepresentationCount A x = 2) := by
  intro h
  apply
    (show ¬ (∃ A : Finset (ZMod 8),
      (∀ sum : ZMod 8, (pairFibre A sum).card ≠ 1) ∧
        ∃ x : ZMod 8, orderedRepresentationCount A x = 2) by decide)
  obtain ⟨A, hUSF, hx⟩ := h
  exact ⟨A, (isUSF_iff_pairFibre_card_ne_one A).mp hUSF, hx⟩

set_option maxRecDepth 100000 in
private theorem no_orderedDivergence_C10 :
    ¬ (∃ A : Finset (ZMod 10),
      IsUSF A ∧
        ∃ x : ZMod 10, orderedRepresentationCount A x = 2) := by
  intro h
  apply
    (show ¬ (∃ A : Finset (ZMod 10),
      (∀ sum : ZMod 10, (pairFibre A sum).card ≠ 1) ∧
        ∃ x : ZMod 10, orderedRepresentationCount A x = 2) by decide)
  obtain ⟨A, hUSF, hx⟩ := h
  exact ⟨A, (isUSF_iff_pairFibre_card_ne_one A).mp hUSF, hx⟩

/-!
The frozen biconditional is filled after the symbolic positive half and the
kernel-exhaustive small-order half.
-/
theorem cyclicEven_orderedDivergence_iff (m : ℕ) :
    (∃ A : Finset (ZMod (2 * m)),
      IsUSF A ∧
        ∃ x : ZMod (2 * m), orderedRepresentationCount A x = 2) ↔
      6 ≤ m := by
  constructor
  · intro h
    by_contra hnot
    have hmle : m ≤ 5 := by omega
    interval_cases m
    · exact no_orderedDivergence_C0 (by simpa using h)
    · exact no_orderedDivergence_C2 (by simpa using h)
    · exact no_orderedDivergence_C4 (by simpa using h)
    · exact no_orderedDivergence_C6 (by simpa using h)
    · exact no_orderedDivergence_C8 (by simpa using h)
    · exact no_orderedDivergence_C10 (by simpa using h)
  · intro hm
    letI : NeZero (2 * m) := ⟨by omega⟩
    exact ⟨cyclicEvenWitness m, cyclicEvenWitness_isUSF hm,
      0, cyclicEvenWitness_ordered_zero hm⟩

/-- Concrete satisfiability companion and direct application of the boundary theorem. -/
theorem cyclicEven_orderedDivergence_satisfiable :
    ∃ A : Finset (ZMod 12),
      IsUSF A ∧
        ∃ x : ZMod 12, orderedRepresentationCount A x = 2 := by
  simpa using (cyclicEven_orderedDivergence_iff 6).mpr (by decide)

#print axioms cyclicEvenWitness_isUSF
#print axioms cyclicEvenWitness_ordered_zero
#print axioms no_orderedDivergence_C0
#print axioms no_orderedDivergence_C2
#print axioms no_orderedDivergence_C4
#print axioms no_orderedDivergence_C6
#print axioms no_orderedDivergence_C8
#print axioms no_orderedDivergence_C10
#print axioms cyclicEven_orderedDivergence_iff
#print axioms cyclicEven_orderedDivergence_satisfiable

end ArtifactQTargets
