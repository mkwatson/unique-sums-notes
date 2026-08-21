import BedertLab.SequentialCounter

/-!
# Correctness of the production sequential counter

The signal at row `i`, column `j` records whether at least `j + 1` visible
inputs among rows `0, ..., i` are true.
-/

namespace BedertLab.SequentialCounterProof

open BedertLab.ProjectionTheorem
open BedertLab.SequentialCounter

def prefixCount {n : ℕ} (membership : ZMod n → Bool) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun i : ℕ => membership (i : ZMod n) = true).card

lemma prefixCount_succ {n : ℕ} (membership : ZMod n → Bool) (m : ℕ) :
    prefixCount membership (m + 1) =
      prefixCount membership m + if membership (m : ZMod n) then 1 else 0 := by
  unfold prefixCount
  rw [show m + 1 = Nat.succ m by omega, Finset.range_succ]
  rw [Finset.filter_insert]
  cases h : membership (m : ZMod n) <;> simp [h]

lemma prefixCount_mono {n : ℕ} (membership : ZMod n → Bool)
    {a b : ℕ} (hab : a ≤ b) : prefixCount membership a ≤ prefixCount membership b := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))

def counterWitness {n k : ℕ} (membership : ZMod n → Bool) : Signal n k → Bool :=
  fun s => decide (s.2.val + 1 ≤ prefixCount membership (s.1.val + 1))

lemma counterWitness_true_iff {n k : ℕ} (membership : ZMod n → Bool)
    (i : Fin n) (j : Fin k) :
    counterWitness membership (i, j) = true ↔
      j.val + 1 ≤ prefixCount membership (i.val + 1) := by
  simp [counterWitness]

lemma counterWitness_false_iff {n k : ℕ} (membership : ZMod n → Bool)
    (i : Fin n) (j : Fin k) :
    counterWitness membership (i, j) = false ↔
      prefixCount membership (i.val + 1) ≤ j.val := by
  simp [counterWitness]

lemma totalCount_eq {n : ℕ} [NeZero n] (membership : ZMod n → Bool) :
    prefixCount membership n =
      (Finset.univ.filter fun x => membership x).card := by
  unfold prefixCount
  apply Finset.card_bij
    (s := (Finset.range n).filter fun i : ℕ => membership (i : ZMod n) = true)
    (t := Finset.univ.filter fun x : ZMod n => membership x = true)
    (fun (i : ℕ) _ => (i : ZMod n))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] using this
  · intro x hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.val_lt, ?_⟩
    simpa [ZMod.natCast_zmod_val x] using (Finset.mem_filter.mp hx).2

lemma witness_satisfies {n k : ℕ} [NeZero n] (membership : ZMod n → Bool)
    (hcard : (Finset.univ.filter fun x => membership x).card ≤ k) :
    AtMostSat n k (combine membership (counterWitness membership)) := by
  by_cases hkn : k ≥ n
  · simp [AtMostSat, hkn]
  simp only [AtMostSat, hkn, ↓reduceIte]
  by_cases hk : k = 0
  · simp only [hk, dite_true]
    intro i
    by_contra hi
    have himem : membership (i.val : ZMod n) = true := by
      simpa [input, combine] using hi
    have hone : 1 ≤ prefixCount membership n := by
      have hlt : i.val < n := i.isLt
      have := prefixCount_mono membership (show i.val + 1 ≤ n by omega)
      rw [prefixCount_succ] at this
      simp [himem] at this
      omega
    rw [totalCount_eq] at hone
    omega
  simp only [hk, dite_false]
  have hn : n ≠ 0 := NeZero.ne n
  simp only [hn, dite_false]
  let zeroN : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let zeroK : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  let lastK : Fin k := ⟨k - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hinput
    simp only [input, combine] at hinput
    change membership (zeroN.val : ZMod n) = true at hinput
    simp only [zeroN] at hinput
    change counterWitness membership (zeroN, zeroK) = true
    rw [counterWitness_true_iff]
    have hz : membership (0 : ZMod n) = true := by simpa using hinput
    simp only [zeroN, zeroK, Fin.val_mk, zero_add]
    unfold prefixCount
    rw [Finset.one_le_card]
    exact ⟨0, by simp [hz]⟩
  · intro j hj
    change counterWitness membership (zeroN, j) = false
    rw [counterWitness_false_iff]
    have hc : prefixCount membership 1 ≤ 1 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [prefixCount])
    change prefixCount membership (0 + 1) ≤ j.val
    have hc' : prefixCount membership (0 + 1) ≤ 1 := by simpa using hc
    omega
  · intro i hi
    constructor
    · intro hinput
      change membership (i.val : ZMod n) = true at hinput
      change counterWitness membership (i, zeroK) = true
      rw [counterWitness_true_iff]
      rw [prefixCount_succ]
      simp [zeroK, hinput]
    · intro hprev
      change counterWitness membership (⟨i.val - 1, by omega⟩, zeroK) = true at hprev
      change counterWitness membership (i, zeroK) = true
      rw [counterWitness_true_iff] at hprev ⊢
      have hidx : (⟨i.val - 1, by omega⟩ : Fin n).val + 1 = i.val := by
        simp only [Fin.val_mk]
        omega
      simpa [zeroK, hidx] using hprev.trans (prefixCount_mono membership (by omega))
  · intro i hi j hj
    constructor
    · rintro ⟨hinput, hprev⟩
      change membership (i.val : ZMod n) = true at hinput
      change counterWitness membership
        (⟨i.val - 1, by omega⟩, ⟨j.val - 1, by omega⟩) = true at hprev
      change counterWitness membership (i, j) = true
      rw [counterWitness_true_iff] at hprev ⊢
      have hidx : (⟨i.val - 1, by omega⟩ : Fin n).val + 1 = i.val := by
        simp only [Fin.val_mk]
        omega
      have hjdx : (⟨j.val - 1, by omega⟩ : Fin k).val + 1 = j.val := by
        simp only [Fin.val_mk]
        omega
      rw [hidx, hjdx] at hprev
      rw [prefixCount_succ]
      simp [hinput]
      omega
    · intro hprev
      change counterWitness membership (⟨i.val - 1, by omega⟩, j) = true at hprev
      change counterWitness membership (i, j) = true
      rw [counterWitness_true_iff] at hprev ⊢
      have hidx : (⟨i.val - 1, by omega⟩ : Fin n).val + 1 = i.val := by
        simp only [Fin.val_mk]
        omega
      rw [hidx] at hprev
      exact hprev.trans (prefixCount_mono membership (by omega))
  · intro i hi hinput
    change membership (i.val : ZMod n) = true at hinput
    change counterWitness membership (⟨i.val - 1, by omega⟩, lastK) = false
    rw [counterWitness_false_iff]
    by_contra hnot
    have hidx : (⟨i.val - 1, by omega⟩ : Fin n).val + 1 = i.val := by
      simp only [Fin.val_mk]
      omega
    rw [hidx] at hnot
    have hprev : lastK.val + 1 ≤ prefixCount membership i.val := by omega
    have hbefore : k ≤ prefixCount membership i.val := by
      simp only [lastK, Fin.val_mk] at hprev
      omega
    have hnow : k + 1 ≤ prefixCount membership (i.val + 1) := by
      rw [prefixCount_succ]
      simp [hinput]
      omega
    have htotal := prefixCount_mono membership (show i.val + 1 ≤ n by omega)
    rw [totalCount_eq] at htotal
    omega

lemma forced_signal {n k : ℕ} (membership : ZMod n → Bool)
    (counter : Signal n k → Bool) (hn : n ≠ 0) (hk : k ≠ 0)
    (hinit : input (combine membership counter) ⟨0, Nat.pos_of_ne_zero hn⟩ = true →
      signal (combine membership counter) ⟨0, Nat.pos_of_ne_zero hn⟩
        ⟨0, Nat.pos_of_ne_zero hk⟩ = true)
    (hcol : ∀ i : Fin n, 0 < i.val →
      (input (combine membership counter) i = true →
        signal (combine membership counter) i ⟨0, Nat.pos_of_ne_zero hk⟩ = true) ∧
      (signal (combine membership counter) ⟨i.val - 1, by omega⟩
          ⟨0, Nat.pos_of_ne_zero hk⟩ = true →
        signal (combine membership counter) i ⟨0, Nat.pos_of_ne_zero hk⟩ = true))
    (hstep : ∀ i : Fin n, 0 < i.val → ∀ j : Fin k, 0 < j.val →
      (input (combine membership counter) i = true ∧
          signal (combine membership counter) ⟨i.val - 1, by omega⟩
            ⟨j.val - 1, by omega⟩ = true →
        signal (combine membership counter) i j = true) ∧
      (signal (combine membership counter) ⟨i.val - 1, by omega⟩ j = true →
        signal (combine membership counter) i j = true)) :
    ∀ i : Fin n, ∀ j : Fin k,
      j.val + 1 ≤ prefixCount membership (i.val + 1) → counter (i, j) = true := by
  intro i
  have main : ∀ m : ℕ, ∀ hmn : m < n, ∀ j : Fin k,
      j.val + 1 ≤ prefixCount membership (m + 1) →
        counter (⟨m, hmn⟩, j) = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn j hcount
      by_cases hm0 : m = 0
      · subst hm0
        have hc : prefixCount membership 1 ≤ 1 :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [prefixCount])
        have hcount' : j.val + 1 ≤ prefixCount membership 1 := by simpa using hcount
        have hj : j.val = 0 := by omega
        have hj0 : j = ⟨0, Nat.pos_of_ne_zero hk⟩ := Fin.ext hj
        subst hj0
        have hone : 1 ≤ prefixCount membership 1 := by simpa using hcount
        have hm : membership (0 : ZMod n) = true := by
          rw [prefixCount_succ] at hone
          simp [prefixCount] at hone
          cases hb : membership (0 : ZMod n) <;> simp [hb] at hone ⊢
        apply hinit
        simpa [input, combine] using hm
      · let cur : Fin n := ⟨m, hmn⟩
        let prev : Fin n := ⟨m - 1, by omega⟩
        have him : m - 1 < m := by omega
        have hi : 0 < cur.val := by simp [cur]; omega
        have ihprev := ih (m - 1) him (by omega)
        by_cases hm : membership (m : ZMod n) = true
        · by_cases hj : j.val = 0
          · have hj0 : j = ⟨0, Nat.pos_of_ne_zero hk⟩ := Fin.ext hj
            subst hj0
            exact (hcol cur hi).1 (by simpa [cur, input, combine] using hm)
          · have hprevCount : (j.val - 1) + 1 ≤ prefixCount membership m := by
              rw [prefixCount_succ] at hcount
              simp [hm] at hcount
              omega
            have hmnorm : m - 1 + 1 = m := by omega
            have hprev := ihprev ⟨j.val - 1, by omega⟩ (by rw [hmnorm]; exact hprevCount)
            exact (hstep cur hi j (by omega)).1
              ⟨by simpa [cur, input, combine] using hm,
                by simpa [cur, prev, signal, combine] using hprev⟩
        · have hprevCount : j.val + 1 ≤ prefixCount membership m := by
            rw [prefixCount_succ] at hcount
            simp [hm] at hcount
            simpa using hcount
          have hmnorm : m - 1 + 1 = m := by omega
          have hprev := ihprev j (by rw [hmnorm]; exact hprevCount)
          by_cases hj : j.val = 0
          · have hj0 : j = ⟨0, Nat.pos_of_ne_zero hk⟩ := Fin.ext hj
            subst hj0
            exact (hcol cur hi).2 (by simpa [cur, prev, signal, combine] using hprev)
          · exact (hstep cur hi j (by omega)).2
              (by simpa [cur, prev, signal, combine] using hprev)
  exact main i.val i.isLt

theorem atMostCorrect (n k : ℕ) [NeZero n] : AtMostCorrect n k := by
  intro membership
  constructor
  · rintro ⟨counter, hsat⟩
    by_cases hkn : k ≥ n
    · have hprefix : prefixCount membership n ≤ n :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [prefixCount])
      rw [totalCount_eq] at hprefix
      omega
    simp only [AtMostSat, hkn, ↓reduceIte] at hsat
    by_cases hk : k = 0
    · simp only [hk, dite_true] at hsat
      have hempty : (Finset.univ.filter fun x => membership x) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro x _
        have hx := hsat ⟨x.val, x.val_lt⟩
        simpa [input, combine, ZMod.natCast_zmod_val x] using hx
      rw [hempty]
      simp [hk]
    simp only [hk, dite_false] at hsat
    have hn : n ≠ 0 := NeZero.ne n
    simp only [hn, dite_false] at hsat
    rcases hsat with ⟨hinit, _, hcol, hstep, hoverflow⟩
    by_contra hle
    have htotal : k + 1 ≤ prefixCount membership n := by
      rw [totalCount_eq]
      omega
    let P : ℕ → Prop := fun t => k + 1 ≤ prefixCount membership t
    have hex : ∃ t, P t := ⟨n, htotal⟩
    let m := Nat.find hex
    have hmprop : k + 1 ≤ prefixCount membership m := Nat.find_spec hex
    have hmle : m ≤ n := Nat.find_min' hex htotal
    have hmpos : 0 < m := by
      by_contra hm
      have : m = 0 := by omega
      rw [this] at hmprop
      simp [prefixCount] at hmprop
    have hminimal : prefixCount membership (m - 1) < k + 1 := by
      apply Nat.lt_of_not_ge
      intro hbad
      exact Nat.find_min hex (show m - 1 < m by omega) hbad
    have hmtrue : membership (m - 1 : ℕ) = true := by
      have hstepCount := prefixCount_succ membership (m - 1)
      have hmnorm : m - 1 + 1 = m := by omega
      rw [hmnorm] at hstepCount
      cases hb : membership (m - 1 : ℕ) <;> simp [hb] at hstepCount hmprop ⊢
      omega
    have hbefore : k ≤ prefixCount membership (m - 1) := by
      have hstepCount := prefixCount_succ membership (m - 1)
      have hmnorm : m - 1 + 1 = m := by omega
      rw [hmnorm] at hstepCount
      simp [hmtrue] at hstepCount
      omega
    let current : Fin n := ⟨m - 1, by omega⟩
    have hcurrentPos : 0 < current.val := by
      simp only [current, Fin.val_mk]
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hprefixBound : prefixCount membership (m - 1) ≤ m - 1 :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [prefixCount])
      omega
    have hmTwo : 2 ≤ m := by
      change 0 < m - 1 at hcurrentPos
      omega
    let lastK : Fin k := ⟨k - 1, by omega⟩
    have hforced := forced_signal membership counter hn hk hinit hcol hstep
      ⟨m - 2, by omega⟩ lastK (by
        change k - 1 + 1 ≤ prefixCount membership (m - 2 + 1)
        have hidx : m - 2 + 1 = m - 1 := by omega
        have hkidx : k - 1 + 1 = k := by omega
        rw [hidx, hkidx]
        exact hbefore)
    have hover := hoverflow current hcurrentPos (by
      simp only [input, combine, current, Fin.val_mk]
      exact hmtrue)
    have : counter (⟨current.val - 1, by omega⟩, lastK) = false := by
      simpa [signal, combine] using hover
    have hforced' : counter (⟨current.val - 1, by omega⟩, lastK) = true := by
      simpa [current] using hforced
    exact Bool.noConfusion (hforced'.symm.trans this)
  · intro hcard
    exact ⟨counterWitness membership, witness_satisfies membership hcard⟩

lemma true_add_false_count {n : ℕ} [NeZero n] (membership : ZMod n → Bool) :
    (Finset.univ.filter fun x => membership x).card +
      (Finset.univ.filter fun x => !membership x).card = n := by
  have htotal := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (ZMod n))) (p := fun x => membership x = true)
  have hneg : (Finset.univ.filter fun x => ¬membership x = true) =
      Finset.univ.filter fun x => !membership x := by
    ext x
    cases membership x <;> simp
  rw [hneg] at htotal
  simpa [ZMod.card] using htotal

def exactCounterWitness {n k : ℕ} (membership : ZMod n → Bool) :
    ExactCounter n k → Bool
  | Sum.inl s => counterWitness membership s
  | Sum.inr s => counterWitness (fun x => !membership x) s

theorem exactCorrect_of_le (n k : ℕ) [NeZero n] (hkn : k ≤ n) : ExactCorrect n k := by
  intro membership
  constructor
  · rintro ⟨counter, hpos, hneg⟩
    have hpos' : (Finset.univ.filter fun x => membership x).card ≤ k :=
      (atMostCorrect n k membership).mp ⟨fun s => counter (Sum.inl s), by
        simpa [positiveAssignment, combine] using hpos⟩
    have hneg' : (Finset.univ.filter fun x => !membership x).card ≤ n - k :=
      (atMostCorrect n (n - k) (fun x => !membership x)).mp
        ⟨fun s => counter (Sum.inr s), by
          simpa [negativeAssignment, combine] using hneg⟩
    have htotal := true_add_false_count membership
    omega
  · intro hcard
    have hpos : (Finset.univ.filter fun x => membership x).card ≤ k := by omega
    have htotal := true_add_false_count membership
    have hneg : (Finset.univ.filter fun x => !membership x).card ≤ n - k := by omega
    refine ⟨exactCounterWitness membership, ?_, ?_⟩
    · simpa [positiveAssignment, exactCounterWitness, combine] using
        witness_satisfies membership hpos
    · simpa [negativeAssignment, exactCounterWitness, combine] using
        witness_satisfies (fun x => !membership x) hneg

theorem exactCorrect_counterexample : ¬ ExactCorrect 1 2 := by
  intro hcorrect
  let membership : ZMod 1 → Bool := fun _ => true
  have hposCard : (Finset.univ.filter fun x => membership x).card ≤ 2 := by
    simp [membership, ZMod.card]
  have hnegCard : (Finset.univ.filter fun x => !membership x).card ≤ 1 - 2 := by
    simp [membership]
  have hmodel : ∃ counter, ExactSat 1 2 (combine membership counter) := by
    refine ⟨exactCounterWitness membership, ?_, ?_⟩
    · simpa [positiveAssignment, exactCounterWitness, combine] using
        witness_satisfies membership hposCard
    · simpa [negativeAssignment, exactCounterWitness, combine] using
        witness_satisfies (fun x => !membership x) hnegCard
  have hcard := (hcorrect membership).mp hmodel
  simp [membership, ZMod.card] at hcard

#print axioms forced_signal
#print axioms atMostCorrect
#print axioms exactCorrect_of_le
#print axioms exactCorrect_counterexample
#print axioms BedertLab.SequentialCounter.tamperedTwo_control

end BedertLab.SequentialCounterProof
