/-
# Bedert lab, D1: the Two Families lemma for pairs (explicit constant)

The paper's Lemma at main.tex:574-582 (used three times in Prop 6's proof and
throughout our Lemma F): if P_1,...,P_k and Q_1,...,Q_k are set families with all
|P_i|, |Q_i| <= 2, each P_i disjoint from Q_i, and every cross pair (i,j), i /= j,
has P_i meeting Q_j or P_j meeting Q_i, then k is bounded by an absolute constant.

We freeze the explicit constant 63, derived by the tournament argument recorded in
candidates/bedert-omega/slack-probe/slack-table.md ("Choices" item 1) and
re-verified in the leg-1 blind analysis: orient each unordered cross pair {i,j} by
which of the two intersection conditions fails (if both hold, either orientation).
By the standard halving argument, every tournament on 2^6 = 64 vertices contains a
transitive subtournament (chain) on 7 vertices, and a 7-chain contradicts the skew
set-pair bound for size <= 2 sets (skew_seven_impossible below). The contrapositive
at 64 vertices gives k <= 63. The fill may use ANY correct elementary route to
k <= 63; if a different constant is forced, print BLOCKED rather than changing the
statement.

This lemma is also a candidate for eventual Mathlib contribution (generalized).

FROZEN STATEMENT: fill the sorry only; do not alter the statement. BLOCKED if
unprovable as written.
-/
import Mathlib

namespace BedertLab

private theorem tournament_chain {β : Type*} [DecidableEq β]
    (R : β → β → Prop) [DecidableRel R]
    (htournament : ∀ ⦃x y⦄, x ≠ y → R x y ∨ R y x)
    (n : ℕ) (S : Finset β) (hcard : 2 ^ n ≤ S.card) :
    ∃ l : List β,
      l.length = n + 1 ∧
      (∀ x ∈ l, x ∈ S) ∧
      l.Pairwise R := by
  induction n generalizing S with
  | zero =>
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hv⟩ := hS
      exact ⟨[v], by simp, by simpa, by simp⟩
  | succ n ih =>
      have hS : S.Nonempty := Finset.card_pos.mp (by
        have : 0 < 2 ^ (n + 1) := by positivity
        omega)
      obtain ⟨v, hv⟩ := hS
      let T := S.erase v
      let A := T.filter (R v)
      let B := T.filter fun w ↦ ¬ R v w
      have hTcard : T.card + 1 = S.card := by
        simpa [T] using Finset.card_erase_add_one hv
      have hsplit : A.card + B.card = T.card := by
        simpa [A, B] using
          (Finset.card_filter_add_card_filter_not (s := T) (p := R v))
      have hlarge : 2 ^ n ≤ A.card ∨ 2 ^ n ≤ B.card := by
        rw [pow_succ] at hcard
        omega
      rcases hlarge with hA | hB
      · obtain ⟨l, hlen, hmem, hpw⟩ := ih A hA
        refine ⟨v :: l, by simp [hlen], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hv
          · exact Finset.erase_subset _ _ (Finset.filter_subset _ _ (hmem x hx))
        · rw [List.pairwise_cons]
          refine ⟨?_, hpw⟩
          intro x hx
          exact (Finset.mem_filter.mp (hmem x hx)).2
      · obtain ⟨l, hlen, hmem, hpw⟩ := ih B hB
        refine ⟨l ++ [v], by simp [hlen], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact Finset.erase_subset _ _ (Finset.filter_subset _ _ (hmem x hx))
          · exact hv
        · rw [List.pairwise_append]
          refine ⟨hpw, by simp, ?_⟩
          intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst y
          have hxB := Finset.mem_filter.mp (hmem x hx)
          have hxne : x ≠ v := by
            exact (Finset.mem_erase.mp hxB.1).1
          exact (htournament hxne).resolve_right hxB.2

private theorem cover_pair_with_dummy {α : Type*} [DecidableEq α]
    (dummy : Option (Option α))
    (hdummy : ∀ x : α, dummy ≠ some (some x))
    (s : Finset α) (hcard : s.card ≤ 2) :
    ∃ a b : Option (Option α),
      (∀ x ∈ s, some (some x) = a ∨ some (some x) = b) ∧
      (a = dummy ∨ ∃ x ∈ s, a = some (some x)) ∧
      (b = dummy ∨ ∃ x ∈ s, b = some (some x)) := by
  interval_cases hs : s.card
  · have hempty : s = ∅ := Finset.card_eq_zero.mp hs
    subst s
    exact ⟨dummy, dummy, by simp⟩
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs
    exact ⟨some (some x), dummy, by simp [hdummy]⟩
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
    exact ⟨some (some x), some (some y), by simp [hxy]⟩

private theorem left_rep_ne_right_rep {α : Type*} [DecidableEq α]
    {P Q : Finset α} (hdisj : Disjoint P Q)
    {p q : Option (Option α)}
    (hp : p = none ∨ ∃ x ∈ P, p = some (some x))
    (hq : q = some none ∨ ∃ y ∈ Q, q = some (some y)) :
    p ≠ q := by
  rcases hp with rfl | ⟨x, hx, rfl⟩ <;>
    rcases hq with rfl | ⟨y, hy, rfl⟩
  · simp
  · simp
  · simp
  · intro hpq
    have hxy : x = y := Option.some.inj (Option.some.inj hpq)
    exact hdisj.forall_ne_finset hx hy hxy

open Matrix

private theorem seven_vectors_not_skew
    (c e : Fin 7 → Fin 6 → ℚ)
    (hzero : ∀ i j : Fin 7, i < j → c i ⬝ᵥ e j = 0)
    (hdiag : ∀ i : Fin 7, c i ⬝ᵥ e i ≠ 0) :
    False := by
  have hli : LinearIndependent ℚ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum
    have hp (j : Fin 7) :
        ∑ i, g i * (c i ⬝ᵥ e j) = 0 := by
      have h := congrArg (fun v : Fin 6 → ℚ ↦ v ⬝ᵥ e j) hsum
      simpa only [sum_dotProduct, smul_dotProduct, smul_eq_mul,
        zero_dotProduct] using h
    have hp' (j : Fin 7) :
        g 0 * (c 0 ⬝ᵥ e j) +
          (g 1 * (c 1 ⬝ᵥ e j) +
          (g 2 * (c 2 ⬝ᵥ e j) +
          (g 3 * (c 3 ⬝ᵥ e j) +
          (g 4 * (c 4 ⬝ᵥ e j) +
          (g 5 * (c 5 ⬝ᵥ e j) +
            g 6 * (c 6 ⬝ᵥ e j)))))) = 0 := by
      have h := hp j
      simpa [Fin.sum_univ_succ] using h
    have hg6 : g 6 = 0 := by
      have h := hp' 6
      simp [hzero] at h
      exact h.resolve_right (hdiag 6)
    have hg5 : g 5 = 0 := by
      have h := hp' 5
      simp [hzero, hg6] at h
      exact h.resolve_right (hdiag 5)
    have hg4 : g 4 = 0 := by
      have h := hp' 4
      simp [hzero, hg6, hg5] at h
      exact h.resolve_right (hdiag 4)
    have hg3 : g 3 = 0 := by
      have h := hp' 3
      simp [hzero, hg6, hg5, hg4] at h
      exact h.resolve_right (hdiag 3)
    have hg2 : g 2 = 0 := by
      have h := hp' 2
      simp [hzero, hg6, hg5, hg4, hg3] at h
      exact h.resolve_right (hdiag 2)
    have hg1 : g 1 = 0 := by
      have h := hp' 1
      simp [hzero, hg6, hg5, hg4, hg3, hg2] at h
      exact h.resolve_right (hdiag 1)
    have hg0 : g 0 = 0 := by
      have h := hp' 0
      simp [hg6, hg5, hg4, hg3, hg2, hg1] at h
      exact h.resolve_right (hdiag 0)
    intro i
    fin_cases i <;> assumption
  have hcard := hli.fintype_card_le_finrank
  norm_num at hcard

private def resultantCoeff (x y : ℚ) : Fin 6 → ℚ :=
  ![x ^ 2 * y ^ 2, -(x ^ 2 * y + x * y ^ 2), x ^ 2 + y ^ 2,
    x * y, -(x + y), 1]

private def resultantEval (z w : ℚ) : Fin 6 → ℚ :=
  let u := z + w
  let v := z * w
  ![1, u, v, u ^ 2, u * v, v ^ 2]

private theorem resultant_dot (x y z w : ℚ) :
    resultantCoeff x y ⬝ᵥ resultantEval z w =
      (x - z) * (x - w) * (y - z) * (y - w) := by
  simp [resultantCoeff, resultantEval, dotProduct, Fin.sum_univ_succ]
  ring

private theorem equality_model_impossible {α : Type*}
    (a b c d : Fin 7 → α)
    (hdisj : ∀ i, a i ≠ c i ∧ a i ≠ d i ∧ b i ≠ c i ∧ b i ≠ d i)
    (hchain : ∀ i j : Fin 7, i < j →
      a i = c j ∨ a i = d j ∨ b i = c j ∨ b i = d j) :
    False := by
  classical
  let U : Finset α :=
    Finset.univ.biUnion fun i : Fin 7 ↦ {a i, b i, c i, d i}
  have ha : ∀ i, a i ∈ U := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hb : ∀ i, b i ∈ U := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hc : ∀ i, c i ∈ U := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hd : ∀ i, d i ∈ U := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hUcard : U.card ≤ 32 := by
    calc
      U.card ≤ Finset.univ.card * 4 := by
        apply Finset.card_biUnion_le_card_mul
        intro i hi
        exact Finset.card_le_four
      _ ≤ 32 := by norm_num
  let E : U ↪ Fin 32 :=
    (U.equivFin.toEmbedding).trans
      ⟨Fin.castLE hUcard, Fin.castLE_injective hUcard⟩
  let val : U → ℚ := fun x ↦ (E x : ℚ)
  have hval_inj : Function.Injective val := by
    intro x y hxy
    apply E.injective
    change ((E x : Fin 32) : ℚ) = (E y : ℚ) at hxy
    apply Fin.ext
    exact_mod_cast hxy
  let aa : Fin 7 → ℚ := fun i ↦ val ⟨a i, ha i⟩
  let bb : Fin 7 → ℚ := fun i ↦ val ⟨b i, hb i⟩
  let cc : Fin 7 → ℚ := fun i ↦ val ⟨c i, hc i⟩
  let dd : Fin 7 → ℚ := fun i ↦ val ⟨d i, hd i⟩
  let coeff : Fin 7 → Fin 6 → ℚ :=
    fun i ↦ resultantCoeff (aa i) (bb i)
  let eval : Fin 7 → Fin 6 → ℚ :=
    fun i ↦ resultantEval (cc i) (dd i)
  apply seven_vectors_not_skew coeff eval
  · intro i j hij
    rw [resultant_dot]
    rcases hchain i j hij with h | h | h | h
    · have hs : aa i = cc j := congrArg val (Subtype.ext h)
      rw [hs]
      ring
    · have hs : aa i = dd j := congrArg val (Subtype.ext h)
      rw [hs]
      ring
    · have hs : bb i = cc j := congrArg val (Subtype.ext h)
      rw [hs]
      ring
    · have hs : bb i = dd j := congrArg val (Subtype.ext h)
      rw [hs]
      ring
  · intro i
    rw [resultant_dot]
    have hac : aa i ≠ cc i := by
      intro heq
      exact (hdisj i).1 (congrArg Subtype.val (hval_inj heq))
    have had : aa i ≠ dd i := by
      intro heq
      exact (hdisj i).2.1 (congrArg Subtype.val (hval_inj heq))
    have hbc : bb i ≠ cc i := by
      intro heq
      exact (hdisj i).2.2.1 (congrArg Subtype.val (hval_inj heq))
    have hbd : bb i ≠ dd i := by
      intro heq
      exact (hdisj i).2.2.2 (congrArg Subtype.val (hval_inj heq))
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (sub_ne_zero.mpr hac) (sub_ne_zero.mpr had))
      (sub_ne_zero.mpr hbc)) (sub_ne_zero.mpr hbd)

private theorem skew_seven_impossible {α : Type*} [DecidableEq α]
    (P Q : Fin 7 → Finset α)
    (hP : ∀ i, (P i).card ≤ 2)
    (hQ : ∀ i, (Q i).card ≤ 2)
    (hdisj : ∀ i, Disjoint (P i) (Q i))
    (hchain : ∀ i j : Fin 7, i < j → ¬ Disjoint (P i) (Q j)) :
    False := by
  choose pa pb hPcover using fun i ↦
    cover_pair_with_dummy none (by simp) (P i) (hP i)
  choose qa qb hQcover using fun i ↦
    cover_pair_with_dummy (some none) (by simp) (Q i) (hQ i)
  apply equality_model_impossible pa pb qa qb
  · intro i
    exact ⟨
      left_rep_ne_right_rep (hdisj i) (hPcover i).2.1 (hQcover i).2.1,
      left_rep_ne_right_rep (hdisj i) (hPcover i).2.1 (hQcover i).2.2,
      left_rep_ne_right_rep (hdisj i) (hPcover i).2.2 (hQcover i).2.1,
      left_rep_ne_right_rep (hdisj i) (hPcover i).2.2 (hQcover i).2.2⟩
  · intro i j hij
    obtain ⟨x, hxi, hxj⟩ := Finset.not_disjoint_iff.mp (hchain i j hij)
    rcases (hPcover i).1 x hxi with hpa | hpb <;>
      rcases (hQcover j).1 x hxj with hqa | hqb
    · exact Or.inl (hpa.symm.trans hqa)
    · exact Or.inr (Or.inl (hpa.symm.trans hqb))
    · exact Or.inr (Or.inr (Or.inl (hpb.symm.trans hqa)))
    · exact Or.inr (Or.inr (Or.inr (hpb.symm.trans hqb)))

/-- Two Families lemma, pairs case, explicit constant 63: families of sets of
size at most 2 over any type, componentwise disjoint, with the skew
cross-intersection condition, have at most 63 members. -/
theorem two_families_pairs {α : Type*} [DecidableEq α] {k : ℕ}
    (P Q : Fin k → Finset α)
    (hP : ∀ i, (P i).card ≤ 2) (hQ : ∀ i, (Q i).card ≤ 2)
    (hdisj : ∀ i, Disjoint (P i) (Q i))
    (hcross : ∀ i j, i ≠ j →
      ¬ Disjoint (P i) (Q j) ∨ ¬ Disjoint (P j) (Q i)) :
    k ≤ 63 := by
  by_contra hk
  have hk64 : 64 ≤ k := by omega
  let R : Fin k → Fin k → Prop :=
    fun i j ↦ ¬ Disjoint (P i) (Q j)
  have htournament : ∀ ⦃i j⦄, i ≠ j → R i j ∨ R j i := by
    intro i j hij
    exact hcross i j hij
  obtain ⟨l, hlen, hmem, hpw⟩ :=
    tournament_chain R htournament 6 Finset.univ (by simpa using hk64)
  have hlen7 : l.length = 7 := by omega
  let e : Fin 7 → Fin k := fun i ↦ l.get (Fin.cast hlen7.symm i)
  apply skew_seven_impossible
      (fun i ↦ P (e i)) (fun i ↦ Q (e i))
  · intro i
    exact hP (e i)
  · intro i
    exact hQ (e i)
  · intro i
    exact hdisj (e i)
  · intro i j hij
    have hcast :
        Fin.cast hlen7.symm i < Fin.cast hlen7.symm j := by
      simpa using hij
    simpa [R, e] using hpw.rel_get_of_lt hcast

#print axioms two_families_pairs

end BedertLab
