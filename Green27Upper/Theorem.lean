import FormalConjectures.GreensOpenProblems.«27»
import Green27Upper.StrausSet

/-!
# Bedert's upper bound $m(p) \ll (\log p)^2$

This file proves `green_27.variants.upper_be23` from the Formal Conjectures repository,
stated there as a `sorry` in `FormalConjectures/GreensOpenProblems/27.lean`.

The definitions `m`, `primesAtTop` and `upperBest` are imported from that repository
rather than restated here, so the statement below is the upstream statement verbatim.

The route is Łuczak-Schoen: Straus's simple set, Lemmas 4 and 5, and the Q = 2 combine.

References:
- [Be23] Bedert, Benjamin. "On unique sums in Abelian groups." Combinatorica 44.2 (2024): 269-298.
- [LS08] Łuczak, Tomasz and Schoen, Tomasz. "On the number of unique sums."
- [St76] Straus, E. G. "Differences of residues (mod p)." Journal of Number Theory 8.1 (1976): 40-42.
-/

open Asymptotics Filter UniqueSums

namespace Green27

/-- Upper bound: $m(p) \ll (\log p)^2$ [Be23, Theorem 5]. -/
theorem upper_be23_proof :
    m =O[primesAtTop] upperBest := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨36, ?_⟩
  rw [primesAtTop, Filter.eventually_inf_principal]
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 30)] with p hpN hpprime
  letI : Fact p.Prime := ⟨hpprime⟩
  have hsize : ((strausSet p).card ^ 2) ^ 2 < p := strausSet_size_gate hpN
  rcases exists_hasNoUniqueRepresentation_card_le (by omega) hsize with
    ⟨A, hA2, hAnur, hAcard⟩
  have hbdd : BddBelow
      { (B.card : ℝ) | (B : Finset (ZMod p)) (_ : 2 ≤ B.card)
        (_ : HasNoUniqueRepresentation B) } := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨B, _, _, rfl⟩
    positivity
  have hmem : (A.card : ℝ) ∈
      { (B.card : ℝ) | (B : Finset (ZMod p)) (_ : 2 ≤ B.card)
        (_ : HasNoUniqueRepresentation B) } := ⟨A, hA2, hAnur, rfl⟩
  have hm_le : m p ≤ (A.card : ℝ) := by
    rw [m]
    exact csInf_le hbdd hmem
  have hm_nonneg : 0 ≤ m p := by
    rw [m]
    apply Real.sInf_nonneg
    intro y hy
    rcases hy with ⟨B, _, _, rfl⟩
    positivity
  have hAcardR : (A.card : ℝ) ≤ (2 * (Nat.log 2 p : ℝ) + 1) ^ 2 := by
    exact_mod_cast hAcard
  rw [Real.norm_of_nonneg hm_nonneg, upperBest,
    Real.norm_of_nonneg (sq_nonneg (Real.log (p : ℝ)))]
  exact hm_le.trans (hAcardR.trans (natLog_sq_bound (by omega)))

end Green27
