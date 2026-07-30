/-
# Bedert lab, Milestone 1: the abstract iteration bound

This file isolates the last analytic step of the iteration.  The iteration
supplies a terminal size, a growth bound, and a cap on its number of steps.
The only specialization-specific ingredient is an `inverseLower` certificate:
every natural index at which `g` exceeds `log₂ thr` must exceed that lower
bound.  This avoids choosing a notion of inverse for an arbitrary `g` while
making changes to `g`, `thr`, or `stepCap` propagate mechanically.
-/
import Mathlib

namespace BedertLab

/-! ## Phase 1: the parameterized derivation -/

/-- The abstract terminal-step argument.

`inverseLower` is an ergonomic lower inverse certificate for `g` at
`log₂ thr`.  No monotonicity or global inverse for `g` is required: an
instantiation proves exactly the implication it needs. -/
theorem abstract_bound
    (g : ℕ → ℝ) (thr : ℝ) (stepCap : ℝ → ℝ)
    {terminalSize K : ℝ} {j : ℕ} (inverseLower : ℝ)
    (hthr : 0 < thr)
    (hterminal : thr < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤ g j)
    (hsteps : (j : ℝ) ≤ stepCap K)
    (hinverse : ∀ n : ℕ, Real.logb 2 thr < g n → inverseLower < (n : ℝ)) :
    inverseLower < stepCap K := by
  have hterminal_pos : 0 < terminalSize := lt_trans hthr hterminal
  have hlog : Real.log thr < Real.log terminalSize := by
    exact Real.strictMonoOn_log hthr hterminal_pos hterminal
  have hlogb : Real.logb 2 thr < Real.logb 2 terminalSize := by
    rw [Real.logb, Real.logb]
    have hlog_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact (div_lt_div_iff₀ hlog_two hlog_two).2
      (mul_lt_mul_of_pos_right hlog hlog_two)
  have hj : inverseLower < (j : ℝ) :=
    hinverse j (lt_of_lt_of_le hlogb hgrowth)
  exact lt_of_lt_of_le hj hsteps

/-! ## Phase 2: Bedert's original growth `g(j) = 3^j` -/

/-- Bedert's published square-root-of-triple-log conclusion, in explicit
inequality form.  Here `terminalSize` is `|S_j|`, `thr = log₂ p`, and the
step cap is `36 K²`.

The mild scale assumption says `log₂(log₂ p) > 1`; it makes all logs
and square roots in the displayed lower bound positive. -/
theorem bedert_original
    {p terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hscale : 1 < Real.logb 2 (Real.logb 2 p))
    (hterminal : Real.logb 2 p < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤ (3 : ℝ) ^ j)
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 0 ≤ K) :
    Real.sqrt
        (Real.log (Real.logb 2 (Real.logb 2 p)) / Real.log 3) / 6 < K := by
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  let B : ℝ := Real.log M / Real.log 3
  have hM : 1 < M := hscale
  have hM_pos : 0 < M := lt_trans (by norm_num) hM
  have hlogM_pos : 0 < Real.log M := Real.log_pos hM
  have hlog_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact (div_pos hlogM_pos hlog_three_pos).le
  have hinverse : ∀ n : ℕ, M < (3 : ℝ) ^ n → B < (n : ℝ) := by
    intro n hn
    have hpow_pos : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) n
    have hlog : Real.log M < Real.log ((3 : ℝ) ^ n) := by
      exact Real.strictMonoOn_log hM_pos hpow_pos hn
    rw [Real.log_pow] at hlog
    dsimp [B]
    exact (div_lt_iff₀ hlog_three_pos).2 hlog
  have hB : B < 36 * K ^ 2 := by
    apply abstract_bound
        (g := fun n : ℕ ↦ (3 : ℝ) ^ n)
        (thr := Real.logb 2 p)
        (stepCap := fun x : ℝ ↦ 36 * x ^ 2)
        (inverseLower := B)
        hthr hterminal hgrowth hsteps
    simpa [M] using hinverse
  have hsqrt_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  dsimp [B] at hB_nonneg hsqrt_sq hsqrt_nonneg hB ⊢
  nlinarith

/-! ## Phase 3: quadratic bookkeeping growth -/

/-- The improved fourth-root-of-double-log conclusion, again as an explicit
inequality.  The inverse certificate uses the exact shifted expression

`0.4 * (sqrt (2.5 M) - 1.25)^2 + (sqrt (2.5 M) - 1.25) = M - 0.625`,

so it does not make the false claim that `g(j) > M` forces
`j ≥ sqrt (2.5 M)`. -/
theorem our_improvement
    {p terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hscale : 1 ≤ Real.logb 2 (Real.logb 2 p))
    (hterminal : Real.logb 2 p < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤
      0.4 * (j : ℝ) ^ 2 + (j : ℝ))
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 0 ≤ K) :
    Real.sqrt
        (Real.sqrt (2.5 * Real.logb 2 (Real.logb 2 p)) - 1.25) / 6 < K := by
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  let x : ℝ := Real.sqrt (2.5 * M) - 1.25
  have hM : 1 ≤ M := hscale
  have hrad : 0 ≤ 2.5 * M := by positivity
  have hsqrt_sq : (Real.sqrt (2.5 * M)) ^ 2 = 2.5 * M := Real.sq_sqrt hrad
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2.5 * M) := Real.sqrt_nonneg _
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    nlinarith
  have hx_eval : 0.4 * x ^ 2 + x = M - 0.625 := by
    dsimp [x]
    nlinarith
  have hinverse : ∀ n : ℕ,
      M < 0.4 * (n : ℝ) ^ 2 + (n : ℝ) → x < (n : ℝ) := by
    intro n hn
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_contra hnot
    have hn_le : (n : ℝ) ≤ x := le_of_not_gt hnot
    have hprod : 0 ≤ ((n : ℝ) + x) * (x - (n : ℝ)) :=
      mul_nonneg (add_nonneg hn_nonneg hx_nonneg) (sub_nonneg.mpr hn_le)
    nlinarith
  have hx : x < 36 * K ^ 2 := by
    apply abstract_bound
        (g := fun n : ℕ ↦ 0.4 * (n : ℝ) ^ 2 + (n : ℝ))
        (thr := Real.logb 2 p)
        (stepCap := fun y : ℝ ↦ 36 * y ^ 2)
        (inverseLower := x)
        hthr hterminal hgrowth hsteps
    simpa [M] using hinverse
  have houter_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
  have houter_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  dsimp [x, M] at hx_nonneg houter_sq houter_nonneg hx ⊢
  nlinarith

/-! ## Phase 4: trust audit -/

#print axioms abstract_bound
#print axioms bedert_original
#print axioms our_improvement

end BedertLab
