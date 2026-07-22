/-
# Bedert lab, Milestone "pricing": what would improving each parameter be worth?

SPEC.md Milestone 3. Each theorem below varies EXACTLY ONE parameter of the
baseline chain (`our_improvement` in Abstract.lean: growth `g j = 0.4 j^2 + j`,
threshold `thr = log₂ p`, step cap `stepCap K = 36 K^2`) and reads off the
resulting lower bound on `K` from `abstract_bound`.

The hypothetical iteration facts are HYPOTHESES of each theorem (not sorries):
each statement says "IF the iteration delivered this parameter, THEN K obeys
this bound". The derivations themselves are kernel-checked, so the pricing
table cannot lie about the arithmetic.

Every scenario keeps the baseline's `hthr : 0 < log₂ p` (as in
`our_improvement`).  It is NOT derivable from `hscale`: Mathlib's
`Real.log x = Real.log |x|` convention means `log₂ log₂ p ≥ 1` is also
satisfied by e.g. `p = 1/4` (where `log₂ p = -2`), and dropping `hthr`
makes the statements false — caught by a Lean-checked counterexample
during the first fill attempt (2026-07-23).

Pricing table (M := log₂ log₂ p; baseline conclusion K > √(√(2.5·M) − 1.25)/6,
i.e. K ≫ (log log p)^{1/4}):

| Scenario                     | Varied parameter        | Resulting bound              | Verdict   |
|------------------------------|-------------------------|------------------------------|-----------|
| `pricing_thr_squared`        | thr = (log₂ p)^2        | K > √(√(5·M) − 1.25)/6       | ~worthless: only a ⁴√2 factor |
| `pricing_stepCap_linearized` | stepCap K = K^(1+ε)     | K > x^(1/(1+ε)), x ≈ √(2.5M) | large: → (log log p)^{1/2−o(1)} |
| `pricing_growth_jlogj`       | g j = j·log₂ j          | K > √(M/log₂ M)/6            | large: ≈ (log log p)^{1/2} up to log |
| `pricing_growth_linear`      | g j = j                 | K > √M/6                     | ceiling of this chain: (log log p)^{1/2} |

FROZEN STATEMENTS: the four theorem statements below are trust boundaries.
Fill the `sorry` proof bodies only; do NOT alter any statement, hypothesis, or
definition. If a statement cannot be proved as written, print
`BLOCKED: <reason>` and stop.
-/
import BedertLab.Abstract

namespace BedertLab

/-! ## Scenario 1: better rectification threshold, `thr = (log₂ p)^2`

What if GAP-contained sets rectified up to size `(log₂ p)^2` instead of
`log₂ p`?  Growth and step cap stay at baseline. -/

/-- Pricing: threshold `(log₂ p)^2`, baseline growth `0.4 j^2 + j`, baseline
step cap `36 K^2`.  The bound improves only from `√(2.5·M)` to `√(5·M)`
inside the fourth root: a factor `2^{1/4}` on `K`.  Verdict: nearly
worthless. -/
theorem pricing_thr_squared
    {p terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hscale : 1 ≤ Real.logb 2 (Real.logb 2 p))
    (hterminal : (Real.logb 2 p) ^ 2 < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤
      0.4 * (j : ℝ) ^ 2 + (j : ℝ))
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 0 ≤ K) :
    Real.sqrt
        (Real.sqrt (5 * Real.logb 2 (Real.logb 2 p)) - 1.25) / 6 < K := by
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  let x : ℝ := Real.sqrt (5 * M) - 1.25
  have hM : 1 ≤ M := hscale
  have hrad : 0 ≤ 5 * M := by positivity
  have hsqrt_sq : (Real.sqrt (5 * M)) ^ 2 = 5 * M := Real.sq_sqrt hrad
  have hsqrt_nonneg : 0 ≤ Real.sqrt (5 * M) := Real.sqrt_nonneg _
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    nlinarith
  have hx_eval : 0.4 * x ^ 2 + x = 2 * M - 0.625 := by
    dsimp [x]
    nlinarith
  have hlogb_sq : Real.logb 2 ((Real.logb 2 p) ^ 2) = 2 * M := by
    dsimp [M, Real.logb]
    rw [Real.log_pow]
    ring
  have hinverse : ∀ n : ℕ,
      2 * M < 0.4 * (n : ℝ) ^ 2 + (n : ℝ) → x < (n : ℝ) := by
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
        (thr := (Real.logb 2 p) ^ 2)
        (stepCap := fun y : ℝ ↦ 36 * y ^ 2)
        (inverseLower := x)
        (sq_pos_of_pos hthr) hterminal hgrowth hsteps
    rw [hlogb_sq]
    exact hinverse
  have houter_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
  have houter_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  dsimp [x, M] at hx_nonneg houter_sq houter_nonneg hx ⊢
  nlinarith

/-! ## Scenario 2: linearized increment, `stepCap K = K^(1+ε)`

What if the density increment argument could be linearised, so the iteration
must stop within `K^{1+ε}` steps instead of `36 K^2`?  Growth and threshold
stay at baseline. -/

/-- Pricing: step cap `K^(1+ε)`, baseline growth and threshold.  The
baseline's inverse certificate `x = √(2.5·M) − 1.25` now bounds `K^(1+ε)`
from below, so `K > x^(1/(1+ε))`: the exponent on `log log p` climbs from
`1/4` toward `1/2`.  Verdict: large. -/
theorem pricing_stepCap_linearized
    {p terminalSize K ε : ℝ} {j : ℕ}
    (hε : 0 < ε)
    (hthr : 0 < Real.logb 2 p)
    (hscale : 1 ≤ Real.logb 2 (Real.logb 2 p))
    (hterminal : Real.logb 2 p < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤
      0.4 * (j : ℝ) ^ 2 + (j : ℝ))
    (hsteps : (j : ℝ) ≤ K ^ (1 + ε))
    (hK : 0 ≤ K) :
    (Real.sqrt (2.5 * Real.logb 2 (Real.logb 2 p)) - 1.25)
        ^ ((1 : ℝ) / (1 + ε)) < K := by
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
  have hx : x < K ^ (1 + ε) := by
    apply abstract_bound
        (g := fun n : ℕ ↦ 0.4 * (n : ℝ) ^ 2 + (n : ℝ))
        (thr := Real.logb 2 p)
        (stepCap := fun y : ℝ ↦ y ^ (1 + ε))
        (inverseLower := x)
        hthr hterminal hgrowth hsteps
    change ∀ n : ℕ,
      M < 0.4 * (n : ℝ) ^ 2 + (n : ℝ) → x < (n : ℝ)
    exact hinverse
  have hexponent_pos : 0 < (1 : ℝ) / (1 + ε) := by positivity
  have hpowered :
      x ^ ((1 : ℝ) / (1 + ε)) <
        (K ^ (1 + ε)) ^ ((1 : ℝ) / (1 + ε)) :=
    Real.rpow_lt_rpow hx_nonneg hx hexponent_pos
  have hcollapse :
      (K ^ (1 + ε)) ^ ((1 : ℝ) / (1 + ε)) = K := by
    calc
      (K ^ (1 + ε)) ^ ((1 : ℝ) / (1 + ε)) =
          K ^ ((1 + ε) * ((1 : ℝ) / (1 + ε))) :=
        (Real.rpow_mul hK _ _).symm
      _ = K ^ (1 : ℝ) := by
        congr 1
        field_simp
      _ = K := Real.rpow_one K
  rw [hcollapse] at hpowered
  simpa [x, M] using hpowered

/-! ## Scenario 3: tamer growth, `g j = j · log₂ j`

What if the container bookkeeping grew quasi-linearly instead of
quadratically?  Threshold and step cap stay at baseline. -/

/-- Pricing: growth `j · log₂ j`, baseline threshold and step cap.  The
inverse certificate is `M / log₂ M`: if `n · log₂ n > M` then either
`n ≤ M` (so `log₂ n ≤ log₂ M` forces `n > M / log₂ M`) or `n > M` outright.
Verdict: large, `K ≫ (log log p / log log log p)^{1/2}`. -/
theorem pricing_growth_jlogj
    {p terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hscale : 2 ≤ Real.logb 2 (Real.logb 2 p))
    (hterminal : Real.logb 2 p < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤
      (j : ℝ) * Real.logb 2 (j : ℝ))
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 0 ≤ K) :
    Real.sqrt
        (Real.logb 2 (Real.logb 2 p) /
          Real.logb 2 (Real.logb 2 (Real.logb 2 p))) / 6 < K := by
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  let L : ℝ := Real.logb 2 M
  let x : ℝ := M / L
  have hM : 2 ≤ M := hscale
  have hM_nonneg : 0 ≤ M := by linarith
  have hM_pos : 0 < M := by linarith
  have hL_one : 1 ≤ L := by
    dsimp [L]
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (b := 2) (x := 2) (y := M)
      (by norm_num) (by norm_num) hM
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_one
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hinverse : ∀ n : ℕ,
      M < (n : ℝ) * Real.logb 2 (n : ℝ) → x < (n : ℝ) := by
    intro n hn
    by_cases hnM : (n : ℝ) ≤ M
    · have hn_pos : 0 < (n : ℝ) := by
        by_contra hnot
        have hn_zero : (n : ℝ) = 0 :=
          le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg n)
        rw [hn_zero] at hn
        simp only [zero_mul] at hn
        linarith
      have hlog_le : Real.logb 2 (n : ℝ) ≤ L := by
        dsimp [L]
        exact Real.logb_le_logb_of_le (by norm_num) hn_pos hnM
      have hprod_le :
          (n : ℝ) * Real.logb 2 (n : ℝ) ≤ (n : ℝ) * L :=
        mul_le_mul_of_nonneg_left hlog_le hn_pos.le
      dsimp [x]
      exact (div_lt_iff₀ hL_pos).2 (lt_of_lt_of_le hn hprod_le)
    · have hx_le_M : x ≤ M := by
        dsimp [x]
        exact div_le_self hM_nonneg hL_one
      exact lt_of_le_of_lt hx_le_M (lt_of_not_ge hnM)
  have hx : x < 36 * K ^ 2 := by
    apply abstract_bound
        (g := fun n : ℕ ↦ (n : ℝ) * Real.logb 2 (n : ℝ))
        (thr := Real.logb 2 p)
        (stepCap := fun y : ℝ ↦ 36 * y ^ 2)
        (inverseLower := x)
        hthr hterminal hgrowth hsteps
    change ∀ n : ℕ,
      M < (n : ℝ) * Real.logb 2 (n : ℝ) → x < (n : ℝ)
    exact hinverse
  have houter_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
  have houter_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  dsimp [x, L, M] at hx_nonneg houter_sq houter_nonneg hx ⊢
  nlinarith

/-! ## Scenario 4: linear growth, `g j = j`

The limiting case: container size doubling once per step, the tamest growth
this chain admits. -/

/-- Pricing: growth `j`, baseline threshold and step cap.  The inverse
certificate is `M` itself, giving `K > √M / 6`: the ceiling of what ANY
growth improvement can deliver while the step cap stays quadratic.
Verdict: `K ≫ (log log p)^{1/2}` and no growth improvement can beat it. -/
theorem pricing_growth_linear
    {p terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hscale : 1 ≤ Real.logb 2 (Real.logb 2 p))
    (hterminal : Real.logb 2 p < terminalSize)
    (hgrowth : Real.logb 2 terminalSize ≤ (j : ℝ))
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 0 ≤ K) :
    Real.sqrt (Real.logb 2 (Real.logb 2 p)) / 6 < K := by
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    linarith
  have hinverse : ∀ n : ℕ, M < (n : ℝ) → M < (n : ℝ) := by
    intro n hn
    exact hn
  have hM_bound : M < 36 * K ^ 2 := by
    apply abstract_bound
        (g := fun n : ℕ ↦ (n : ℝ))
        (thr := Real.logb 2 p)
        (stepCap := fun y : ℝ ↦ 36 * y ^ 2)
        (inverseLower := M)
        hthr hterminal hgrowth hsteps
    change ∀ n : ℕ, M < (n : ℝ) → M < (n : ℝ)
    exact hinverse
  have hsqrt_sq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  dsimp [M] at hM_nonneg hM_bound hsqrt_sq hsqrt_nonneg ⊢
  nlinarith

/-! ## Trust audit

After the fills, every theorem must report exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. -/

#print axioms pricing_thr_squared
#print axioms pricing_stepCap_linearized
#print axioms pricing_growth_jlogj
#print axioms pricing_growth_linear

end BedertLab
