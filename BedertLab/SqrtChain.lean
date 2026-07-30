/-
# Bedert lab: the square-root chain (streamlined, referee-2 basis)

FROZEN by Fable 2026-07-23 from skeleton-proposals.md v2 after independent
line-check of the terminal arithmetic (case 1: K^2 > M/49; case 2:
202 K^2 >= M/2 via log2 K <= K^2, cutoff hMC doubling 202 -> 404).
Basis: referee-report-2.md MAJOR-1/2 streamlined chain — ORIGINAL two-term
cap, u-side E_t budget, center-pinned labels, banks d/(36K) and d/(49K),
one-bit growth. TRUST BOUNDARY: interface facts cited inline to
main.tex / referee-report-2 / blind3. Fill the sorry bodies only; BLOCKED
if any statement is unprovable as written.
-/
import Mathlib
import BedertLab.Abstract

namespace BedertLab

/-
# Bedert lab: the streamlined square-root one-bit chain

Analytic core of the streamlined chain adjudicated in
`candidates/bedert-omega/referee-report-2.md`, MAJOR-1 and MAJOR-2.

TRUST BOUNDARY:
  * original two-term cap: `sources/bedert/src/main.tex:479-484`;
  * original removal `B^(1)(D)` using `2S-2S`:
    `sources/bedert/src/main.tex:532-546`;
  * outward gain `d / (36 K)` and one-bit update:
    `sources/bedert/src/main.tex:696-713`;
  * inward gain `d / (49 K)` and one-bit update:
    `referee-report-2.md`, MAJOR-1 and MAJOR-2, using the source equations at
    `sources/bedert/src/main.tex:716-724`;
  * balancedness input `log₂ p ≤ n`:
    `sources/bedert/src/main.tex:497-512`.

The sixth-root cap and `3S-3S` removal are not interfaces of this proposal.
Everything after the interfaces above is intended to be kernel-checked.

PROPOSED FROZEN STATEMENTS: after review, fill only the `sorry` bodies. Do not
alter a frozen statement to make a proof pass. Print `BLOCKED: <reason>` if a
statement is false.
-/


/-- Streamlined composition, re-derived adjacent to the definition:
the step budget is `49 K²`; the fourth-root terminal case contributes
`4 * 49 K² + 6 log₂ K`; `log₂ K ≤ K²` gives `202 K²`; and the cutoff
`M ≥ 2 log₂ C` doubles `202` to `404`. Thus
`2 * (4 * 49 + 6) = 404`. -/
noncomputable def sqrtChainDenominator : ℝ := 404

/-- The two one-bit gains telescope to the weighted budget, and the inward
coefficient `49` controls the total number of steps. -/
theorem one_bit_budget_steps
    {n d K cT fI : ℝ}
    /- Source: the `d ≥ 10` main regime in `main.tex:479-484`; the easy
       branch is separated in `main.tex:497-498`. -/
    (hd : 10 ≤ d)
    /- Source: `K = n / d` in `main.tex:497-498`; since `D ⊆ A`, `K ≥ 1`. -/
    (hK : 1 ≤ K)
    /- Source: `cT` and `fI` are step counts, hence nonnegative. -/
    (hcT : 0 ≤ cT)
    (hfI : 0 ≤ fI)
    /- Source: `K := n / d`, equivalently `n = Kd`. -/
    (hscale : n = K * d)
    /- Source: outward gain `d/(36K)` from `main.tex:696-713`, inward gain
       `d/(49K)` from `referee-report-2.md`, MAJOR-1, and disjoint newly
       covered points under iteration. Strict gains are weakened to this
       non-strict telescoping interface. -/
    (htelescope :
      cT * (d / (36 * K)) + fI * (d / (49 * K)) ≤ n) :
    cT / 36 + fI / 49 ≤ K ^ 2 ∧
      cT + fI ≤ 49 * K ^ 2 := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hleft :
      cT * (d / (36 * K)) + fI * (d / (49 * K)) =
        (d / K) * (cT / 36 + fI / 49) := by
    field_simp
  have hright : K * d = (d / K) * K ^ 2 := by
    field_simp
  rw [hscale, hleft, hright] at htelescope
  have hweighted : cT / 36 + fI / 49 ≤ K ^ 2 :=
    le_of_mul_le_mul_left htelescope (div_pos hd_pos hK_pos)
  constructor
  · exact hweighted
  · by_cases hfI' : 0 ≤ fI
    · nlinarith
    · exact (hfI' hfI).elim

/-- Abstract one-bit growth lemma. Starting with one point and multiplying
the current size by at most two at each update gives
`log₂ |S_j| ≤ j`. -/
theorem one_bit_growth
    {size : ℕ → ℕ} {j : ℕ}
    /- Source: the iteration starts from `S₀ = {0}` in `main.tex:497-498`. -/
    (hstart : size 0 = 1)
    /- Source: the outward branch is `S ∪ (S+t)` in `main.tex:707-713`; the
       streamlined inward branch is `S + {0,t}` by `referee-report-2.md`,
       MAJOR-1. Both have multiplier at most two. -/
    (hstep : ∀ i < j, size (i + 1) ≤ 2 * size i) :
    Real.logb 2 (size j : ℝ) ≤ (j : ℝ) := by
  have hsize : ∀ i ≤ j, size i ≤ 2 ^ i := by
    intro i hi
    induction i with
    | zero =>
        simp [hstart]
    | succ i ih =>
        calc
          size (i + 1) ≤ 2 * size i :=
            hstep i (Nat.lt_of_succ_le hi)
          _ ≤ 2 * 2 ^ i :=
            Nat.mul_le_mul_left 2
              (ih (Nat.le_trans (Nat.le_succ i) hi))
          _ = 2 ^ (i + 1) := (pow_succ' 2 i).symm
  have hsize_j : size j ≤ 2 ^ j := hsize j le_rfl
  by_cases hz : size j = 0
  · simp [hz, Real.logb]
  · have hsize_pos_nat : 0 < size j := Nat.pos_of_ne_zero hz
    have hsize_pos : (0 : ℝ) < size j := by exact_mod_cast hsize_pos_nat
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) j
    have hsize_real : (size j : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast hsize_j
    have hlog :=
      (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num)
        hsize_pos hpow_pos).2 hsize_real
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
    simpa using hlog

/-- Failure of the original two-term cap in `main.tex:481-484`, together
with balancedness and the scale identity, gives exactly the two logged
terminal alternatives in the streamlined chain. -/
theorem sqrt_terminal_cases
    {p terminalSize d n K C : ℝ}
    /- Source: the headline cutoff `M ≥ 10` implies the positivity needed
       to take the outer logarithm in the rectification case. -/
    (hp : 0 < Real.logb 2 p)
    /- Source: `terminalSize = |S_j|`; `0 ∈ S_j` throughout. -/
    (hterminalSize : 0 < terminalSize)
    /- Source: the `d ≥ 10` main regime in `main.tex:479-484`. -/
    (hd : 10 ≤ d)
    /- Source: `K = n / d` and `D ⊆ A`, so `K ≥ 1`. -/
    (hK : 1 ≤ K)
    /- Source: the paper chooses a positive absolute cap constant `C`. -/
    (hC : 1 ≤ C)
    /- Source: `K := n / d`, equivalently `n = Kd`. -/
    (hscale : n = K * d)
    /- Source: the weak balancedness bound used at `main.tex:506-512`. -/
    (hbalanced : Real.logb 2 p ≤ n)
    /- Source: the exact original cap at `main.tex:481-484`. -/
    (hcapFailure :
      min
          (Real.logb 2 p)
          ((d ^ 6 / (C * n ^ 5)) ^ ((1 : ℝ) / 4)) <
        terminalSize) :
    Real.logb 2 (Real.logb 2 p) < Real.logb 2 terminalSize ∨
      Real.logb 2 (Real.logb 2 p) -
          Real.logb 2 C - 6 * Real.logb 2 K <
        4 * Real.logb 2 terminalSize := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hn_pos : 0 < n := by
    rw [hscale]
    exact mul_pos hK_pos hd_pos
  rcases (min_lt_iff.mp hcapFailure) with hrect | halgebraic
  · left
    rw [Real.logb, Real.logb]
    exact (div_lt_div_iff_of_pos_right
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
        (Real.strictMonoOn_log hp hterminalSize hrect)
  · right
    have hratio_pos : 0 < d ^ 6 / (C * n ^ 5) := by positivity
    have hroot_pos :
        0 < (d ^ 6 / (C * n ^ 5)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos hratio_pos _
    have hroot_log :
        Real.logb 2 ((d ^ 6 / (C * n ^ 5)) ^ ((1 : ℝ) / 4)) <
          Real.logb 2 terminalSize :=
      Real.logb_lt_logb (by norm_num) hroot_pos halgebraic
    have hroot_eval :
        4 *
            Real.logb 2
              ((d ^ 6 / (C * n ^ 5)) ^ ((1 : ℝ) / 4)) =
          Real.logb 2 (d ^ 6 / (C * n ^ 5)) := by
      rw [Real.logb, Real.logb, Real.log_rpow hratio_pos]
      ring
    have hratio_log :
        Real.logb 2 (d ^ 6 / (C * n ^ 5)) =
          6 * Real.logb 2 d - Real.logb 2 C -
            5 * Real.logb 2 n := by
      rw [Real.logb_div (pow_ne_zero 6 (ne_of_gt hd_pos))
        (mul_ne_zero (ne_of_gt hC_pos) (pow_ne_zero 5 (ne_of_gt hn_pos)))]
      rw [Real.logb_pow, Real.logb_mul (ne_of_gt hC_pos)
        (pow_ne_zero 5 (ne_of_gt hn_pos)), Real.logb_pow]
      ring
    have hratio_lt :
        Real.logb 2 (d ^ 6 / (C * n ^ 5)) <
          4 * Real.logb 2 terminalSize := by
      nlinarith [hroot_log, hroot_eval]
    have hlog_n :
        Real.logb 2 n = Real.logb 2 K + Real.logb 2 d := by
      rw [hscale, Real.logb_mul (ne_of_gt hK_pos) (ne_of_gt hd_pos)]
    have hbalanced_log :
        Real.logb 2 (Real.logb 2 p) ≤ Real.logb 2 n :=
      (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) hp hn_pos).2
        hbalanced
    nlinarith [hratio_log]

/-- Headline streamlined square-root chain. Both branches cost one bit, the
inward gain `d/(49K)` controls the step budget, and failure of the original
two-term cap forces `K > sqrt(M/404)`. -/
theorem sqrt_improvement
    {p terminalSize d n K C cT fI : ℝ}
    /- Source: the uniform headline regime in `referee-report-2.md`,
       MAJOR-1. It also supplies the log positivity needed below. -/
    /- Source: p is a large prime; guards Mathlib's log|x| convention
       (claim-checklist item; third incident 2026-07-23). -/
    (hthr : 0 < Real.logb 2 p)
    (hM10 : 10 ≤ Real.logb 2 (Real.logb 2 p))
    /- Source: the cutoff used to absorb the fixed `log₂ C` remainder in
       the same constant re-derivation. -/
    (hMC :
      2 * Real.logb 2 C ≤ Real.logb 2 (Real.logb 2 p))
    /- Source: `terminalSize = |S_j|` with `0 ∈ S_j`. -/
    (hterminalSize : 0 < terminalSize)
    /- Source: the `d ≥ 10` main regime in `main.tex:479-484`. -/
    (hd : 10 ≤ d)
    /- Source: `K = n / d` and `D ⊆ A`. -/
    (hK : 1 ≤ K)
    /- Source: positivity of the paper's absolute cap constant. -/
    (hC : 1 ≤ C)
    /- Source: outward and inward step counts. -/
    (hcT : 0 ≤ cT)
    (hfI : 0 ≤ fI)
    /- Source: `K := n / d`, equivalently `n = Kd`. -/
    (hscale : n = K * d)
    /- Source: weak balancedness at `main.tex:506-512`. -/
    (hbalanced : Real.logb 2 p ≤ n)
    /- Source: outward `d/(36K)` at `main.tex:696-713`, inward `d/(49K)`
       in `referee-report-2.md`, MAJOR-1, and telescoping of disjoint gains. -/
    (htelescope :
      cT * (d / (36 * K)) + fI * (d / (49 * K)) ≤ n)
    /- Source: both branches are one-bit updates, so
       `log₂ |S_j| ≤ j = cT + fI`. -/
    (hgrowth :
      Real.logb 2 terminalSize ≤ cT + fI)
    /- Source: exact original two-term cap at `main.tex:481-484`. -/
    (hcapFailure :
      min
          (Real.logb 2 p)
          ((d ^ 6 / (C * n ^ 5)) ^ ((1 : ℝ) / 4)) <
        terminalSize) :
    Real.sqrt
        (Real.logb 2 (Real.logb 2 p) / sqrtChainDenominator) < K := by
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    linarith
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hsteps : cT + fI ≤ 49 * K ^ 2 :=
    (one_bit_budget_steps hd hK hcT hfI hscale htelescope).2
  have hterminal_bound : Real.logb 2 terminalSize ≤ 49 * K ^ 2 :=
    le_trans hgrowth hsteps
  have hcases :
      M < Real.logb 2 terminalSize ∨
        M - Real.logb 2 C - 6 * Real.logb 2 K <
          4 * Real.logb 2 terminalSize := by
    simpa [M] using
      sqrt_terminal_cases hthr hterminalSize hd hK hC hscale
        hbalanced hcapFailure
  have hsqrt_lt (hMK : M < 404 * K ^ 2) :
      Real.sqrt (M / 404) < K := by
    have hrad_nonneg : 0 ≤ M / 404 := by positivity
    have hsqrt_sq : (Real.sqrt (M / 404)) ^ 2 = M / 404 :=
      Real.sq_sqrt hrad_nonneg
    have hsqrt_nonneg : 0 ≤ Real.sqrt (M / 404) :=
      Real.sqrt_nonneg _
    nlinarith
  rcases hcases with hrect | halgebraic
  · have hMK : M < 404 * K ^ 2 := by
      nlinarith [sq_nonneg K]
    simpa [sqrtChainDenominator] using hsqrt_lt hMK
  · have hlog_two_half : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    have hlogK : Real.log K ≤ K - 1 :=
      Real.log_le_sub_one_of_pos hK_pos
    have hlogbK_twoK : Real.logb 2 K ≤ 2 * K := by
      rw [Real.logb]
      apply (div_le_iff₀ (Real.log_pos (by norm_num))).2
      nlinarith
    have hlogbK : Real.logb 2 K ≤ K ^ 2 := by
      by_cases hK_two : K ≤ 2
      · have hlogbK_one : Real.logb 2 K ≤ 1 := by
          calc
            Real.logb 2 K ≤ Real.logb 2 2 :=
              Real.logb_le_logb_of_le (by norm_num) hK_pos hK_two
            _ = 1 := Real.logb_self_eq_one (by norm_num)
        nlinarith [sq_nonneg (K - 1)]
      · nlinarith
    have hhalf : M / 2 < 202 * K ^ 2 := by
      nlinarith
    have hMK : M < 404 * K ^ 2 := by
      nlinarith
    simpa [sqrtChainDenominator] using hsqrt_lt hMK

/- After the fills, each theorem must have exactly the project-permitted
axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. -/
#print axioms one_bit_budget_steps
#print axioms one_bit_growth
#print axioms sqrt_terminal_cases
#print axioms sqrt_improvement



/-
# Bedert lab: abstract counting core of the streamlined inward bank

The theorem separates the finite popularity argument from the paper-side
construction of successful incidences and the u-side target sets `E_t`.

TRUST BOUNDARY:
  * the heavy fibres and fixed star centers come from
    `sources/bedert/src/main.tex:635-704`;
  * the center-pinned label is
    `t_a = a - (d(a) + s_{d(a)})`, read directly from the fixed-center
    equations at `sources/bedert/src/main.tex:696-704,721-724`;
  * the total successful incidence mass is strictly greater than `d²/49`,
    by the sharp `Q ≥ d²/7` mass and summed absorption derived in
    `arcB-s3-attempt.md` (1.8)-(3.9) and independently audited in
    `referee-report-2.md`, MAJOR-1;
  * `successful(a) ≤ |E_(label a)|` follows from the inward equations at
    `sources/bedert/src/main.tex:716-724` and the transfer derived in
    `arcB-s3-attempt.md` (3.6)-(3.9), then checked in
    `referee-report-2.md`, MAJOR-2;
  * `∑ₜ |E_t| ≤ n` is the u-side budget derived in
    `arcB-s3-attempt.md` (3.2)-(3.3), then confirmed true as written in
    `referee-report-2.md`, MAJOR-2. Its injection uses
    `S-S ⊆ 2S-2S` and the original `B^(1)(D)` at
    `sources/bedert/src/main.tex:532-546`.

There is deliberately no per-`a` uniqueness hypothesis. The label is a
function because the star center was fixed, and the bank counts distinct
`a` in a fibre of that center-pinned function.

Everything from these interface facts to the popular-label conclusion is
intended to be kernel-checked.

PROPOSED FROZEN STATEMENT: after review, fill only the `sorry` body. Do not
alter the statement to make the proof pass. Print `BLOCKED: <reason>` if it
is false.
-/


/-- Abstract streamlined inward-bank counting core.

`H` is the finite set of heavy, star-centered `a`; `label a` is the
center-pinned `t_a`; `successful a` is `|I(a)|`; and `E t` is Sol's u-side
target set
`{u ∈ G^(1)(D) : s_u - t ∈ S_u}`.
-/
theorem inwardBank_core
    {α τ υ : Type*}
    /- Source: labels are group differences, with zero singled out. -/
    [Zero τ]
    /- Source: the ambient group, hence the label type, is finite. Summing
       over all labels matches Sol's display (3.3) exactly. -/
    [Fintype τ]
    [DecidableEq α]
    [DecidableEq τ]
    (H : Finset α)
    (label : α → τ)
    (successful : α → ℕ)
    (E : τ → Finset υ)
    {d n K : ℝ}
    /- Source: the `d ≥ 10` main regime in `main.tex:479-484`. -/
    (hd : 10 ≤ d)
    /- Source: `K = n / d` and `D ⊆ A`. -/
    (hK : 1 ≤ K)
    /- Source: `K := n / d`, equivalently `n = Kd`. -/
    (hscale : n = K * d)
    /- Source: `a ∉ D+S` at `main.tex:635-648`, while the fixed center
       `d(a)+s_{d(a)}` lies in `D+S`; hence the center-pinned label is
       nonzero. No uniqueness statement is used. -/
    (hnonzero : ∀ a ∈ H, label a ≠ 0)
    /- Source: each successful spoke gives a distinct u-side target in
       `E_(label a)` using `main.tex:716-724`; this is the transfer verified
       in `referee-report-2.md`, MAJOR-2. -/
    (htransfer :
      ∀ a ∈ H, successful a ≤ (E (label a)).card)
    /- Source: Sol's u-side budget (3.3), confirmed true as written in
       `referee-report-2.md`, MAJOR-2. The injection uses the original
       `B^(1)(D)` definition at `main.tex:532-546`. -/
    (hbudget :
      (∑ t : τ, ((E t).card : ℝ)) ≤ n)
    /- Source: the sharp star mass plus summed absorption in
       `referee-report-2.md`, MAJOR-1, gives
       `R = ∑ₐ |I(a)| > d²/49`. -/
    (hmass :
      d ^ 2 / 49 < ∑ a ∈ H, (successful a : ℝ)) :
    ∃ t : τ,
      t ≠ 0 ∧
      d / (49 * K) <
        ((H.filter (fun a => label a = t)).card : ℝ) := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hq_nonneg : 0 ≤ d / (49 * K) := by positivity
  by_contra hpopular
  push_neg at hpopular
  have hzero_fiber :
      H.filter (fun a => label a = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha hlabel
    exact hnonzero a ha hlabel
  have hfiberwise :
      (∑ a ∈ H, ((E (label a)).card : ℝ)) =
        ∑ t : τ,
          ((H.filter (fun a => label a = t)).card : ℝ) *
            ((E t).card : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := (Finset.univ : Finset τ))
      (fun (_ : α) _ => Finset.mem_univ _)
      (fun a => ((E (label a)).card : ℝ))]
    apply Finset.sum_congr rfl
    intro t _
    calc
      ∑ a ∈ H with label a = t, ((E (label a)).card : ℝ) =
          ∑ _a ∈ H.filter (fun a => label a = t), ((E t).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [(Finset.mem_filter.mp ha).2]
      _ = ((H.filter (fun a => label a = t)).card : ℝ) *
          ((E t).card : ℝ) := by simp
  have hfiber_bound :
      (∑ t : τ,
          ((H.filter (fun a => label a = t)).card : ℝ) *
            ((E t).card : ℝ)) ≤
        d / (49 * K) * ∑ t : τ, ((E t).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : t = 0
    · subst t
      rw [hzero_fiber]
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
    · exact mul_le_mul_of_nonneg_right (hpopular t ht) (by positivity)
  have htransfer_sum :
      (∑ a ∈ H, (successful a : ℝ)) ≤
        ∑ a ∈ H, ((E (label a)).card : ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    exact_mod_cast htransfer a ha
  have hbudget_scaled :
      d / (49 * K) * (∑ t : τ, ((E t).card : ℝ)) ≤
        d / (49 * K) * n :=
    mul_le_mul_of_nonneg_left hbudget hq_nonneg
  have hscale_eval : d / (49 * K) * n = d ^ 2 / 49 := by
    rw [hscale]
    field_simp
  rw [hfiberwise] at htransfer_sum
  nlinarith

/- After the fill, the theorem must have exactly the project-permitted
axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. -/
#print axioms inwardBank_core


/-! ### LEMMA B-in, the alphabet face (ADDITIVE, 2026-07-25)

This section is **additive**: it alters no frozen statement and no existing
proof. It records, kernel-certified, that the Lean side of "LEMMA B-in"
(`candidates/bedert-omega/density-increment-adjudication.md:82-86,501-505`)
costs nothing, because `inwardBank_core` is already parametric in the budget:
its `n` enters only through `hscale : n = K * d`, and its conclusion is really
`d² / (49 * budget)`.

So a budget of the shape `c * d` is obtained by instantiating `n := c * d`,
`K := c`. Nothing is re-proved; the theorem below is one application.

WHAT THIS DOES NOT DO, and must not be read as doing: it does not supply
`hbudget'`. In the object layer that hypothesis is *discharged*, by
`ObjectLayer.inward_target_budget_from_objects_proposed`
(`O5Banks.lean:406-464`), which proves the budget `≤ |A|` and cannot prove
`≤ c * |D|`. Moreover the budget is an exact identity, not a slack bound:
`∑_t |E t| = |A ∩ (G⁽¹⁾(D) + S)|` (`O2Budget.fibre_sum_eq` plus the injection
in `O2Budget.uside_budget`, whose image is exactly that set). A uniform bound
`≤ c * |D|` with absolute `c` therefore asserts that the density-increment
iteration never leaves density `c/K`, which caps its own step count at
`O(c²)` and forces `c ≳ √(log₂log₂ p)`; fed back through the chain that
returns the already-banked `K ≫ √(log₂log₂ p)` and nothing more. See
`lean/bedert-lab/LEMMA-B-IN-REPORT.md`, Phase 2.

Kept because it is free and because it makes the accounting checkable: any
future budget theorem of the form `∑_t |E t| ≤ c * d` upgrades the inward bank
to `d / (49 * c)` by this theorem alone. -/
theorem inwardBank_core_alphabet
    {α τ υ : Type*}
    [Zero τ] [Fintype τ] [DecidableEq α] [DecidableEq τ]
    (H : Finset α)
    (label : α → τ)
    (successful : α → ℕ)
    (E : τ → Finset υ)
    {d c : ℝ}
    (hd : 10 ≤ d)
    (hc : 1 ≤ c)
    (hnonzero : ∀ a ∈ H, label a ≠ 0)
    (htransfer : ∀ a ∈ H, successful a ≤ (E (label a)).card)
    /- The alphabet budget: the shift alphabet is bounded by `c * |D|`
       instead of by `|A|`. OPEN; not discharged anywhere in this project. -/
    (hbudget' : (∑ t : τ, ((E t).card : ℝ)) ≤ c * d)
    (hmass : d ^ 2 / 49 < ∑ a ∈ H, (successful a : ℝ)) :
    ∃ t : τ,
      t ≠ 0 ∧
      d / (49 * c) <
        ((H.filter (fun a => label a = t)).card : ℝ) :=
  inwardBank_core (d := d) (n := c * d) (K := c)
    H label successful E hd hc rfl hnonzero htransfer hbudget' hmass

/- Additive theorem: same permitted axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`. -/
#print axioms inwardBank_core_alphabet


end BedertLab
