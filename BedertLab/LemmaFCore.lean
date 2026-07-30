/-
# Bedert lab, D2: the abstract counting core of Lemma F

Certifies the counting argument of Lemma F (candidates/bedert-omega/
lemma-F-attempt.md and leg1/blind-lemma-F.md, Cauchy-Schwarz route) from an
abstract interface. The fibre labels are abstract; `star` is the set of star
fibres (the paper's N(1/3) inside the ambient label set).

TRUST BOUNDARY (cited interface facts, proved in the prose from the paper):
  hmass  = the good-pair mass bound (main.tex:640-645 with manygood 624-632);
           the source supports sufficiently large C, while the exact-C interface
           comes from the campaign re-derivation in
           candidates/bedert-omega/constant-C-interface.md;
  hbad   = the weighted triple count for heavy non-star fibres
           (T-count with sigma C_1-multiplicity, main.tex:674-694);
  hstarcap = the star fibre cap q_a <= 3(d-1) (degree bound in a simple graph
           on D, blind-lemma-F.md Step F);
  hcard  = fibre labels live in A, so at most n of them;
  hS4    = the Proposition 6 algebraic cap (main.tex:481-484).
Everything from these to the conclusions is kernel-checked here.

Conclusions: star mass >= d^2/8 and star count >= d/24 — Lemma F(i),(ii) with
the blind route's constants.

FROZEN STATEMENT: fill the sorry only; do NOT alter the statement. BLOCKED if
unprovable as written.
-/
import Mathlib

namespace BedertLab

/-- Abstract counting core of Lemma F.  `s` is the set of fibre labels, `q` the
fibre sizes, `star ⊆ s` the star fibres.  The heavy threshold is
`d^2/(6n)`; heavy non-star fibres carry bounded square mass; star fibres are
individually capped at `3(d-1)`.  Then the star fibres carry mass at least
`d^2/8` and number at least `d/24`. -/
theorem lemmaF_core {ι : Type*} [DecidableEq ι]
    (s star : Finset ι) (hsub : star ⊆ s) (q : ι → ℕ)
    {d n C₁ C S : ℝ}
    (hd : 10 ≤ d) (hdn : d ≤ n)
    (hC1 : 1 ≤ C₁) (hC : 2048 * C₁ ≤ C)
    (hS4 : S ^ 4 ≤ d ^ 6 / (C * n ^ 5))
    (hmass : d ^ 2 / 3 ≤ ∑ a ∈ s, (q a : ℝ))
    (hcard : (s.card : ℝ) ≤ n)
    (hbad : ∑ a ∈ (s \ star).filter (fun a => d ^ 2 / (6 * n) ≤ (q a : ℝ)),
        ((q a : ℝ)) ^ 2 ≤ 3 * C₁ * n ^ 2 * S ^ 4)
    (hstarcap : ∀ a ∈ star, (q a : ℝ) ≤ 3 * (d - 1)) :
    d ^ 2 / 8 ≤ (∑ a ∈ star, (q a : ℝ)) ∧ d / 24 ≤ (star.card : ℝ) := by
  classical
  let heavy : Finset ι :=
    (s \ star).filter (fun a => d ^ 2 / (6 * n) ≤ (q a : ℝ))
  let light : Finset ι :=
    (s \ star).filter (fun a => ¬d ^ 2 / (6 * n) ≤ (q a : ℝ))
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hn_pos : 0 < n := hd_pos.trans_le hdn
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le (by norm_num) hC1
  have hC_pos : 0 < C := by nlinarith [hC]
  have hmass_split :
      (∑ a ∈ heavy, (q a : ℝ)) + (∑ a ∈ light, (q a : ℝ)) +
          (∑ a ∈ star, (q a : ℝ)) =
        ∑ a ∈ s, (q a : ℝ) := by
    have hnonstar :=
      Finset.sum_filter_add_sum_filter_not (s \ star)
        (fun a => d ^ 2 / (6 * n) ≤ (q a : ℝ)) (fun a => (q a : ℝ))
    have hs := Finset.sum_sdiff hsub (f := fun a => (q a : ℝ))
    change
      (∑ a ∈ heavy, (q a : ℝ)) + (∑ a ∈ light, (q a : ℝ)) =
        ∑ a ∈ s \ star, (q a : ℝ) at hnonstar
    rw [hnonstar]
    exact hs
  have hlight_subset : light ⊆ s := by
    intro a ha
    have ha' :
        a ∈ s \ star ∧ ¬d ^ 2 / (6 * n) ≤ (q a : ℝ) := by
      simpa only [light, Finset.mem_filter] using ha
    exact Finset.sdiff_subset ha'.1
  have hlight_card : (light.card : ℝ) ≤ n := by
    have hcard_nat : light.card ≤ s.card :=
      Finset.card_le_card hlight_subset
    have hcard_real : (light.card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast hcard_nat
    exact hcard_real.trans hcard
  have hthreshold_nonneg : 0 ≤ d ^ 2 / (6 * n) := by positivity
  have hlight_mass : (∑ a ∈ light, (q a : ℝ)) ≤ d ^ 2 / 6 := by
    calc
      (∑ a ∈ light, (q a : ℝ)) ≤
          ∑ _a ∈ light, d ^ 2 / (6 * n) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' :
            a ∈ s \ star ∧ ¬d ^ 2 / (6 * n) ≤ (q a : ℝ) := by
          simpa only [light, Finset.mem_filter] using ha
        exact le_of_not_ge ha'.2
      _ = (light.card : ℝ) * (d ^ 2 / (6 * n)) := by
        simp
      _ ≤ n * (d ^ 2 / (6 * n)) :=
        mul_le_mul_of_nonneg_right hlight_card hthreshold_nonneg
      _ = d ^ 2 / 6 := by
        field_simp
  have hheavy_subset : heavy ⊆ s := by
    intro a ha
    have ha' :
        a ∈ s \ star ∧ d ^ 2 / (6 * n) ≤ (q a : ℝ) := by
      simpa only [heavy, Finset.mem_filter] using ha
    exact Finset.sdiff_subset ha'.1
  have hheavy_card : (heavy.card : ℝ) ≤ n := by
    have hcard_nat : heavy.card ≤ s.card :=
      Finset.card_le_card hheavy_subset
    have hcard_real : (heavy.card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast hcard_nat
    exact hcard_real.trans hcard
  have hheavy_sq :
      (∑ a ∈ heavy, (q a : ℝ)) ^ 2 ≤
        (heavy.card : ℝ) * ∑ a ∈ heavy, ((q a : ℝ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hbad' :
      (∑ a ∈ heavy, ((q a : ℝ)) ^ 2) ≤ 3 * C₁ * n ^ 2 * S ^ 4 := by
    exact hbad
  have hsum_sq_nonneg :
      0 ≤ ∑ a ∈ heavy, ((q a : ℝ)) ^ 2 := by positivity
  have hC_bound : 1728 * C₁ ≤ C := by nlinarith [hC]
  have hd_sq_le : d ^ 2 ≤ n ^ 2 := by nlinarith
  have hconstant_product : 1728 * C₁ * d ^ 2 ≤ C * n ^ 2 := by
    calc
      1728 * C₁ * d ^ 2 ≤ C * d ^ 2 :=
        mul_le_mul_of_nonneg_right hC_bound (sq_nonneg d)
      _ ≤ C * n ^ 2 :=
        mul_le_mul_of_nonneg_left hd_sq_le hC_pos.le
  have hscaled_constant :
      3 * C₁ * d ^ 6 ≤ d ^ 4 / 576 * (C * n ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hconstant_product
      (show 0 ≤ d ^ 4 / 576 by positivity)
    nlinarith [hmul]
  have hratio :
      3 * C₁ * d ^ 6 / (C * n ^ 2) ≤ d ^ 4 / 576 := by
    apply (div_le_iff₀ (mul_pos hC_pos (sq_pos_of_pos hn_pos))).2
    exact hscaled_constant
  have halgebra :
      n * (3 * C₁ * n ^ 2 * (d ^ 6 / (C * n ^ 5))) =
        3 * C₁ * d ^ 6 / (C * n ^ 2) := by
    field_simp
  have hheavy_mass_sq :
      (∑ a ∈ heavy, (q a : ℝ)) ^ 2 ≤ d ^ 4 / 576 := by
    calc
      (∑ a ∈ heavy, (q a : ℝ)) ^ 2 ≤
          (heavy.card : ℝ) * ∑ a ∈ heavy, ((q a : ℝ)) ^ 2 :=
        hheavy_sq
      _ ≤ n * ∑ a ∈ heavy, ((q a : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hheavy_card hsum_sq_nonneg
      _ ≤ n * (3 * C₁ * n ^ 2 * S ^ 4) :=
        mul_le_mul_of_nonneg_left hbad' hn_pos.le
      _ ≤ n * (3 * C₁ * n ^ 2 * (d ^ 6 / (C * n ^ 5))) := by
        gcongr
      _ = 3 * C₁ * d ^ 6 / (C * n ^ 2) := halgebra
      _ ≤ d ^ 4 / 576 := hratio
  have hheavy_mass_nonneg : 0 ≤ ∑ a ∈ heavy, (q a : ℝ) := by positivity
  have hheavy_mass :
      (∑ a ∈ heavy, (q a : ℝ)) ≤ d ^ 2 / 24 := by
    nlinarith only [hheavy_mass_sq, hheavy_mass_nonneg, sq_nonneg d]
  have hstar_mass : d ^ 2 / 8 ≤ ∑ a ∈ star, (q a : ℝ) := by
    nlinarith only [hmass_split, hmass, hlight_mass, hheavy_mass]
  constructor
  · exact hstar_mass
  · have hstar_mass_upper :
        (∑ a ∈ star, (q a : ℝ)) ≤ (star.card : ℝ) * (3 * d) := by
      calc
        (∑ a ∈ star, (q a : ℝ)) ≤ ∑ _a ∈ star, 3 * d := by
          apply Finset.sum_le_sum
          intro a ha
          calc
            (q a : ℝ) ≤ 3 * (d - 1) := hstarcap a ha
            _ ≤ 3 * d := by linarith
        _ = (star.card : ℝ) * (3 * d) := by
          simp
    nlinarith only [hd_pos, hstar_mass, hstar_mass_upper]

#print axioms lemmaF_core

/-- Sharp version (the Sol-route constants, referee-report MAJOR-1 fix): from
the SAME interface, star mass at least `d^2/7` and star count at least `d/21`,
matching the `12/7`-budget frozen in CubicChain.  Route: threshold division
instead of Cauchy-Schwarz — on the heavy filter set every fibre has
`q_a >= d^2/(6n)`, so `sum q <= (6n/d^2) * sum q^2`. -/
theorem lemmaF_core_sharp {ι : Type*} [DecidableEq ι]
    (s star : Finset ι) (hsub : star ⊆ s) (q : ι → ℕ)
    {d n C₁ C S : ℝ}
    (hd : 10 ≤ d) (hdn : d ≤ n)
    (hC1 : 1 ≤ C₁) (hC : 2048 * C₁ ≤ C)
    (hS4 : S ^ 4 ≤ d ^ 6 / (C * n ^ 5))
    (hmass : d ^ 2 / 3 ≤ ∑ a ∈ s, (q a : ℝ))
    (hcard : (s.card : ℝ) ≤ n)
    (hbad : ∑ a ∈ (s \ star).filter (fun a => d ^ 2 / (6 * n) ≤ (q a : ℝ)),
        ((q a : ℝ)) ^ 2 ≤ 3 * C₁ * n ^ 2 * S ^ 4)
    (hstarcap : ∀ a ∈ star, (q a : ℝ) ≤ 3 * (d - 1)) :
    d ^ 2 / 7 ≤ (∑ a ∈ star, (q a : ℝ)) ∧ d / 21 ≤ (star.card : ℝ) := by
  classical
  let heavy : Finset ι :=
    (s \ star).filter (fun a => d ^ 2 / (6 * n) ≤ (q a : ℝ))
  let light : Finset ι :=
    (s \ star).filter (fun a => ¬d ^ 2 / (6 * n) ≤ (q a : ℝ))
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hn_pos : 0 < n := hd_pos.trans_le hdn
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le (by norm_num) hC1
  have hC_pos : 0 < C := by nlinarith [hC]
  have hmass_split :
      (∑ a ∈ heavy, (q a : ℝ)) + (∑ a ∈ light, (q a : ℝ)) +
          (∑ a ∈ star, (q a : ℝ)) =
        ∑ a ∈ s, (q a : ℝ) := by
    have hnonstar :=
      Finset.sum_filter_add_sum_filter_not (s \ star)
        (fun a => d ^ 2 / (6 * n) ≤ (q a : ℝ)) (fun a => (q a : ℝ))
    have hs := Finset.sum_sdiff hsub (f := fun a => (q a : ℝ))
    change
      (∑ a ∈ heavy, (q a : ℝ)) + (∑ a ∈ light, (q a : ℝ)) =
        ∑ a ∈ s \ star, (q a : ℝ) at hnonstar
    rw [hnonstar]
    exact hs
  have hlight_subset : light ⊆ s := by
    intro a ha
    have ha' :
        a ∈ s \ star ∧ ¬d ^ 2 / (6 * n) ≤ (q a : ℝ) := by
      simpa only [light, Finset.mem_filter] using ha
    exact Finset.sdiff_subset ha'.1
  have hlight_card : (light.card : ℝ) ≤ n := by
    have hcard_nat : light.card ≤ s.card :=
      Finset.card_le_card hlight_subset
    have hcard_real : (light.card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast hcard_nat
    exact hcard_real.trans hcard
  have hthreshold_nonneg : 0 ≤ d ^ 2 / (6 * n) := by positivity
  have hlight_mass : (∑ a ∈ light, (q a : ℝ)) ≤ d ^ 2 / 6 := by
    calc
      (∑ a ∈ light, (q a : ℝ)) ≤
          ∑ _a ∈ light, d ^ 2 / (6 * n) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' :
            a ∈ s \ star ∧ ¬d ^ 2 / (6 * n) ≤ (q a : ℝ) := by
          simpa only [light, Finset.mem_filter] using ha
        exact le_of_not_ge ha'.2
      _ = (light.card : ℝ) * (d ^ 2 / (6 * n)) := by
        simp
      _ ≤ n * (d ^ 2 / (6 * n)) :=
        mul_le_mul_of_nonneg_right hlight_card hthreshold_nonneg
      _ = d ^ 2 / 6 := by
        field_simp
  have hheavy_pointwise :
      ∀ a ∈ heavy,
        (q a : ℝ) ≤ (6 * n / d ^ 2) * ((q a : ℝ)) ^ 2 := by
    intro a ha
    have ha' :
        a ∈ s \ star ∧ d ^ 2 / (6 * n) ≤ (q a : ℝ) := by
      simpa only [heavy, Finset.mem_filter] using ha
    have hthreshold :
        d ^ 2 ≤ 6 * n * (q a : ℝ) := by
      simpa [mul_comm] using
        (div_le_iff₀ (by positivity : 0 < 6 * n)).mp ha'.2
    have hmul := mul_le_mul_of_nonneg_right hthreshold
      (show 0 ≤ (q a : ℝ) by positivity)
    calc
      (q a : ℝ) ≤ (6 * n * ((q a : ℝ)) ^ 2) / d ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hd_pos)).2
        nlinarith only [hmul]
      _ = (6 * n / d ^ 2) * ((q a : ℝ)) ^ 2 := by ring
  have hbad' :
      (∑ a ∈ heavy, ((q a : ℝ)) ^ 2) ≤
        3 * C₁ * n ^ 2 * S ^ 4 := by
    exact hbad
  have hheavy_mass_raw :
      (∑ a ∈ heavy, (q a : ℝ)) ≤
        18 * C₁ * d ^ 4 / (C * n ^ 2) := by
    calc
      (∑ a ∈ heavy, (q a : ℝ)) ≤
          ∑ a ∈ heavy, (6 * n / d ^ 2) * ((q a : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        exact hheavy_pointwise
      _ = (6 * n / d ^ 2) *
          ∑ a ∈ heavy, ((q a : ℝ)) ^ 2 := by
        simp [Finset.mul_sum]
      _ ≤ (6 * n / d ^ 2) * (3 * C₁ * n ^ 2 * S ^ 4) :=
        mul_le_mul_of_nonneg_left hbad' (by positivity)
      _ ≤ (6 * n / d ^ 2) *
          (3 * C₁ * n ^ 2 * (d ^ 6 / (C * n ^ 5))) := by
        gcongr
      _ = 18 * C₁ * d ^ 4 / (C * n ^ 2) := by
        field_simp
        norm_num
  have hconstant_ratio : 18 * C₁ / C ≤ 18 / 2048 := by
    apply (div_le_iff₀ hC_pos).2
    nlinarith [hC]
  have hd_sq_le : d ^ 2 ≤ n ^ 2 := by nlinarith
  have hdegree_ratio : d ^ 4 / n ^ 2 ≤ d ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn_pos)).2
    have hmul :=
      mul_le_mul_of_nonneg_left hd_sq_le (sq_nonneg d)
    nlinarith only [hmul]
  have hheavy_mass :
      (∑ a ∈ heavy, (q a : ℝ)) ≤ (18 / 2048) * d ^ 2 := by
    calc
      (∑ a ∈ heavy, (q a : ℝ)) ≤
          18 * C₁ * d ^ 4 / (C * n ^ 2) := hheavy_mass_raw
      _ = (18 * C₁ / C) * (d ^ 4 / n ^ 2) := by
        field_simp
      _ ≤ (18 / 2048) * d ^ 2 :=
        mul_le_mul hconstant_ratio hdegree_ratio (by positivity) (by norm_num)
  have hstar_mass : d ^ 2 / 7 ≤ ∑ a ∈ star, (q a : ℝ) := by
    nlinarith only [hmass_split, hmass, hlight_mass, hheavy_mass]
  constructor
  · exact hstar_mass
  · have hstar_mass_upper :
        (∑ a ∈ star, (q a : ℝ)) ≤ (star.card : ℝ) * (3 * d) := by
      calc
        (∑ a ∈ star, (q a : ℝ)) ≤ ∑ _a ∈ star, 3 * d := by
          apply Finset.sum_le_sum
          intro a ha
          calc
            (q a : ℝ) ≤ 3 * (d - 1) := hstarcap a ha
            _ ≤ 3 * d := by linarith
        _ = (star.card : ℝ) * (3 * d) := by
          simp
    nlinarith only [hd_pos, hstar_mass, hstar_mass_upper]

#print axioms lemmaF_core_sharp

end BedertLab
