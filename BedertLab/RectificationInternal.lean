import BedertLab.ObjectLayer.O7Headline

open Pointwise

namespace BedertLab
namespace ObjectLayer

private theorem int_abs_nat_sub_lt_of_div_eq
    {a b q : ℕ} (hq : 0 < q) (hdiv : a / q = b / q) :
    |(a : ℤ) - (b : ℤ)| < (q : ℤ) := by
  have ha_mod : a % q < q := Nat.mod_lt a hq
  have hb_mod : b % q < q := Nat.mod_lt b hq
  have ha_decomp := Nat.mod_add_div a q
  have hb_decomp := Nat.mod_add_div b q
  rw [hdiv] at ha_decomp
  rw [abs_lt]
  constructor <;> omega

private theorem o7_card_room
    {p : ℕ} (hp : p.Prime)
    (A D S : Finset (ZMod p)) {C : ℝ}
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (h0 : (0 : ZMod p) ∈ S)
    (hcap : FourthPowerCap A D S C)
    (hC : 129024 ≤ C) :
    8 ^ S.card < p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hS_card_pos : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
  have hD_card_pos : 0 < D.card := by
    by_contra hDnot
    have hDzero : D.card = 0 := Nat.eq_zero_of_not_pos hDnot
    unfold FourthPowerCap at hcap
    rw [hDzero] at hcap
    norm_num at hcap
    have hpow_pos : 0 < (S.card : ℝ) ^ 4 := by positivity
    linarith
  have hD_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast hD_card_pos
  have hA_pos : 0 < (A.card : ℝ) := by
    exact lt_of_lt_of_le hD_pos (by
      exact_mod_cast Finset.card_le_card hDsubA)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hDA : (D.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hDsubA
  have hDA5 : (D.card : ℝ) ^ 5 ≤ (A.card : ℝ) ^ 5 := by
    gcongr
  have hden :
      129024 * (D.card : ℝ) ^ 5 ≤ C * (A.card : ℝ) ^ 5 := by
    calc
      129024 * (D.card : ℝ) ^ 5 ≤ C * (D.card : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ C * (A.card : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hDA5 hC_pos.le
  have hcap_mul :
      (S.card : ℝ) ^ 4 * (C * (A.card : ℝ) ^ 5) ≤
        (D.card : ℝ) ^ 6 := by
    exact (le_div_iff₀ (mul_pos hC_pos (by positivity))).mp hcap
  have hS4small :
      (S.card : ℝ) ^ 4 ≤ (D.card : ℝ) / 129024 := by
    apply (le_div_iff₀ (by norm_num)).2
    have hmul := mul_le_mul_of_nonneg_left hden
      (pow_nonneg hS_card_pos.le 4)
    have htotal :
        (S.card : ℝ) ^ 4 * (129024 * (D.card : ℝ) ^ 5) ≤
          (D.card : ℝ) ^ 6 :=
      hmul.trans hcap_mul
    nlinarith [show 0 < (D.card : ℝ) ^ 5 by positivity]
  have hthree_real :
      3 * (S.card : ℝ) ≤ (D.card : ℝ) := by
    have hS_one : (1 : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
    have hS_le_S4 : (S.card : ℝ) ≤ (S.card : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((S.card : ℝ) - 1),
        mul_nonneg (sq_nonneg (S.card : ℝ))
          (sub_nonneg.mpr hS_one)]
    nlinarith
  have hthree : 3 * S.card ≤ D.card := by
    exact_mod_cast hthree_real
  let subsetSum : D.powerset → ZMod p :=
    fun T => ∑ x ∈ T.1, x
  have hsubsetSum_injective : Function.Injective subsetSum := by
    intro T U hTU
    apply Subtype.ext
    exact hD T.1 T.2 U.1 U.2 hTU
  have hpowerset_le :
      D.powerset.card ≤ Fintype.card (ZMod p) := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective subsetSum hsubsetSum_injective
  have htwoD : 2 ^ D.card ≤ p := by
    simpa [Finset.card_powerset, ZMod.card] using hpowerset_le
  have height_le : 8 ^ S.card ≤ 2 ^ D.card := by
    calc
      8 ^ S.card = 2 ^ (3 * S.card) := by norm_num [pow_mul]
      _ ≤ 2 ^ D.card := Nat.pow_le_pow_right (by norm_num) hthree
  have height_le_p : 8 ^ S.card ≤ p := height_le.trans htwoD
  exact lt_of_le_of_ne height_le_p (by
    intro heq
    have hp_dvd : p ∣ 8 ^ S.card := by rw [heq]
    have hp_dvd_eight : p ∣ 8 := hp.dvd_of_dvd_pow hp_dvd
    have hp_le_eight : p ≤ 8 := Nat.le_of_dvd (by norm_num) hp_dvd_eight
    have height_ge_eight : 8 ≤ 8 ^ S.card := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 8)
        (Finset.card_pos.mpr ⟨0, h0⟩)
    have hp_ge_eight : 8 ≤ p := heq ▸ height_ge_eight
    have hp_eq : p = 8 := by omega
    norm_num [hp_eq] at hp)

private theorem exists_short_freiman_hom_of_card_room
    {p : ℕ} (hp : p.Prime) (S : Finset (ZMod p))
    (hS : S.Nonempty)
    (hroom : 8 ^ S.card < p) :
    ∃ φ : ZMod p → ℤ,
      Set.InjOn φ (↑S : Set (ZMod p)) ∧
        ∀ x ∈ S, ∀ y ∈ S, ∀ u ∈ S, ∀ v ∈ S,
          x + y = u + v →
            φ x + φ y = φ u + φ v := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  let q : ℕ := p / 8 + 1
  have hq : 0 < q := by simp [q]
  have hp_le_eight_q : p ≤ 8 * q := by
    dsimp only [q]
    omega
  let color : Fin (8 ^ S.card + 1) → S → Fin 8 :=
    fun k z =>
      ⟨(((k.val : ZMod p) * z.1).val / q), by
        apply (Nat.div_lt_iff_lt_mul hq).2
        have hval := ZMod.val_lt ((k.val : ZMod p) * z.1)
        omega⟩
  have hcard_lt :
      Fintype.card (S → Fin 8) <
        Fintype.card (Fin (8 ^ S.card + 1)) := by
    simp
  obtain ⟨k₀, l₀, hkl_ne, hcolor₀⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt color hcard_lt
  have hval_ne : k₀.val ≠ l₀.val := by
    intro h
    exact hkl_ne (Fin.ext h)
  obtain ⟨k, l, hkl, hcolor⟩ :
      ∃ k l : Fin (8 ^ S.card + 1),
        k.val < l.val ∧ color k = color l := by
    rcases lt_or_gt_of_ne hval_ne with h | h
    · exact ⟨k₀, l₀, h, hcolor₀⟩
    · exact ⟨l₀, k₀, h, hcolor₀.symm⟩
  have hl_le_room : l.val ≤ 8 ^ S.card := by
    omega
  have hl_lt_p : l.val < p := lt_of_le_of_lt hl_le_room hroom
  let aNat : ℕ := l.val - k.val
  have haNat_pos : 0 < aNat := by
    dsimp only [aNat]
    omega
  have haNat_lt_p : aNat < p := by
    dsimp only [aNat]
    omega
  have ha_ne : (aNat : ZMod p) ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_of_pos_of_lt haNat_pos haNat_lt_p
      ((ZMod.natCast_eq_zero_iff aNat p).mp hzero)
  let φ : ZMod p → ℤ := fun z =>
    (((l.val : ZMod p) * z).val : ℤ) -
      (((k.val : ZMod p) * z).val : ℤ)
  have hφ_cast (z : ZMod p) :
      (φ z : ZMod p) = (aNat : ZMod p) * z := by
    dsimp only [φ, aNat]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [Nat.cast_sub (Nat.le_of_lt hkl)]
    ring
  have hφ_bound :
      ∀ z ∈ S, |φ z| < (q : ℤ) := by
    intro z hz
    have hsame := congrFun hcolor (⟨z, hz⟩ : S)
    have hsame_val := congrArg Fin.val hsame
    change
      (((k.val : ZMod p) * z).val / q) =
        (((l.val : ZMod p) * z).val / q) at hsame_val
    exact int_abs_nat_sub_lt_of_div_eq hq hsame_val.symm
  refine ⟨φ, ?_, ?_⟩
  · intro x hx y hy hφxy
    have hmul :
        (aNat : ZMod p) * x = (aNat : ZMod p) * y := by
      rw [← hφ_cast, ← hφ_cast, hφxy]
    exact mul_left_cancel₀ ha_ne hmul
  · intro x hx y hy u hu v hv hsum
    let Δ : ℤ := φ x + φ y - φ u - φ v
    have hΔ_cast : (Δ : ZMod p) = 0 := by
      dsimp only [Δ]
      push_cast
      simp only [hφ_cast]
      calc
        (aNat : ZMod p) * x + (aNat : ZMod p) * y -
              (aNat : ZMod p) * u - (aNat : ZMod p) * v =
            (aNat : ZMod p) * (x + y - u - v) := by ring
        _ = 0 := by rw [hsum]; simp
    have hp_dvd_Δ : (p : ℤ) ∣ Δ :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd Δ p).mp hΔ_cast
    have hfour_q_lt_p : 4 * q < p := by
      have height_ge_eight : 8 ≤ 8 ^ S.card := by
        have hSpos : 0 < S.card := Finset.card_pos.mpr hS
        simpa only [pow_one] using Nat.pow_le_pow_right
          (by norm_num : 0 < 8) hSpos
      have hp_gt_eight : 8 < p := lt_of_le_of_lt height_ge_eight hroom
      dsimp only [q]
      omega
    have hΔ_lower : -(p : ℤ) < Δ := by
      have hx' := hφ_bound x hx
      have hy' := hφ_bound y hy
      have hu' := hφ_bound u hu
      have hv' := hφ_bound v hv
      rw [abs_lt] at hx' hy' hu' hv'
      dsimp only [Δ]
      omega
    have hΔ_upper : Δ < (p : ℤ) := by
      have hx' := hφ_bound x hx
      have hy' := hφ_bound y hy
      have hu' := hφ_bound u hu
      have hv' := hφ_bound v hv
      rw [abs_lt] at hx' hy' hu' hv'
      dsimp only [Δ]
      omega
    obtain ⟨c, hc⟩ := hp_dvd_Δ
    have hp_int_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hΔ_zero : Δ = 0 := by
      rw [hc] at hΔ_lower hΔ_upper ⊢
      by_cases hc0 : c = 0
      · simp [hc0]
      · rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
        · nlinarith
        · nlinarith
    dsimp only [Δ] at hΔ_zero
    omega

/-- The O7-specific replacement for the frozen global rectification
interface. It uses the fourth-power cap and dissociativity to construct only
the source-fibre selector actually consumed by O7b. -/
theorem exists_source_fibre_selector_of_o7_cap_internal
    {p : ℕ} (hp : p.Prime)
    (A D S : Finset (ZMod p)) {C : ℝ}
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (h0 : (0 : ZMod p) ∈ S)
    (hcap : FourthPowerCap A D S C)
    (hC : 129024 ≤ C) :
    ∃ sel : ZMod p → ZMod p,
      (∀ d ∈ D, sel d ∈ S ∧ d + sel d ∈ A) ∧
        ∀ d ∈ D, ∀ d' ∈ D,
          ∀ x ∈ S, d + x ∈ A →
            ∀ y ∈ S, d' + y ∈ A →
              x + y = sel d + sel d' →
                x = sel d ∧ y = sel d' := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hroom : 8 ^ S.card < p :=
    o7_card_room hp A D S hDsubA hD h0 hcap hC
  obtain ⟨φ, hφ_inj, hφ_add⟩ :=
    exists_short_freiman_hom_of_card_room hp S ⟨0, h0⟩ hroom
  have hmax :
      ∀ X : Finset (ZMod p), ∃ z : ZMod p,
        X.Nonempty → z ∈ X ∧ ∀ x ∈ X, φ x ≤ φ z := by
    intro X
    by_cases hX : X.Nonempty
    · let m := (X.image φ).max' (hX.image φ)
      have hm : m ∈ X.image φ := Finset.max'_mem _ _
      obtain ⟨z, hz, hφz⟩ := Finset.mem_image.mp hm
      refine ⟨z, fun _ => ⟨hz, ?_⟩⟩
      intro x hx
      rw [hφz]
      exact Finset.le_max' (X.image φ) (φ x)
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · exact ⟨0, fun h => (hX h).elim⟩
  choose choose hchoose using hmax
  have hsimultaneous :
      IsSimultaneousUniqueSelector S choose := by
    constructor
    · intro X hX hXS
      exact (hchoose X hX).1
    · intro X Y hX hY hXS hYS x hx y hy hsum
      have hxS : x ∈ S := hXS hx
      have hyS : y ∈ S := hYS hy
      have hchooseXS : choose X ∈ S :=
        hXS (hchoose X hX).1
      have hchooseYS : choose Y ∈ S :=
        hYS (hchoose Y hY).1
      have hφsum :
          φ x + φ y = φ (choose X) + φ (choose Y) :=
        hφ_add x hxS y hyS (choose X) hchooseXS
          (choose Y) hchooseYS hsum
      have hxle : φ x ≤ φ (choose X) :=
        (hchoose X hX).2 x hx
      have hyle : φ y ≤ φ (choose Y) :=
        (hchoose Y hY).2 y hy
      have hφx : φ x = φ (choose X) := by omega
      have hφy : φ y = φ (choose Y) := by omega
      exact ⟨hφ_inj hxS hchooseXS hφx,
        hφ_inj hyS hchooseYS hφy⟩
  exact source_selector_from_simultaneous_proposed
    A D S choose hsimultaneous hDsubA h0

/-- The maximality-free O7 one-bit step with the source-fibre selector
constructed internally from the O7 cap. -/
theorem sharpened_one_step_from_isUSF_internal
    {p : ℕ} (hp : p.Prime)
    (A D S : Finset (ZMod p)) {K C : ℝ}
    (hUSF : IsUSF A)
    (hDsubA : D ⊆ A)
    (hD : DissociatedF D)
    (hd : 10 ≤ D.card)
    (h0 : (0 : ZMod p) ∈ S)
    (hcap : FourthPowerCap A D S C)
    (hC : 129024 ≤ C)
    (hK : 1 ≤ K)
    (hscale : (A.card : ℝ) = K * (D.card : ℝ)) :
    ∃ t : ZMod p,
      t ≠ 0 ∧
        (S + ({0, t} : Finset (ZMod p))).card ≤ 2 * S.card ∧
          ((D.card : ℝ) / (36 * K) ≤
              ((((A ∩
                  (D + (S + ({0, t} : Finset (ZMod p))))) \
                (D + S)).card : ℕ) : ℝ) ∨
            (D.card : ℝ) / (49 * K) <
              ((((A ∩
                  (D + (S + ({0, t} : Finset (ZMod p))))) \
                (D + S)).card : ℕ) : ℝ)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨sel, hsel, hsim⟩ :=
    exists_source_fibre_selector_of_o7_cap_internal
      hp A D S hDsubA hD h0 hcap hC
  have hsecond :
      HasSecondRemovalBound D S (goodTwo D S sel) :=
    goodTwo_hasSecondRemovalBound_proposed
      D S sel hD (fun d hdD => (hsel d hdD).1)
  obtain ⟨ρ, hρ⟩ :=
    exists_oriented_representation_choice_from_isUSF_proposed
      A D S sel hUSF hsel hsim
  obtain ⟨center, retained, hcenter, _, hretained⟩ :=
    exists_star_centres_and_retained_proposed A D S sel ρ
  have hstarMass :=
    star_mass_for_constructed_system_proposed
      A D S sel ρ hDsubA hD h0 hd hC hcap hsecond hρ
  have hbranchClassification :=
    constructed_branch_dichotomy_proposed
      A D S sel center ρ retained hρ hcenter hretained
  have hyDistinct :=
    retained_chosenY_injective_proposed
      A D S sel center ρ retained hρ hretained
  have houtwardBank :
      ∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∉ D + S).card ≥
          (retained a).card →
        ∃ t : ZMod p,
          t ≠ 0 ∧
            (S + ({0, t} : Finset (ZMod p))).card ≤ 2 * S.card ∧
              (D.card : ℝ) / (36 * K) ≤
                ((((A ∩
                    (D + (S + ({0, t} : Finset (ZMod p))))) \
                  (D + S)).card : ℕ) : ℝ) := by
    intro a ha houtward
    obtain ⟨t, _, ht, hcard, hgain⟩ :=
      outward_bank_from_objects_proposed
        A D S (goodTwo D S sel) sel center ρ retained
        hρ hK hscale ha (hcenter a ha) (hretained a ha)
        (hyDistinct a ha) houtward
    exact ⟨t, ht, hcard, hgain⟩
  have hinwardBank :
      (∀ a ∈ starFibres A D S (goodTwo D S sel) ρ,
        2 *
            ((retained a).filter fun P =>
              chosenY ρ P ∈ D + S).card >
          (retained a).card) →
        ∃ t : ZMod p,
          t ≠ 0 ∧
            (S + ({0, t} : Finset (ZMod p))).card ≤ 2 * S.card ∧
              (D.card : ℝ) / (49 * K) <
                ((((A ∩
                    (D + (S + ({0, t} : Finset (ZMod p))))) \
                  (D + S)).card : ℕ) : ℝ) := by
    intro hinward
    obtain ⟨I, hI_sub, hI_success, hmass⟩ :=
      inward_diagonal_package_from_constructed_system_proposed
        A D S sel center ρ retained hDsubA hD h0 hd hC hcap
        hsecond hρ hretained hstarMass.1 hinward
    have hnonzero :=
      inward_label_nonzero_from_objects_proposed
        A D S (goodTwo D S sel) sel center ρ hρ
        (fun a ha => (hcenter a ha).1)
    have htransfer :=
      inward_successful_transfer_from_objects_proposed
        A D S (goodTwo D S sel) sel center ρ retained I hρ
        (fun a ha => (hretained a ha).1)
        (by
          intro a ha P hPI
          exact ⟨(Finset.mem_filter.mp (hI_sub a ha hPI)).1,
            hI_success a ha P hPI⟩)
    have hbudget :=
      inward_target_budget_from_objects_proposed
        A D S (goodTwo D S sel) sel ρ h0 hρ
    exact inward_bank_from_interfaces_proposed
      A D S (goodTwo D S sel) sel center ρ I hρ
      (fun a ha => (hcenter a ha).1)
      (by exact_mod_cast hd) hK hscale hnonzero htransfer hbudget hmass
  obtain ⟨t, Snext, ht, hSnext, _, _, hcard, hgain⟩ :=
    one_bit_iteration_step_from_O5_proposed
      A D S (goodTwo D S sel) ρ retained h0 houtwardBank hinwardBank
  subst Snext
  rcases hbranchClassification with _ | _
  · exact ⟨t, ht, hcard, hgain⟩
  · exact ⟨t, ht, hcard, hgain⟩

/-- The exact O6 current-state step interface, discharged without the
external `hBLR` parameter. -/
theorem o6_hstep_from_isUSF_internal
    {p : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) {C : ℝ}
    (hUSF : IsUSF A)
    (hdim : 0 < dimA A)
    (hC_object : 129024 ≤ C) :
    ∀ (D S : Finset (ZMod p)),
      D ⊆ A →
        DissociatedF D →
          D.card = dimA A →
            10 ≤ D.card →
              (0 : ZMod p) ∈ S →
                (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
                  FourthPowerCap A D S C →
                    ∃ t : ZMod p,
                      t ≠ 0 ∧
                        (S + ({0, t} : Finset (ZMod p))).card ≤
                          2 * S.card ∧
                        ((D.card : ℝ) / (36 * (KA A : ℝ)) ≤
                            ((((A ∩
                                (D + (S + ({0, t} : Finset (ZMod p))))) \
                              (D + S)).card : ℕ) : ℝ) ∨
                          (D.card : ℝ) / (49 * (KA A : ℝ)) <
                            ((((A ∩
                                (D + (S + ({0, t} : Finset (ZMod p))))) \
                              (D + S)).card : ℕ) : ℝ)) := by
  intro D S hDsubA hD hDcard hd h0 _hrect hcap
  have hscale :
      (A.card : ℝ) = (KA A : ℝ) * (D.card : ℝ) :=
    ka_scale_from_maximal_dissociated_proposed A D hDcard hdim
  have hK : (1 : ℝ) ≤ (KA A : ℝ) :=
    one_le_ka_of_maximal_dissociated_proposed
      A D hDsubA hDcard hdim
  exact sharpened_one_step_from_isUSF_internal
    hp A D S hUSF hDsubA hD hd h0 hcap hC_object hK hscale

/-- Unconditional campaign headline. The former Lev 2008 rectification
parameter is absent; all other hypotheses of the frozen headline remain. -/
theorem sqrt_improvement_from_isUSF_internal
    {p : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) {C : ℝ}
    (hUSF : IsUSF A)
    (hdim : 0 < dimA A)
    (hthr : 0 < Real.logb 2 (p : ℝ))
    (hM10 : 10 ≤ Real.logb 2 (Real.logb 2 (p : ℝ)))
    (hMC :
      2 * Real.logb 2 C ≤
        Real.logb 2 (Real.logb 2 (p : ℝ)))
    (hC : 1 ≤ C)
    (hC_object : 129024 ≤ C) :
    Real.sqrt
        (Real.logb 2 (Real.logb 2 (p : ℝ)) /
          sqrtChainDenominator) <
      (KA A : ℝ) := by
  exact sqrt_improvement' hp A hUSF hdim hthr hM10 hMC hC hC_object
    (o6_hstep_from_isUSF_internal hp A hUSF hdim hC_object)

end ObjectLayer
end BedertLab

#print axioms BedertLab.ObjectLayer.exists_source_fibre_selector_of_o7_cap_internal
#print axioms BedertLab.ObjectLayer.sharpened_one_step_from_isUSF_internal
#print axioms BedertLab.ObjectLayer.sqrt_improvement_from_isUSF_internal
