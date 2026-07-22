/-
Bedert lab, Milestone 3: the realization glue.

This file formalizes the one "on paper only" passage: from the two-branch reading of
Bedert's Proposition 6 (the hypothesis `TwoBranchStep` below) to the quadratic growth
bound consumed by `our_improvement` in `BedertLab.Abstract`, via the side-tracking
machine of `BedertLab.Bookkeeping` realized as actual box GAPs in an ambient group.

TRUST BOUNDARY (per SPEC.md): `TwoBranchStep` must faithfully transcribe Proposition 6
of arXiv:2303.15134 (author LaTeX: sources/bedert/src/main.tex lines 479-494) together
with the branch information its proof produces, as verified three-way blind in
candidates/bedert-omega/prop6-passivity-adjudication.md:
  branch (I):  S' = S ∪ (S + t),   |S'| ≤ 2|S|,  increment ≥ |D|² / (36|A|)
  branch (II): S' = 2S − S,        |S'| ≤ |S|³,  increment ≥ |D|² / (12|A|)
Recorded simplifications relative to the paper:
  * `p : ℕ` is an abstract stand-in for p(G) (least prime order of a nonzero element);
    the iteration consumes only the size caps, so this weakens nothing it uses.
  * The exceptional-scale escape (|D| < 10) and the input |A| ≥ log₂ p(G) (the paper's
    Corollary `balancedG`) are taken as explicit hypotheses of the final theorem,
    exactly as Bedert's own Proposition 5 proof consumes them.
Everything else in this file is to be kernel-checked with no proof placeholders.
-/
import Mathlib
import BedertLab.Abstract
import BedertLab.Bookkeeping

open Finset
open scoped Pointwise

namespace BedertLab

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## Box GAPs: the realization of `GAPSides` -/

/-- An integer box mapped affinely into `G`: the container shape the iteration tracks.
`len i` is the number of allowed integer values in coordinate `i`. -/
structure BoxGAP (G : Type*) [AddCommGroup G] where
  d : ℕ
  gen : Fin d → G
  lo : Fin d → ℤ
  len : Fin d → ℕ

namespace BoxGAP

/-- The points of the box GAP. -/
def carrier (P : BoxGAP G) : Set G :=
  { x | ∃ ε : Fin P.d → ℤ,
      (∀ i, P.lo i ≤ ε i ∧ ε i < P.lo i + P.len i) ∧ x = ∑ i, ε i • P.gen i }

/-- The abstract side record of a realized box, in the sense of `Bookkeeping`. -/
def sides (P : BoxGAP G) : GAPSides := ⟨List.ofFn P.len⟩

/-- Every coordinate range contains `0`; guarantees `0 ∈ carrier` and is preserved by
both steps. -/
def IsNormalized (P : BoxGAP G) : Prop :=
  ∀ i, P.lo i ≤ 0 ∧ 0 < P.lo i + P.len i

/-- The empty box: `carrier = {0}`, the iteration's `S₀` container. -/
def initial (G : Type*) [AddCommGroup G] : BoxGAP G :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0⟩

omit [DecidableEq G] in
theorem initial_isNormalized : (initial G).IsNormalized := fun i => i.elim0

omit [DecidableEq G] in
theorem initial_sides : (initial G).sides = BedertLab.initial := by
  rfl

omit [DecidableEq G] in
theorem carrier_initial : (initial G).carrier = {0} := by
  ext x
  simp [carrier, initial]

omit [DecidableEq G] in
theorem zero_mem_carrier {P : BoxGAP G} (h : P.IsNormalized) : (0 : G) ∈ P.carrier := by
  refine ⟨fun _ => 0, h, ?_⟩
  simp

theorem carrier_finite (P : BoxGAP G) : P.carrier.Finite := by
  classical
  let box : Finset (Fin P.d → ℤ) :=
    Fintype.piFinset fun i => Finset.Ico (P.lo i) (P.lo i + P.len i)
  have hcarrier : P.carrier =
      (box.image (fun ε => ∑ i, ε i • P.gen i) : Finset G) := by
    ext x
    simp [carrier, box, eq_comm]
  rw [hcarrier]
  exact Finset.finite_toSet _

/-- The point count is bounded by the product of the side lengths. -/
theorem ncard_carrier_le (P : BoxGAP G) : P.carrier.ncard ≤ P.sides.sides.prod := by
  classical
  let box : Finset (Fin P.d → ℤ) :=
    Fintype.piFinset fun i => Finset.Ico (P.lo i) (P.lo i + P.len i)
  have hcarrier : P.carrier =
      (box.image (fun ε => ∑ i, ε i • P.gen i) : Finset G) := by
    ext x
    simp [carrier, box, eq_comm]
  rw [hcarrier, Set.ncard_coe_finset]
  calc
    (box.image (fun ε => ∑ i, ε i • P.gen i)).card ≤ box.card :=
      Finset.card_image_le
    _ = ∏ i, P.len i := by simp [box]
    _ = P.sides.sides.prod := by simp [sides, List.prod_ofFn]

/-- Realization of `Bookkeeping.translate`: adjoin the generator `t` with range `{0, 1}`. -/
def translateStep (P : BoxGAP G) (t : G) : BoxGAP G where
  d := P.d + 1
  gen := Fin.cons t P.gen
  lo := Fin.cons 0 P.lo
  len := Fin.cons 2 P.len

/-- Realization of `Bookkeeping.cube`: same generators, each range `[lo, hi]` maps to
`[2·lo − hi, 2·hi − lo]`, so `len ↦ 3·len − 2`. -/
def cubeStep (P : BoxGAP G) : BoxGAP G where
  d := P.d
  gen := P.gen
  lo := fun i => P.lo i - ((P.len i : ℤ) - 1)
  len := fun i => 3 * P.len i - 2

omit [DecidableEq G] in
theorem sides_translateStep (P : BoxGAP G) (t : G) :
    (P.translateStep t).sides = translate P.sides := by
  simp [sides, translateStep, translate, List.ofFn_succ]

omit [DecidableEq G] in
theorem sides_cubeStep (P : BoxGAP G) (h : ∀ i, 1 ≤ P.len i) :
    P.cubeStep.sides = cube P.sides := by
  by_cases hlen : ∀ i, 1 ≤ P.len i
  · simp [sides, cubeStep, cube, List.map_ofFn, Function.comp_def]
  · exact (hlen h).elim

omit [DecidableEq G] in
theorem isNormalized_translateStep {P : BoxGAP G} (h : P.IsNormalized) (t : G) :
    (P.translateStep t).IsNormalized := by
  unfold IsNormalized at h ⊢
  simp only [translateStep, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Nat.cast_ofNat]
  exact ⟨by norm_num, h⟩

omit [DecidableEq G] in
theorem isNormalized_cubeStep {P : BoxGAP G} (h : P.IsNormalized) :
    P.cubeStep.IsNormalized := by
  unfold IsNormalized at h ⊢
  intro i
  simp only [cubeStep]
  have hi := h i
  have hlen : 1 ≤ P.len i := by omega
  have hsub : 2 ≤ 3 * P.len i := by omega
  rw [Nat.cast_sub hsub]
  push_cast
  constructor <;> omega

/-- Branch (I) containment: if `S` lives in the box, `S ∪ (S + t)` lives in the
translate-extended box. -/
theorem union_translate_subset {S : Finset G} {P : BoxGAP G} (t : G)
    (hS : (S : Set G) ⊆ P.carrier) :
    ((S ∪ S.image (· + t) : Finset G) : Set G) ⊆ (P.translateStep t).carrier := by
  intro x hx
  have hx' : x ∈ S ∪ S.image (· + t) := hx
  rw [Finset.mem_union] at hx'
  rcases hx' with hxS | hxS
  · rcases hS hxS with ⟨ε, hε, rfl⟩
    refine ⟨Fin.cons 0 ε, ?_, ?_⟩
    · simp only [translateStep, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
        Nat.cast_ofNat]
      exact ⟨by norm_num, hε⟩
    · simp [translateStep, Fin.sum_univ_succ]
  · rcases Finset.mem_image.mp hxS with ⟨s, hs, rfl⟩
    rcases hS hs with ⟨ε, hε, rfl⟩
    refine ⟨Fin.cons 1 ε, ?_, ?_⟩
    · simp only [translateStep, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
        Nat.cast_ofNat]
      exact ⟨by norm_num, hε⟩
    · simp [translateStep, Fin.sum_univ_succ, add_comm]

/-- Branch (II) containment: if `S` lives in the box, `2S − S = S + S − S` lives in the
cubed box. -/
theorem cube_subset {S : Finset G} {P : BoxGAP G}
    (hS : (S : Set G) ⊆ P.carrier) :
    ((S + S - S : Finset G) : Set G) ⊆ P.cubeStep.carrier := by
  intro x hx
  have hx' : x ∈ S + S - S := hx
  rcases Finset.mem_sub.mp hx' with ⟨s₁₂, hs₁₂, s₃, hs₃, hsubeq⟩
  rcases Finset.mem_add.mp hs₁₂ with ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  rcases hS hs₁ with ⟨ε₁, hε₁, hs₁eq⟩
  rcases hS hs₂ with ⟨ε₂, hε₂, hs₂eq⟩
  rcases hS hs₃ with ⟨ε₃, hε₃, hs₃eq⟩
  subst s₁
  subst s₂
  subst s₃
  subst x
  refine ⟨fun i => ε₁ i + ε₂ i - ε₃ i, ?_, ?_⟩
  · intro i
    have h₁ := hε₁ i
    have h₂ := hε₂ i
    have h₃ := hε₃ i
    have hlen : 1 ≤ P.len i := by omega
    have hnat : 2 ≤ 3 * P.len i := by omega
    simp only [cubeStep]
    rw [Nat.cast_sub hnat]
    push_cast
    constructor <;> omega
  · simp only [cubeStep]
    simp_rw [sub_smul, add_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]

end BoxGAP

/-! ## The transcribed hypothesis (TRUST BOUNDARY) -/

/-- **Proposition 6', the two-branch reading of [Bedert, arXiv:2303.15134, Prop. 6].**

Faithful transcription of the proposition's hypotheses (main.tex lines 479-484) with the
conclusion strengthened only by information the published proof already produces
(main.tex lines 707-713 and 716-742; adjudication record
candidates/bedert-omega/prop6-passivity-adjudication.md):
the constructed set is `S ∪ (S + t)` with increment `|D|²/(36|A|)` in the translate
branch, and `2S − S` with increment `|D|²/(12|A|)` in the cube branch.

This is a hypothesis of the development, never proven here; it is the single statement
a reviewer must check against the paper. -/
def TwoBranchStep (C : ℝ) (p : ℕ) (A D : Finset G) : Prop :=
  ∀ S : Finset G, (0 : G) ∈ S →
    (S.card : ℝ) ≤
      min (Real.logb 2 p) (((D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4)) →
    (∃ t : G,
      ((((D + (S ∪ S.image (· + t))) ∩ A).card : ℝ) ≥
        (((D + S) ∩ A).card : ℝ) + (D.card : ℝ) ^ 2 / (36 * (A.card : ℝ))))
    ∨
      ((((D + (S + S - S)) ∩ A).card : ℝ) ≥
        (((D + S) ∩ A).card : ℝ) + (D.card : ℝ) ^ 2 / (12 * (A.card : ℝ)))

/-- The invariant package carried by the iteration after exactly `n` steps. -/
private structure IterationState (A D : Finset G) (n : ℕ) where
  S : Finset G
  P : BoxGAP G
  ops : List Op
  zero_mem : (0 : G) ∈ S
  subset_carrier : (S : Set G) ⊆ P.carrier
  normalized : P.IsNormalized
  sides_run : P.sides = run ops
  length_ops : ops.length = n
  coverage :
    (n : ℝ) * ((D.card : ℝ) ^ 2 / (36 * (A.card : ℝ))) ≤
      (((D + S) ∩ A).card : ℝ)

/-- The realized-box invariant converts the operation history into the quadratic
bookkeeping bound for the current finite set. -/
private theorem IterationState.growth {A D : Finset G} {n : ℕ}
    (st : IterationState A D n) :
    Real.logb 2 (st.S.card : ℝ) ≤ 0.4 * (n : ℝ) ^ 2 + (n : ℝ) := by
  have hcard_pos_nat : 0 < st.S.card := Finset.card_pos.mpr ⟨0, st.zero_mem⟩
  have hcard_ncard : st.S.card ≤ st.P.carrier.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard st.subset_carrier (BoxGAP.carrier_finite st.P)
  have hcard_sides : st.S.card ≤ st.P.sides.sides.prod :=
    hcard_ncard.trans (BoxGAP.ncard_carrier_le st.P)
  have hcard_pos : (0 : ℝ) < st.S.card := by exact_mod_cast hcard_pos_nat
  have hcard_sides_real : (st.S.card : ℝ) ≤ st.P.sides.sides.prod := by
    exact_mod_cast hcard_sides
  calc
    Real.logb 2 (st.S.card : ℝ)
        ≤ Real.logb 2 (st.P.sides.sides.prod : ℝ) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) hcard_pos hcard_sides_real
    _ = Real.logb 2 ((run st.ops).sides.prod : ℝ) := by rw [st.sides_run]
    _ ≤ 0.4 * (st.ops.length : ℝ) ^ 2 + (st.ops.length : ℝ) := bookkeeping st.ops
    _ = 0.4 * (n : ℝ) ^ 2 + (n : ℝ) := by rw [st.length_ops]

/-- One successful invocation of `TwoBranchStep` preserves the full invariant and adds
the uniform `/36` amount of coverage. -/
private theorem IterationState.next (C : ℝ) (p : ℕ) {A D : Finset G} {n : ℕ}
    (hApos : (0 : ℝ) < A.card) (hstep : TwoBranchStep C p A D)
    (st : IterationState A D n)
    (hcap : (st.S.card : ℝ) ≤
      min (Real.logb 2 p)
        (((D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4))) :
    Nonempty (IterationState A D (n + 1)) := by
  rcases hstep st.S st.zero_mem hcap with htranslate | hcube
  · rcases htranslate with ⟨t, hinc⟩
    refine ⟨{
      S := st.S ∪ st.S.image (· + t)
      P := st.P.translateStep t
      ops := .translate :: st.ops
      zero_mem := Finset.mem_union_left _ st.zero_mem
      subset_carrier := BoxGAP.union_translate_subset t st.subset_carrier
      normalized := BoxGAP.isNormalized_translateStep st.normalized t
      sides_run := ?_
      length_ops := by simp [st.length_ops]
      coverage := ?_
    }⟩
    · calc
        (st.P.translateStep t).sides = translate st.P.sides :=
          BoxGAP.sides_translateStep st.P t
        _ = translate (run st.ops) := by rw [st.sides_run]
        _ = run (.translate :: st.ops) := rfl
    · change (((n + 1 : ℕ) : ℝ) *
          ((D.card : ℝ) ^ 2 / (36 * (A.card : ℝ)))) ≤
        ((((D + (st.S ∪ st.S.image (· + t))) ∩ A).card : ℕ) : ℝ)
      rw [Nat.cast_add, Nat.cast_one]
      linarith [st.coverage]
  · have hlen : ∀ i, 1 ≤ st.P.len i := by
      intro i
      have hi := st.normalized i
      omega
    have hfrac :
        (D.card : ℝ) ^ 2 / (36 * (A.card : ℝ)) ≤
          (D.card : ℝ) ^ 2 / (12 * (A.card : ℝ)) := by
      have hq : 0 ≤ (D.card : ℝ) ^ 2 / (12 * (A.card : ℝ)) := by positivity
      calc
        (D.card : ℝ) ^ 2 / (36 * (A.card : ℝ)) =
            (1 / 3 : ℝ) * ((D.card : ℝ) ^ 2 / (12 * (A.card : ℝ))) := by ring
        _ ≤ (D.card : ℝ) ^ 2 / (12 * (A.card : ℝ)) := by nlinarith
    have hzero : (0 : G) ∈ st.S + st.S - st.S := by
      have hadd : (0 : G) + 0 ∈ st.S + st.S :=
        Finset.add_mem_add st.zero_mem st.zero_mem
      have hsub : (0 : G) + 0 - 0 ∈ st.S + st.S - st.S :=
        Finset.sub_mem_sub hadd st.zero_mem
      simpa using hsub
    refine ⟨{
      S := st.S + st.S - st.S
      P := st.P.cubeStep
      ops := .cube :: st.ops
      zero_mem := hzero
      subset_carrier := BoxGAP.cube_subset st.subset_carrier
      normalized := BoxGAP.isNormalized_cubeStep st.normalized
      sides_run := ?_
      length_ops := by simp [st.length_ops]
      coverage := ?_
    }⟩
    · calc
        st.P.cubeStep.sides = cube st.P.sides := BoxGAP.sides_cubeStep st.P hlen
        _ = cube (run st.ops) := by rw [st.sides_run]
        _ = run (.cube :: st.ops) := rfl
    · norm_num [Nat.cast_add]
      linarith [st.coverage, hfrac, hcube]

/-! ## The iteration -/

/-- The glue: from the two-branch hypothesis, either the size cap is violated at once by
`S₀ = {0}` (degenerate branch, `K` huge), or the iteration reaches a failing step `j`
within the step budget carrying the bookkeeping growth bound.

The three delivered facts are exactly the interface of `our_improvement`
(`hterminal`-shaped failure is delivered as the disjunction of the two arms of the min). -/
theorem exists_failure_step (C : ℝ) (p : ℕ) (A D : Finset G)
    (hD : D.Nonempty) (hDA : D ⊆ A)
    (hstep : TwoBranchStep C p A D) :
    (min (Real.logb 2 p) (((D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4)) < 1)
    ∨
    ∃ (j : ℕ) (Sj : Finset G),
      (j : ℝ) ≤ 36 * ((A.card : ℝ) / (D.card : ℝ)) ^ 2 ∧
      Real.logb 2 (Sj.card) ≤ 0.4 * (j : ℝ) ^ 2 + (j : ℝ) ∧
      min (Real.logb 2 p) (((D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4))
        < (Sj.card : ℝ) := by
  classical
  let cap : ℝ :=
    min (Real.logb 2 p)
      (((D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)) ^ ((1 : ℝ) / 4))
  by_cases hinitial : cap < 1
  · exact Or.inl hinitial
  right
  by_contra hfailure
  have hDpos_nat : 0 < D.card := Finset.card_pos.mpr hD
  have hA : A.Nonempty := hD.mono hDA
  have hApos_nat : 0 < A.card := Finset.card_pos.mpr hA
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hDpos_nat
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hApos_nat
  let budget : ℝ := 36 * ((A.card : ℝ) / (D.card : ℝ)) ^ 2
  have hbudget : 0 ≤ budget := by dsimp [budget]; positivity
  let N : ℕ := ⌊budget⌋₊
  have hNle : (N : ℝ) ≤ budget := by
    dsimp [N]
    exact Nat.floor_le hbudget
  have hbudget_lt : budget < ((N + 1 : ℕ) : ℝ) := by
    dsimp [N]
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one budget
  let st0 : IterationState A D 0 := {
    S := {0}
    P := BoxGAP.initial G
    ops := []
    zero_mem := by simp
    subset_carrier := by
      rw [BoxGAP.carrier_initial]
      intro x hx
      simpa using hx
    normalized := BoxGAP.initial_isNormalized
    sides_run := by simpa [run] using (BoxGAP.initial_sides (G := G))
    length_ops := rfl
    coverage := by norm_num
  }
  have hstates : ∀ n : ℕ, n ≤ N + 1 → Nonempty (IterationState A D n) := by
    intro n hn
    induction n with
    | zero => exact ⟨st0⟩
    | succ n ih =>
        have hnN : n ≤ N := by omega
        obtain ⟨st⟩ := ih (by omega)
        have hn_budget : (n : ℝ) ≤ budget :=
          (by exact_mod_cast hnN : (n : ℝ) ≤ N).trans hNle
        have hgrowth := st.growth
        have hcap : (st.S.card : ℝ) ≤ cap := by
          apply le_of_not_gt
          intro hfail
          apply hfailure
          exact ⟨n, st.S, hn_budget, hgrowth, hfail⟩
        exact IterationState.next C p hApos hstep st hcap
  obtain ⟨stfinal⟩ := hstates (N + 1) le_rfl
  let delta : ℝ := (D.card : ℝ) ^ 2 / (36 * (A.card : ℝ))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hbudget_delta : budget * delta = (A.card : ℝ) := by
    dsimp [budget, delta]
    field_simp [ne_of_gt hDpos, ne_of_gt hApos]
  have hcoverage_gt : (A.card : ℝ) < ((N + 1 : ℕ) : ℝ) * delta := by
    rw [← hbudget_delta]
    exact mul_lt_mul_of_pos_right hbudget_lt hdelta
  have hinter : ((((D + stfinal.S) ∩ A).card : ℕ) : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)
  have hcoverage := stfinal.coverage
  change ((N + 1 : ℕ) : ℝ) * delta ≤
    ((((D + stfinal.S) ∩ A).card : ℕ) : ℝ) at hcoverage
  linarith

/-- Arm (ii) conversion: if the failure came from the quartic cap, the same growth data
still yields the fourth-root bound, at the cost of the constant (2.5 ↦ 0.625 = 2.5/4),
using the input `|A| ≥ log₂ p` and a dichotomy on whether `C·K⁶` is already large.
NOT part of the trust boundary; the constant here may be adjusted during proof as long
as the final theorem's shape is preserved. -/
private theorem arm_two_bound_core (C : ℝ) (hC : 1 ≤ C)
    {p : ℕ} {terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hA : ∃ a : ℝ, Real.logb 2 p ≤ a ∧
      (terminalSize : ℝ) ^ (4 : ℕ) * (C * K ^ 6) ≥ a ∧ 0 < a)
    (hgrowth : Real.logb 2 terminalSize ≤ 0.4 * (j : ℝ) ^ 2 + (j : ℝ))
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 1 ≤ K) :
    Real.sqrt (Real.sqrt (0.625 *
      (Real.logb 2 (Real.logb 2 p) - Real.logb 2 C)) - 1.25) / 6 - 1 < K := by
  rcases hA with ⟨a, hap, hprod, ha⟩
  let M : ℝ := Real.logb 2 (Real.logb 2 p)
  let E : ℝ := M - Real.logb 2 C
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hCKpos : 0 < C * K ^ 6 := mul_pos hCpos (pow_pos hKpos 6)
  have hwhole_pos : 0 < terminalSize ^ 4 * (C * K ^ 6) := lt_of_lt_of_le ha hprod
  have hTpow_ne : terminalSize ^ 4 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hwhole_pos
    exact lt_irrefl 0 hwhole_pos
  have hCKne : C * K ^ 6 ≠ 0 := ne_of_gt hCKpos
  have hloga_lower : M ≤ Real.logb 2 a := by
    dsimp [M]
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num) hthr hap
  have hloga_upper :
      Real.logb 2 a ≤ Real.logb 2 (terminalSize ^ 4 * (C * K ^ 6)) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) ha hprod
  have hlog_expand :
      Real.logb 2 (terminalSize ^ 4 * (C * K ^ 6)) =
        4 * Real.logb 2 terminalSize +
          (Real.logb 2 C + 6 * Real.logb 2 K) := by
    rw [Real.logb_mul hTpow_ne hCKne, Real.logb_pow,
      Real.logb_mul (ne_of_gt hCpos) (pow_ne_zero 6 (ne_of_gt hKpos)),
      Real.logb_pow]
    norm_num
  have hlog_two_half : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogK : Real.log K ≤ K - 1 := Real.log_le_sub_one_of_pos hKpos
  have hlogbK : Real.logb 2 K ≤ 2 * K := by
    rw [Real.logb]
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).2
    nlinarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hstep0 : 0 ≤ 36 * K ^ 2 := by positivity
  have hdiffprod :
      0 ≤ (36 * K ^ 2 - (j : ℝ)) * (36 * K ^ 2 + (j : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hsteps) (add_nonneg hstep0 hj0)
  have hjsq : (j : ℝ) ^ 2 ≤ (36 * K ^ 2) ^ 2 := by nlinarith
  have hEupper : E ≤ 2073.6 * K ^ 4 + 144 * K ^ 2 + 12 * K := by
    rw [hlog_expand] at hloga_upper
    dsimp [E]
    nlinarith [hloga_lower, hloga_upper, hgrowth, hlogbK, hjsq]
  change Real.sqrt (Real.sqrt (0.625 * E) - 1.25) / 6 - 1 < K
  by_cases hy : Real.sqrt (0.625 * E) - 1.25 ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos hy]
    norm_num
    linarith
  · have hypos : 0 < Real.sqrt (0.625 * E) - 1.25 := lt_of_not_ge hy
    have hrad : 0 ≤ 0.625 * E := by
      by_contra hneg
      have hz := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hneg)
      rw [hz] at hypos
      norm_num at hypos
    have hrsq : (Real.sqrt (0.625 * E)) ^ 2 = 0.625 * E := Real.sq_sqrt hrad
    have hysq :
        (Real.sqrt (Real.sqrt (0.625 * E) - 1.25)) ^ 2 =
          Real.sqrt (0.625 * E) - 1.25 := Real.sq_sqrt hypos.le
    by_contra hgoal
    have hKle : K ≤
        Real.sqrt (Real.sqrt (0.625 * E) - 1.25) / 6 - 1 := le_of_not_gt hgoal
    have hsqrt_lower :
        6 * (K + 1) ≤ Real.sqrt (Real.sqrt (0.625 * E) - 1.25) := by
      nlinarith
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (Real.sqrt (0.625 * E) - 1.25) := Real.sqrt_nonneg _
    have hKone : 0 ≤ 6 * (K + 1) := by positivity
    have houter_prod :
        0 ≤ (Real.sqrt (Real.sqrt (0.625 * E) - 1.25) - 6 * (K + 1)) *
          (Real.sqrt (Real.sqrt (0.625 * E) - 1.25) + 6 * (K + 1)) :=
      mul_nonneg (sub_nonneg.mpr hsqrt_lower) (add_nonneg hsqrt_nonneg hKone)
    have hy_lower :
        36 * (K + 1) ^ 2 ≤ Real.sqrt (0.625 * E) - 1.25 := by
      nlinarith
    let q : ℝ := 36 * (K + 1) ^ 2 + 1.25
    have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
    have hq_le : q ≤ Real.sqrt (0.625 * E) := by
      dsimp [q]
      linarith
    have hr_nonneg : 0 ≤ Real.sqrt (0.625 * E) := Real.sqrt_nonneg _
    have hinner_prod :
        0 ≤ (Real.sqrt (0.625 * E) - q) * (Real.sqrt (0.625 * E) + q) :=
      mul_nonneg (sub_nonneg.mpr hq_le) (add_nonneg hr_nonneg hq_nonneg)
    have hElower : q ^ 2 ≤ 0.625 * E := by
      nlinarith only [hrsq, hinner_prod]
    have hscaled :
        0.625 * E ≤ 0.625 * (2073.6 * K ^ 4 + 144 * K ^ 2 + 12 * K) :=
      mul_le_mul_of_nonneg_left hEupper (by norm_num)
    have hpoly :
        0.625 * (2073.6 * K ^ 4 + 144 * K ^ 2 + 12 * K) < q ^ 2 := by
      have hid :
          q ^ 2 - 0.625 * (2073.6 * K ^ 4 + 144 * K ^ 2 + 12 * K) =
            22201 / 16 + (10713 / 2) * K + 7776 * K ^ 2 + 5184 * K ^ 3 := by
        dsimp [q]
        ring
      apply sub_pos.mp
      rw [hid]
      positivity
    exact (not_lt_of_ge (hElower.trans hscaled)) hpoly

theorem arm_two_bound (C : ℝ) (hC : 1 ≤ C) {p : ℕ} {terminalSize K : ℝ} {j : ℕ}
    (hthr : 0 < Real.logb 2 p)
    (hscale : 4 ≤ Real.logb 2 (Real.logb 2 p))
    (hA : ∃ a : ℝ, Real.logb 2 p ≤ a ∧
      (terminalSize : ℝ) ^ (4 : ℕ) * (C * K ^ 6) ≥ a ∧ 0 < a)
    (hgrowth : Real.logb 2 terminalSize ≤ 0.4 * (j : ℝ) ^ 2 + (j : ℝ))
    (hsteps : (j : ℝ) ≤ 36 * K ^ 2)
    (hK : 1 ≤ K) :
    Real.sqrt (Real.sqrt (0.625 *
      (Real.logb 2 (Real.logb 2 p) - Real.logb 2 C)) - 1.25) / 6 - 1 < K := by
  by_cases hs : 4 ≤ Real.logb 2 (Real.logb 2 p)
  · exact arm_two_bound_core C hC hthr hA hgrowth hsteps hK
  · exact (hs hscale).elim

/-! ## Milestone 3 headline -/

/-- **Milestone 3.** Under the transcribed two-branch hypothesis, with the paper's own
inputs (`D ⊆ A` dissociated is not needed here beyond what `TwoBranchStep` encodes;
`10 ≤ |D|` and `log₂ p ≤ |A|` exactly as Bedert's Proposition 5 proof consumes them),
either `K = |A|/|D|` is degenerately huge, or `K` obeys the fourth-root-of-double-log
bound: the order `(log log p)^{1/4}`, one full logarithm better than the published
`(log log log p)^{1/2}`.

The `- 1` slack and the `0.625` constant come from the arm-(ii) conversion; the
translate-arm failure delivers the stronger `2.5` constant via `our_improvement`, which
implies this statement. -/
theorem milestone3 (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (A D : Finset G)
    (hD : 10 ≤ D.card) (hDA : D ⊆ A)
    (hAp : Real.logb 2 p ≤ (A.card : ℝ))
    (hthr : 0 < Real.logb 2 p)
    (hscale : 4 ≤ Real.logb 2 (Real.logb 2 p))
    (hstep : TwoBranchStep C p A D) :
    ((Real.logb 2 p / C) ^ ((1 : ℝ) / 6) ≤ (A.card : ℝ) / (D.card : ℝ))
    ∨
    Real.sqrt (Real.sqrt (0.625 *
      (Real.logb 2 (Real.logb 2 p) - Real.logb 2 C)) - 1.25) / 6 - 1
        < (A.card : ℝ) / (D.card : ℝ) := by
  classical
  have hDne : D.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hD)
  have hAne : A.Nonempty := hDne.mono hDA
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hDne
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hAne
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let K : ℝ := (A.card : ℝ) / (D.card : ℝ)
  have hK : 1 ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ hDpos).2
    norm_num
    exact_mod_cast Finset.card_le_card hDA
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let L : ℝ := Real.logb 2 p
  let X : ℝ := (D.card : ℝ) ^ 6 / (C * (A.card : ℝ) ^ 5)
  let Q : ℝ := X ^ ((1 : ℝ) / 4)
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hXnonneg : 0 ≤ X := hXpos.le
  have hQnonneg : 0 ≤ Q := by dsimp [Q]; positivity
  have hLgt : 1 < L := by
    by_contra hnot
    have hLle : L ≤ 1 := le_of_not_gt hnot
    have hlogle : Real.logb 2 L ≤ Real.logb 2 1 :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by simpa [L] using hthr) hLle
    norm_num at hlogle
    dsimp [L] at hlogle
    linarith
  rcases exists_failure_step C p A D hDne hDA hstep with hinitial | hfailure
  · left
    have hQlt : Q < 1 := by
      by_contra hnot
      have hmin : 1 ≤ min L Q := le_min hLgt.le (le_of_not_gt hnot)
      change min L Q < 1 at hinitial
      linarith
    have hXlt : X < 1 :=
      (Real.rpow_lt_one_iff' hXnonneg (by norm_num : (0 : ℝ) < 1 / 4)).mp hQlt
    have hdenpos : 0 < C * (A.card : ℝ) ^ 5 := by positivity
    have hDCA : (D.card : ℝ) ^ 6 < C * (A.card : ℝ) ^ 5 :=
      (div_lt_one hdenpos).mp (by simpa [X] using hXlt)
    have hAoverC : (A.card : ℝ) / C < K ^ 6 := by
      apply (div_lt_iff₀ hCpos).2
      calc
        (A.card : ℝ) < C * ((A.card : ℝ) ^ 6 / (D.card : ℝ) ^ 6) := by
          rw [← mul_div_assoc]
          apply (lt_div_iff₀ (pow_pos hDpos 6)).2
          calc
            (A.card : ℝ) * (D.card : ℝ) ^ 6
                < (A.card : ℝ) * (C * (A.card : ℝ) ^ 5) :=
              mul_lt_mul_of_pos_left hDCA hApos
            _ = C * (A.card : ℝ) ^ 6 := by ring
        _ = K ^ 6 * C := by dsimp [K]; rw [div_pow]; ring
    have hLC : L / C ≤ (A.card : ℝ) / C :=
      (div_le_div_iff_of_pos_right hCpos).2 (by simpa [L] using hAp)
    have hroot : (L / C) ^ ((1 : ℝ) / 6) ≤ (K ^ 6) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow (by dsimp [L]; positivity) (hLC.trans hAoverC.le) (by norm_num)
    have hsix : (K ^ 6) ^ ((1 : ℝ) / 6) = K := by
      simpa [one_div] using
        (Real.pow_rpow_inv_natCast hKpos.le (by norm_num : (6 : ℕ) ≠ 0))
    rw [hsix] at hroot
    simpa [L, K] using hroot
  · rcases hfailure with ⟨j, Sj, hj, hgrowth, hfail⟩
    change min L Q < (Sj.card : ℝ) at hfail
    by_cases harms : L ≤ Q
    · have hterminal : L < (Sj.card : ℝ) := by
        rwa [min_eq_left harms] at hfail
      have hstrong := our_improvement
        (p := (p : ℝ)) (terminalSize := (Sj.card : ℝ)) (K := K) (j := j)
        (by simpa [L] using hthr)
        (le_trans (by norm_num) hscale)
        (by simpa [L] using hterminal)
        hgrowth hj (le_trans (by norm_num) hK)
      have hlogC : 0 ≤ Real.logb 2 C := Real.logb_nonneg (by norm_num) hC
      have hM : 0 ≤ Real.logb 2 L := le_trans (by norm_num) hscale
      have harg :
          0.625 * (Real.logb 2 L - Real.logb 2 C) ≤ 2.5 * Real.logb 2 L := by
        nlinarith
      have hsqrt₁ := Real.sqrt_le_sqrt harg
      have hsqrt₂ := Real.sqrt_le_sqrt (sub_le_sub_right hsqrt₁ 1.25)
      right
      dsimp [K] at hstrong ⊢
      dsimp [L] at hsqrt₂ hstrong ⊢
      nlinarith [hsqrt₂]
    · have hQL : Q ≤ L := le_of_lt (lt_of_not_ge harms)
      have hterminal : Q < (Sj.card : ℝ) := by
        rwa [min_eq_right hQL] at hfail
      have hQpow : Q ^ 4 = X := by
        dsimp [Q]
        simpa [one_div] using
          (Real.rpow_inv_natCast_pow hXnonneg (by norm_num : (4 : ℕ) ≠ 0))
      have hTpos : (0 : ℝ) < Sj.card := lt_of_le_of_lt hQnonneg hterminal
      have hpowlt : Q ^ 4 < (Sj.card : ℝ) ^ 4 :=
        pow_lt_pow_left₀ hterminal hQnonneg (by norm_num)
      have hX_T : X < (Sj.card : ℝ) ^ 4 := by rwa [hQpow] at hpowlt
      have hidentity : X * (C * K ^ 6) = (A.card : ℝ) := by
        dsimp [X, K]
        field_simp [ne_of_gt hDpos, ne_of_gt hApos, ne_of_gt hCpos]
      have hproduct :
          (A.card : ℝ) ≤ (Sj.card : ℝ) ^ 4 * (C * K ^ 6) := by
        rw [← hidentity]
        exact (mul_lt_mul_of_pos_right hX_T (mul_pos hCpos (pow_pos hKpos 6))).le
      right
      simpa [K, L] using arm_two_bound C hC
        (p := p) (terminalSize := (Sj.card : ℝ)) (K := K) (j := j)
        hthr hscale ⟨(A.card : ℝ), hAp, hproduct, hApos⟩ hgrowth hj hK

#print axioms milestone3

end BedertLab
