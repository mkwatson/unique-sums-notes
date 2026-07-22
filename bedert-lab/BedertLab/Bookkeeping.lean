/-
# Bedert lab, Milestone 2: the bookkeeping lemma

We track a generalized arithmetic progression (GAP) only through its list of
side lengths; the underlying set is never needed for the bound, so we never
formalize GAPs as subsets of a group.

* `translate` (`P ↦ P + {0, t}`) prepends a new side of length `2`.
* `cube` (`P ↦ 2P - P`) maps every side `L` to `3L - 2` and adds no sides.

The whole proof is the observation that `L ↦ 3L - 2` fixes `1`, so a side born
at length `2` that later sees `f'` cube steps has length `3 ^ f' + 1 ≤ 2 * 3 ^ f'`.
We only need the cruder per-side bound with `f' ≤ f` (the total number of cube
steps), which already gives, with `c` translate steps and `c + f = j`,

  `log₂ (∏ sides) ≤ c * (1 + f * log₂ 3) ≤ j + (j²/4) * (8/5) = 0.4 j² + j`

using `log₂ 3 ≤ 8/5` (equivalently `3⁵ = 243 ≤ 256 = 2⁸`) and `c f ≤ j² / 4`.
-/
import Mathlib

namespace BedertLab

/-! ## Phase 1: the sides-only GAP representation -/

/-- A GAP tracked only by the list of its side lengths.  Throwaway bookkeeping
device: the ambient set is deliberately not represented. -/
structure GAPSides where
  sides : List ℕ
  deriving Repr, DecidableEq

/-- The dimension of the tracked GAP. -/
def GAPSides.dim (P : GAPSides) : ℕ := P.sides.length

/-- The starting GAP `P₀ = {0}`: dimension 0, no sides. -/
def initial : GAPSides := ⟨[]⟩

/-- Translate step `P ↦ P + {0, t}`: a new side of length 2 is born. -/
def translate (P : GAPSides) : GAPSides := ⟨2 :: P.sides⟩

/-- Cube step `P ↦ 2P - P`: every side `L` becomes `3L - 2`, no new sides.
(Natural subtraction is harmless here: every side reachable from `initial`
satisfies `2 ≤ L`, see `sides_bounds`.) -/
def cube (P : GAPSides) : GAPSides := ⟨P.sides.map fun L => 3 * L - 2⟩

/-- The two operations of the iteration. -/
inductive Op
  | translate
  | cube
  deriving Repr, DecidableEq

/-- Apply one operation. -/
def Op.apply : Op → GAPSides → GAPSides
  | .translate, P => BedertLab.translate P
  | .cube, P => BedertLab.cube P

/-- `run ops` is the result of applying `ops` to `initial`; the HEAD of the
list is the operation applied LAST.  (This orientation makes "the cube steps a
side sees after being born" the cube steps strictly before it in the list,
which is what the structural induction consumes.) -/
def run : List Op → GAPSides
  | [] => initial
  | op :: ops => op.apply (run ops)

/-- Number of cube steps in an operation sequence. -/
def cubeCount : List Op → ℕ
  | [] => 0
  | .translate :: ops => cubeCount ops
  | .cube :: ops => cubeCount ops + 1

/-- Number of translate steps in an operation sequence. -/
def translateCount : List Op → ℕ
  | [] => 0
  | .translate :: ops => translateCount ops + 1
  | .cube :: ops => translateCount ops

theorem translateCount_add_cubeCount (ops : List Op) :
    translateCount ops + cubeCount ops = ops.length := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [translateCount, cubeCount] <;> omega

/-! ## Phase 2: the container lemmas

Definitional given the encoding; recorded as named lemmas so later phases can
cite them. -/

/-- A translate step adds one side of length 2 and preserves the others. -/
theorem container_translate (P : GAPSides) :
    (translate P).sides = 2 :: P.sides := rfl

/-- A translate step increases dimension by one. -/
theorem dim_translate (P : GAPSides) : (translate P).dim = P.dim + 1 := rfl

/-- A cube step maps every side `L` to `3L - 2` and adds no sides. -/
theorem container_cube (P : GAPSides) :
    (cube P).sides = P.sides.map (fun L => 3 * L - 2) := rfl

/-- A cube step preserves dimension. -/
theorem dim_cube (P : GAPSides) : (cube P).dim = P.dim := by
  simp [GAPSides.dim, cube]

/-- The dimension after `j` steps is the number of translate steps taken. -/
theorem run_dim (ops : List Op) : (run ops).dim = translateCount ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op <;>
      simp only [run, Op.apply, translate, cube, translateCount, GAPSides.dim,
        List.length_cons, List.length_map] at ih ⊢ <;> omega

/-! ## Phase 3: the bookkeeping bound -/

/-- Every side after running `ops` is at least 2 (so natural subtraction in
`cube` never truncated) and at most `2 * 3 ^ (number of cube steps)`.

The upper bound is the coarse form of "a side born at 2 seeing `f'` later cube
steps has length `3 ^ f' + 1 ≤ 2 * 3 ^ f' ≤ 2 * 3 ^ f`". -/
theorem sides_bounds (ops : List Op) :
    ∀ L ∈ (run ops).sides, 2 ≤ L ∧ L ≤ 2 * 3 ^ cubeCount ops := by
  induction ops with
  | nil => intro L hL; simp [run, initial] at hL
  | cons op ops ih =>
    cases op with
    | translate =>
      intro L hL
      simp only [run, Op.apply, translate, List.mem_cons] at hL
      rcases hL with rfl | hmem
      · exact ⟨le_refl 2, by
          have h1 : 1 ≤ 3 ^ cubeCount (.translate :: ops) :=
            Nat.one_le_pow _ _ (by norm_num)
          omega⟩
      · simpa [cubeCount] using ih L hmem
    | cube =>
      intro L hL
      simp only [run, Op.apply, cube, List.mem_map] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      obtain ⟨h2, hub⟩ := ih L' hL'
      refine ⟨by omega, ?_⟩
      calc 3 * L' - 2 ≤ 3 * L' := Nat.sub_le _ _
        _ ≤ 3 * (2 * 3 ^ cubeCount ops) := Nat.mul_le_mul_left 3 hub
        _ = 2 * 3 ^ cubeCount (.cube :: ops) := by
            simp only [cubeCount]; rw [pow_succ]; ring

/-- Every side is positive, hence so is the product of sides. -/
theorem prod_sides_pos (ops : List Op) : 0 < (run ops).sides.prod :=
  List.prod_pos fun L hL =>
    lt_of_lt_of_le (by norm_num) (sides_bounds ops L hL).1

/-- The product of the sides is at most `(2 * 3 ^ f) ^ c` where `c` counts
translate steps and `f` counts cube steps. -/
theorem prod_sides_le (ops : List Op) :
    (run ops).sides.prod
      ≤ (2 * 3 ^ cubeCount ops) ^ translateCount ops := by
  have hlen : (run ops).sides.length = translateCount ops := run_dim ops
  calc (run ops).sides.prod
      ≤ (2 * 3 ^ cubeCount ops) ^ (run ops).sides.length :=
        List.prod_le_pow_card _ _ fun L hL => (sides_bounds ops L hL).2
    _ = (2 * 3 ^ cubeCount ops) ^ translateCount ops := by rw [hlen]

/-- `log₂ 3 ≤ 8/5`, because `3⁵ = 243 ≤ 256 = 2⁸`. -/
theorem logb_two_three_le : Real.logb 2 3 ≤ 8 / 5 := by
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h1 : Real.log 243 = 5 * Real.log 3 := by
    rw [show (243 : ℝ) = 3 ^ 5 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have h3 : Real.log 243 ≤ Real.log 256 := by gcongr; norm_num
  linarith

/-- **The bookkeeping lemma** (Milestone 2 headline).  After any sequence of
`j` translate/cube steps from `P₀ = {0}`,

  `log₂ (∏ sides) ≤ 0.4 j² + j`. -/
theorem bookkeeping (ops : List Op) :
    Real.logb 2 ((run ops).sides.prod : ℝ)
      ≤ 0.4 * (ops.length : ℝ) ^ 2 + ops.length := by
  set c := translateCount ops with hc
  set f := cubeCount ops with hf
  -- `c + f = j` as reals
  have hcf : (c : ℝ) + f = ops.length := by
    exact_mod_cast translateCount_add_cubeCount ops
  -- pass the product bound through `log₂`
  have hmono : Real.logb 2 ((run ops).sides.prod : ℝ)
      ≤ Real.logb 2 (((2 * 3 ^ f) ^ c : ℕ) : ℝ) := by
    have h := prod_sides_le ops
    gcongr
    · norm_num
    · exact_mod_cast prod_sides_pos ops
  -- compute the right-hand log
  have hcalc : Real.logb 2 (((2 * 3 ^ f) ^ c : ℕ) : ℝ)
      = c * (1 + f * Real.logb 2 3) := by
    push_cast
    rw [Real.logb_pow, Real.logb_mul (by norm_num) (by positivity),
      Real.logb_self_eq_one (by norm_num), Real.logb_pow]
  rw [hcalc] at hmono
  refine hmono.trans ?_
  -- the arithmetic: `c + c f log₂3 ≤ j + (j²/4)(8/5) = 0.4 j² + j`
  have ht : Real.logb 2 3 ≤ 8 / 5 := logb_two_three_le
  have ht0 : 0 ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hcf4 : (c : ℝ) * f ≤ (ops.length : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((c : ℝ) - f)]
  have hA : (c : ℝ) * f * Real.logb 2 3 ≤ (c : ℝ) * f * (8 / 5) :=
    mul_le_mul_of_nonneg_left ht (mul_nonneg hc0 hf0)
  nlinarith [hA, hcf4, hcf, hf0]

#print axioms bookkeeping

end BedertLab
