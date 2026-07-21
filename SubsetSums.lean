/-
Subset sums are counted by dissociated index sets: for a finite family `z : ι → G` in an
additive abelian group, `|Σ(z)| ≤ #𝒟 ≤ ∑_{j=0}^{d} (n choose j)`, where `Σ(z)` is the set of
subset sums, `𝒟` the family of index sets whose subsets all have distinct sums, `n = |ι|`, and
`d` the largest size of a set in `𝒟`.  This sharpens Proposition 1 of Bedert, *On unique sums in
Abelian groups* (Combinatorica 44.2, 2024).  Method: for each attainable sum
take the colexicographically least index set attaining it; sets shattered by this family are
dissociated; Pajor's strengthened Sauer-Shelah lemma (`Finset.card_le_card_shatterer`) counts.
-/
import Mathlib

namespace BedertLab

open Finset

variable {ι G : Type*} [Fintype ι] [LinearOrder ι] [AddCommGroup G] [DecidableEq G]

/-- The sum of the subfamily of `z` indexed by `I`. -/
def sumOver (z : ι → G) (I : Finset ι) : G := ∑ i ∈ I, z i

/-- The set `Σ(z)` of all subset sums of the family `z`. -/
def subsetSums (z : ι → G) : Finset G := (univ : Finset ι).powerset.image (sumOver z)

/-- `I` is *dissociated* if distinct subsets of `I` have distinct sums.  This is the
`{0,1}`-coefficient notion, not Mathlib's `{-1,0,1}`-coefficient `AddDissociated`. -/
def IsDissoc (z : ι → G) (I : Finset ι) : Prop :=
  ∀ J ⊆ I, ∀ K ⊆ I, sumOver z J = sumOver z K → J = K

instance (z : ι → G) : DecidablePred (IsDissoc z) := fun I =>
  decidable_of_iff (∀ J ∈ I.powerset, ∀ K ∈ I.powerset, sumOver z J = sumOver z K → J = K)
    (by simp [IsDissoc])

omit [Fintype ι] [LinearOrder ι] [DecidableEq G] in
/-- `IsDissoc` says exactly that the subset-sum map is injective on the powerset of `I`. -/
lemma isDissoc_iff_injOn (z : ι → G) (I : Finset ι) :
    IsDissoc z I ↔ Set.InjOn (sumOver z) (I.powerset : Set (Finset ι)) := by
  simp only [Set.InjOn, mem_coe, mem_powerset]; rfl

/-- The family of all dissociated index sets. -/
def dissocFamily (z : ι → G) : Finset (Finset ι) :=
  {I ∈ (univ : Finset ι).powerset | IsDissoc z I}

/-- The maximum size of a dissociated index set. -/
def dissocDim (z : ι → G) : ℕ := (dissocFamily z).sup card

/-- The index sets that are colex-least in their fibre of the subset-sum map. -/
def minReps (z : ι → G) : Finset (Finset ι) :=
  {I ∈ (univ : Finset ι).powerset | ∀ J, sumOver z J = sumOver z I → toColex I ≤ toColex J}

/-- Every fibre of the subset-sum map contains a colex-minimal representative. -/
lemma exists_minRep (z : ι → G) (I : Finset ι) :
    ∃ R ∈ minReps z, sumOver z R = sumOver z I := by
  obtain ⟨R, hR, hmin⟩ := exists_min_image
    {J ∈ (univ : Finset ι).powerset | sumOver z J = sumOver z I} toColex ⟨I, by simp⟩
  exact ⟨R, mem_filter.2 ⟨mem_powerset.2 (subset_univ R), fun J hJ =>
    hmin J (by simp [hJ.trans (mem_filter.1 hR).2])⟩, (mem_filter.1 hR).2⟩

/-- Core of the key claim: given disjoint `P, Q ⊆ S` with equal sums and top element `m ∈ Q`,
a shattering witness `R` with `S ∩ R = Q` loses colex-minimality to `(R \ Q) ∪ P`. -/
private lemma not_shatters_aux {z : ι → G} {S P Q : Finset ι}
    (hPS : P ⊆ S) (hd : Disjoint P Q) (hsum : sumOver z P = sumOver z Q)
    (hS : (minReps z).Shatters S) (hQS : Q ⊆ S)
    {m : ι} (hmQ : m ∈ Q) (hmax : ∀ a ∈ P, a < m) : False := by
  obtain ⟨R, hRF, hRS⟩ := hS hQS
  have hQR : Q ⊆ R := hRS ▸ inter_subset_right
  have hPR : Disjoint P R := disjoint_left.2 fun a haP haR =>
    disjoint_left.1 hd haP (hRS ▸ mem_inter.2 ⟨hPS haP, haR⟩)
  have hsum' : sumOver z ((R \ Q) ∪ P) = sumOver z R := by
    simp only [sumOver] at hsum ⊢
    rw [sum_union (hPR.mono_right sdiff_subset).symm, hsum, sum_sdiff hQR]
  have hmR : m ∈ R := hQR hmQ
  have hmR' : m ∉ (R \ Q) ∪ P := fun h => (mem_union.1 h).elim
    (fun h => (mem_sdiff.1 h).2 hmQ) fun h => disjoint_left.1 hd h hmQ
  have hlt : toColex ((R \ Q) ∪ P) < toColex R := by
    rw [Colex.toColex_lt_toColex]
    exact ⟨(ne_of_mem_of_not_mem' hmR hmR').symm, fun a haU haR =>
      ⟨m, hmR, hmR', (hmax a ((mem_union.1 haU).resolve_left fun h => haR (mem_sdiff.1 h).1)).le⟩⟩
  exact lt_irrefl _ (hlt.trans_le ((mem_filter.1 hRF).2 _ hsum'))

/-- **Key claim**: every set shattered by the colex-minimal representatives is dissociated. -/
lemma isDissoc_of_shatters {z : ι → G} {S : Finset ι}
    (hS : (minReps z).Shatters S) : IsDissoc z S := by
  intro P₀ hP₀S Q₀ hQ₀S hsum₀; by_contra hne
  -- cancel the common part: `P` and `Q` are disjoint with equal sums
  set P := P₀ \ Q₀ with hPdef; set Q := Q₀ \ P₀ with hQdef
  have hPS : P ⊆ S := sdiff_subset.trans hP₀S
  have hQS : Q ⊆ S := sdiff_subset.trans hQ₀S
  have hd : Disjoint P Q := disjoint_sdiff_sdiff
  have hsub : ∀ A B : Finset ι, sumOver z (A \ B) = sumOver z A - sumOver z (A ∩ B) :=
    fun A B => by rw [← sdiff_inter_self_left]; exact sum_sdiff_eq_sub inter_subset_left
  have hsum : sumOver z P = sumOver z Q := by rw [hPdef, hQdef, hsub, hsub, inter_comm, hsum₀]
  have hUne : (P ∪ Q).Nonempty := nonempty_iff_ne_empty.2 fun h => hne (symmDiff_eq_bot.1 h)
  -- the top element of `P ∪ Q` lies in exactly one of the two; that one plays `Q` above
  obtain hmP | hmQ := mem_union.1 ((P ∪ Q).max'_mem hUne)
  · exact not_shatters_aux hQS hd.symm hsum.symm hS hPS hmP fun a haQ =>
      (le_max' _ _ (mem_union_right _ haQ)).lt_of_ne fun h => disjoint_left.1 hd hmP (h ▸ haQ)
  · exact not_shatters_aux hPS hd hsum hS hQS hmQ fun a haP =>
      (le_max' _ _ (mem_union_left _ haP)).lt_of_ne fun h => disjoint_left.1 hd haP (h.symm ▸ hmQ)

/-- **First inequality**: `|Σ(z)| ≤ #𝒟`, by Pajor's lemma applied to `minReps z`. -/
theorem card_subsetSums_le_card_dissocFamily (z : ι → G) :
    (subsetSums z).card ≤ (dissocFamily z).card :=
  calc (subsetSums z).card
      ≤ ((minReps z).image (sumOver z)).card := card_le_card fun y hy => by
        obtain ⟨I, -, rfl⟩ := mem_image.1 hy; exact mem_image.2 (exists_minRep z I)
    _ ≤ (minReps z).card := card_image_le
    _ ≤ (minReps z).shatterer.card := card_le_card_shatterer _
    _ ≤ (dissocFamily z).card := card_le_card fun S hS => mem_filter.2
        ⟨mem_powerset.2 (subset_univ S), isDissoc_of_shatters (mem_shatterer.1 hS)⟩

/-- **Second inequality**: dissociated sets have size at most `d`, giving the binomial tail. -/
theorem card_dissocFamily_le_sum_choose (z : ι → G) :
    (dissocFamily z).card ≤ ∑ j ∈ range (dissocDim z + 1), (Fintype.card ι).choose j := by
  have h : dissocFamily z ⊆ (range (dissocDim z + 1)).biUnion fun j => powersetCard j univ :=
    fun I hI => mem_biUnion.2 ⟨I.card, mem_range.2 (Nat.lt_succ_of_le (le_sup (f := card) hI)),
      mem_powersetCard_univ.2 rfl⟩
  simpa [card_powersetCard] using (card_le_card h).trans card_biUnion_le

/-- **Main theorem** (sharpens Bedert 2024, Proposition 1). -/
theorem card_subsetSums_le (z : ι → G) :
    (subsetSums z).card ≤ (dissocFamily z).card ∧
      (dissocFamily z).card ≤ ∑ j ∈ range (dissocDim z + 1), (Fintype.card ι).choose j :=
  ⟨card_subsetSums_le_card_dissocFamily z, card_dissocFamily_le_sum_choose z⟩

#print axioms card_subsetSums_le

/- Tightness, with a repeated element and `d < n`: for `![1, 1]` the chain is `3 ≤ 3 ≤ 3`. -/
example : (subsetSums ![(1 : ℤ), 1]).card = 3 ∧ (dissocFamily ![(1 : ℤ), 1]).card = 3 ∧
    dissocDim ![(1 : ℤ), 1] = 1 := by decide

end BedertLab
