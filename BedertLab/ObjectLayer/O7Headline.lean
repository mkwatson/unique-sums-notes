import BedertLab.ObjectLayer.O7fStep

namespace BedertLab
namespace ObjectLayer

/-- The campaign headline composed from the exact O7 one-step adapter and
O6 square-root iteration.

Kernel-certified from the original finite objects conditional on one
explicitly stated Lev 2008 cyclic rectification interface; the
campaign's sharpened one-bit argument and all witness reconstruction
after rectification are kernel-certified. (`hBLR` parameter name retained
unchanged; the encoded `log_2 p` threshold matches Lev 2008 Theorem 1, not
Bilu-Lev-Ruzsa's weaker `log_4 p` Theorem 3.1 at order 2. See
`candidates/bedert-omega/tailored-rectification.md` PHASE 1.2.)

Source attribution is deliberately three-way:

* Bedert's printed proposition has the outward one-bit branch but a cubic
  inward update: `sources/bedert/src/main.tex:479-494,704-765`.
* The strict inward one-bit conclusion and the exact campaign cap
  `129024` are the campaign's sharpened argument in
  `candidates/bedert-omega/note-core/prose-proof-arm1.md`.
* The independent blind arm in
  `candidates/bedert-omega/note-core/prose-proof-arm2-blind.md`
  reconstructs the four inward object inputs with the larger cap
  `8128512`; the final popular-label aggregation is the already-certified
  O5/SqrtChain bridge. The sharpened theorem is not attributed to Bedert. -/
theorem sqrt_improvement_from_isUSF_proposed
    (hBLR :
      ∀ {p : ℕ}, p.Prime →
        ∀ S : Finset (ZMod p),
          (S.card : ℝ) ≤ Real.logb 2 (p : ℝ) →
            ∃ T : Finset ℤ, ∃ φ : ZMod p → ℤ,
              IsAddFreimanIso 2 (↑S) (↑T) φ)
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
  exact sqrt_improvement' hp A hUSF hdim hthr hM10 hMC hC hC_object (o6_hstep_from_isUSF_proposed hBLR hp A hUSF hdim hC_object)

end ObjectLayer
end BedertLab
