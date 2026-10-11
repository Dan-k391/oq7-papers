import OQ7.ResourceCells
import OQ7.PhysicalModulus
import OQ7.PhysicalClass
import OQ7.FourierOpenCaps

noncomputable section
namespace OQ7
open Set MeasureTheory

theorem cell_pairIntegral_lower_of_sineComparison_Ioo {k Pglobal Qglobal Q K a b : ℝ}
    (hk : 0 < k) (hQ : 0 < Q) (hK : 0 < K) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hcap : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / K)
    (hcomp : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Real.sin (K * (y - x)) / K ≤ ‖stackFundamentalSolution k layers y x‖) :
    (Q ^ 2 / (4 * K ^ 2) * ResourceScalar.f
      (K * (∫ z in a..b, stackLossProfile layers z) / Q)) / K ^ 2 ≤
      ∫ p in {p : ℝ × ℝ | p.1 < p.2}, stackFundamentalPairKernel k layers p
        ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) := by
  let μ := volume.restrict (Ioc a b)
  let low : ℝ × ℝ → ℝ := fun p => stackLossProfile layers p.1 * stackLossProfile layers p.2 *
    Real.sin (K * (p.2 - p.1)) ^ 2
  let triangle : Set (ℝ × ℝ) := {p | p.1 < p.2}
  have htri : MeasurableSet triangle := (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hqi := stackLossProfile_intervalIntegrable a b hQglobal h
  have hlo : Integrable low (μ.prod μ) := sineSquare_product_integrable hqi
  have hhi := physicalFundamentalPair_integrable hk hQglobal h a b
  have hsupport : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ioc a b ∧ p.2 ∈ Ioc a b := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hmono : (∫ p in triangle, low p / K ^ 2 ∂μ.prod μ) ≤
      ∫ p in triangle, stackFundamentalPairKernel k layers p ∂μ.prod μ := by
    apply setIntegral_mono_on_ae (hlo.div_const (K ^ 2)).integrableOn hhi.integrableOn htri
    filter_upwards [hsupport] with p hp
    intro hpt
    exact physicalPair_sine_lower_of_comparison hQglobal h hK hlength hcomp
      (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2) hpt.le
  rw [integral_div] at hmono
  have hfourier := sineSquare_triangleIntegral_capped_Ioo hab hK hQ hlength hqi hcap
  change Q ^ 2 / (4 * K ^ 2) * ResourceScalar.f
    (K * (∫ z in a..b, stackLossProfile layers z) / Q) ≤ ∫ p in triangle, low p ∂μ.prod μ at hfourier
  exact (div_le_div_of_nonneg_right hfourier (sq_nonneg K)).trans hmono

theorem cell_det_lower_of_sineComparison_Ioo {k P Q Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hcap : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b)
    (hlength : b - a ≤ Real.pi / (k * Real.sqrt P))
    (hcomp : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Real.sin (k * Real.sqrt P * (y - x)) / (k * Real.sqrt P) ≤
        ‖stackFundamentalSolution k layers y x‖) :
    Q ^ 2 / P ^ 2 * ResourceScalar.f
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      (stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) := by
  let K := k * Real.sqrt P
  have hK : 0 < K := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hKsq : K ^ 2 = k ^ 2 * P := by
    dsimp [K]
    rw [mul_pow, Real.sq_sqrt hP.le]
  have hp := cell_pairIntegral_lower_of_sineComparison_Ioo hk hQ hK hQglobal h hcap hab hlength hcomp
  have hGramComplex := stackPhysicalGramDeterminant hk hQglobal h a b
  have hGram : (stackDepositedAbsorption k layers a b).det.re /
      Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) =
        4 * k ^ 4 * ∫ p in {p : ℝ × ℝ | p.1 < p.2}, stackFundamentalPairKernel k layers p
          ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) := by
    have hr := congrArg Complex.re hGramComplex
    simpa only [Complex.div_ofReal_re, Complex.ofReal_re] using hr
  rw [hGram]
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * k ^ 4 by positivity)
  have heq : 4 * k ^ 4 * ((Q ^ 2 / (4 * K ^ 2) * ResourceScalar.f
      (K * (∫ z in a..b, stackLossProfile layers z) / Q)) / K ^ 2) =
      Q ^ 2 / P ^ 2 * ResourceScalar.f (K * (∫ z in a..b, stackLossProfile layers z) / Q) := by
    calc
      _ = k ^ 4 * Q ^ 2 / (K ^ 2) ^ 2 * ResourceScalar.f
          (K * (∫ z in a..b, stackLossProfile layers z) / Q) := by
        field_simp
      _ = _ := by
        rw [hKsq]
        field_simp
  rw [heq] at hmul
  exact hmul

theorem cell_sqrt_det_lower_of_sineComparison_Ioo {k P Q Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hcap : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b)
    (hlength : b - a ≤ Real.pi / (k * Real.sqrt P))
    (hcomp : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Real.sin (k * Real.sqrt P * (y - x)) / (k * Real.sqrt P) ≤
        ‖stackFundamentalSolution k layers y x‖) :
    Q / P * ResourceScalar.g
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      Real.sqrt ((stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) := by
  have hdet := cell_det_lower_of_sineComparison_Ioo hk hP hQ hQglobal h hcap hab hlength hcomp
  have hroot := Real.sqrt_le_sqrt hdet
  have hcoef : Q ^ 2 / P ^ 2 = (Q / P) ^ 2 := by rw [div_pow]
  rw [hcoef, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hQ.le hP.le)] at hroot
  exact hroot

/-- Actual Lemma 4.1 supplies every pairwise comparison inside a selected short cell. -/
theorem stackFundamentalSolution_cellComparison_Ioo {k P Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) {layers : List HomogeneousLayer}
    (h : StackAdmissible Pglobal Qglobal layers)
    (hlength : b - a ≤ Real.pi / (k * Real.sqrt P))
    (hlocal : ∀ z ∈ Ioo a b, stackRealProfile layers z ≤ P) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Real.sin (k * Real.sqrt P * (y - x)) / (k * Real.sqrt P) ≤
        ‖stackFundamentalSolution k layers y x‖ := by
  intro x hx y hy hxy
  have hwidth : y - x ≤ Real.pi / (k * Real.sqrt P) := by
    linarith [hx.1, hy.2]
  have hcomp := stackFundamentalSolution_modulus_comparison (x := x) (h := y - x) hk hP h
    (sub_nonneg.mpr hxy) hwidth
    (fun z hz => hlocal z ⟨by linarith [hx.1, hz.1], by linarith [hy.2, hz.2]⟩)
  simpa only [add_sub_cancel] using hcomp

/-- Lemma 4.3 for the original scattering field, with material caps only on the cell. -/
theorem cell_det_lower_Ioo {k P Q Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hlocalp : ∀ z ∈ Ioo a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q ^ 2 / P ^ 2 * ResourceScalar.f
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      (stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) :=
  cell_det_lower_of_sineComparison_Ioo hk hP hQ hQglobal h hlocalq hab hlength
    (stackFundamentalSolution_cellComparison_Ioo hk hP h hlength hlocalp)

/-- The square-root form needed by the physical determinant Minkowski inequality. -/
theorem cell_sqrt_det_lower_Ioo {k P Q Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hlocalp : ∀ z ∈ Ioo a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q / P * ResourceScalar.g
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      Real.sqrt ((stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) :=
  cell_sqrt_det_lower_of_sineComparison_Ioo hk hP hQ hQglobal h hlocalq hab hlength
    (stackFundamentalSolution_cellComparison_Ioo hk hP h hlength hlocalp)

/-- Exterior layers need only belong to the finite physical class. -/
theorem cell_det_lower_finitePhysical_Ioo {k P Q a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (h : FinitePhysicalStack layers)
    (hlocalp : ∀ z ∈ Ioo a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q ^ 2 / P ^ 2 * ResourceScalar.f
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      (stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  exact cell_det_lower_Ioo hk hP hQ hQglobal hadm hlocalp hlocalq hab hlength

theorem cell_sqrt_det_lower_finitePhysical_Ioo {k P Q a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (h : FinitePhysicalStack layers)
    (hlocalp : ∀ z ∈ Ioo a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Ioo a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q / P * ResourceScalar.g
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      Real.sqrt ((stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  exact cell_sqrt_det_lower_Ioo hk hP hQ hQglobal hadm hlocalp hlocalq hab hlength

#print axioms cell_pairIntegral_lower_of_sineComparison_Ioo
#print axioms cell_det_lower_of_sineComparison_Ioo
#print axioms cell_sqrt_det_lower_of_sineComparison_Ioo
#print axioms stackFundamentalSolution_cellComparison_Ioo
#print axioms cell_det_lower_Ioo
#print axioms cell_sqrt_det_lower_Ioo
#print axioms cell_det_lower_finitePhysical_Ioo
#print axioms cell_sqrt_det_lower_finitePhysical_Ioo
end OQ7

