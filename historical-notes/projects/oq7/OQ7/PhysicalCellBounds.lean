import OQ7.ResourceCells
import OQ7.PhysicalModulus
import OQ7.PhysicalClass

noncomputable section
namespace OQ7
open Set MeasureTheory

/-- Actual Lemma 4.1 supplies every pairwise comparison inside a selected short cell. -/
theorem stackFundamentalSolution_cellComparison {k P Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) {layers : List HomogeneousLayer}
    (h : StackAdmissible Pglobal Qglobal layers)
    (hlength : b - a ≤ Real.pi / (k * Real.sqrt P))
    (hlocal : ∀ z ∈ Icc a b, stackRealProfile layers z ≤ P) :
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
theorem cell_det_lower {k P Q Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hlocalp : ∀ z ∈ Icc a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Icc a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q ^ 2 / P ^ 2 * ResourceScalar.f
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      (stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) :=
  cell_det_lower_of_sineComparison hk hP hQ hQglobal h hlocalq hab hlength
    (stackFundamentalSolution_cellComparison hk hP h hlength hlocalp)

/-- The square-root form needed by the physical determinant Minkowski inequality. -/
theorem cell_sqrt_det_lower {k P Q Pglobal Qglobal a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (hQglobal : 0 ≤ Qglobal) (h : StackAdmissible Pglobal Qglobal layers)
    (hlocalp : ∀ z ∈ Icc a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Icc a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q / P * ResourceScalar.g
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      Real.sqrt ((stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) :=
  cell_sqrt_det_lower_of_sineComparison hk hP hQ hQglobal h hlocalq hab hlength
    (stackFundamentalSolution_cellComparison hk hP h hlength hlocalp)

/-- Exterior layers need only belong to the finite physical class. -/
theorem cell_det_lower_finitePhysical {k P Q a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (h : FinitePhysicalStack layers)
    (hlocalp : ∀ z ∈ Icc a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Icc a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q ^ 2 / P ^ 2 * ResourceScalar.f
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      (stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  exact cell_det_lower hk hP hQ hQglobal hadm hlocalp hlocalq hab hlength

theorem cell_sqrt_det_lower_finitePhysical {k P Q a b : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (h : FinitePhysicalStack layers)
    (hlocalp : ∀ z ∈ Icc a b, stackRealProfile layers z ≤ P)
    (hlocalq : ∀ z ∈ Icc a b, 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hab : a ≤ b) (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q / P * ResourceScalar.g
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      Real.sqrt ((stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  exact cell_sqrt_det_lower hk hP hQ hQglobal hadm hlocalp hlocalq hab hlength

/-- The original globally capped material class is an immediate specialization. -/
theorem cell_det_lower_admissible {k P Q a b : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (hab : a ≤ b)
    (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q ^ 2 / P ^ 2 * ResourceScalar.f
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      (stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) :=
  cell_det_lower hk (by linarith) hQ hQ.le h
    (fun z _ => (stackRealProfile_bounds hP h z).2)
    (fun z _ => stackLossProfile_bounds hQ.le h z) hab hlength

theorem cell_sqrt_det_lower_admissible {k P Q a b : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : 0 < Q) {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (hab : a ≤ b)
    (hlength : b - a ≤ Real.pi / (k * Real.sqrt P)) :
    Q / P * ResourceScalar.g
      (k * Real.sqrt P * (∫ z in a..b, stackLossProfile layers z) / Q) ≤
      Real.sqrt ((stackDepositedAbsorption k layers a b).det.re /
        Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers)))) :=
  cell_sqrt_det_lower hk (by linarith) hQ hQ.le h
    (fun z _ => (stackRealProfile_bounds hP h z).2)
    (fun z _ => stackLossProfile_bounds hQ.le h z) hab hlength

#print axioms stackFundamentalSolution_cellComparison
#print axioms cell_det_lower
#print axioms cell_sqrt_det_lower
#print axioms cell_det_lower_finitePhysical
#print axioms cell_sqrt_det_lower_finitePhysical
#print axioms cell_det_lower_admissible
#print axioms cell_sqrt_det_lower_admissible
end OQ7
