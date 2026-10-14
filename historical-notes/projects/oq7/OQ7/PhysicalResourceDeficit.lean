import OQ7.Target
import OQ7.Passivity
import OQ7.PhysicalPassivity

noncomputable section
namespace OQ7

/-- The scalar envelope deficit for the actual finite multilayer at its exact targets. -/
theorem exactTargetClass_normalizedDet_deficit {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    ScalarEnvelope.alpha p.T p.a *
      normalizedAbsorptionDet (stackReflectionLeft p.k layers)
        (stackReflectionRight p.k layers) (stackTransmission p.k layers) ≤
      ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k layers := by
  have hp := stack_scattering_passive p.k_pos hm.1
  have ht := hm.2.2.2.1
  have ha := hm.2.2.2.2
  have hactive : ScalarEnvelope.ActiveTarget (stackTransmissionPower p.k layers)
      (stackMeanAbsorptance p.k layers) := by
    rw [ht, ha]
    exact p.active
  have hb := active_matrix_deficit hp hactive
  change ScalarEnvelope.alpha (stackTransmissionPower p.k layers)
      (stackMeanAbsorptance p.k layers) *
      normalizedAbsorptionDet (stackReflectionLeft p.k layers)
        (stackReflectionRight p.k layers) (stackTransmission p.k layers) ≤
      ScalarEnvelope.D0 (stackTransmissionPower p.k layers)
        (stackMeanAbsorptance p.k layers) - stackAsymmetry p.k layers at hb
  simpa only [ht, ha] using hb

#print axioms exactTargetClass_normalizedDet_deficit

/-- The supremum defining the exact-target optimum has a proved finite upper bound. -/
theorem exactTargetClass_asymmetry_bddAbove (p : PhysicalParameters) (L : ℝ) :
    BddAbove (stackAsymmetry p.k '' exactTargetClass p L) := by
  refine ⟨ScalarEnvelope.D0 p.T p.a, ?_⟩
  rintro d ⟨layers, hm, rfl⟩
  have hc : 0 ≤ normalizedAbsorptionDet (stackReflectionLeft p.k layers)
      (stackReflectionRight p.k layers) (stackTransmission p.k layers) := by
    exact div_nonneg (passive_det_nonneg (stack_scattering_passive p.k_pos hm.1))
      (Complex.normSq_nonneg _)
  have halpha : 0 < ScalarEnvelope.alpha p.T p.a :=
    (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hb := exactTargetClass_normalizedDet_deficit hm
  have hprod := mul_nonneg halpha.le hc
  linarith

/-- A physical determinant floor bounds the optimum without assuming a maximizing stack. -/
theorem exactTargetClass_optimal_deficit_of_normalizedDet_floor
    {p : PhysicalParameters} {L β : ℝ} (hne : (exactTargetClass p L).Nonempty)
    (hfloor : ∀ layers ∈ exactTargetClass p L,
      β ≤ normalizedAbsorptionDet (stackReflectionLeft p.k layers)
        (stackReflectionRight p.k layers) (stackTransmission p.k layers)) :
    ScalarEnvelope.alpha p.T p.a * β ≤
      ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L := by
  have halpha : 0 < ScalarEnvelope.alpha p.T p.a :=
    (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hbound : ∀ d ∈ stackAsymmetry p.k '' exactTargetClass p L,
      d ≤ ScalarEnvelope.D0 p.T p.a - ScalarEnvelope.alpha p.T p.a * β := by
    rintro d ⟨layers, hm, rfl⟩
    have hmul := mul_le_mul_of_nonneg_left (hfloor layers hm) halpha.le
    have hb := hmul.trans (exactTargetClass_normalizedDet_deficit hm)
    linarith
  have hsup := csSup_le (hne.image (stackAsymmetry p.k)) hbound
  change optimalAsymmetry p L ≤
    ScalarEnvelope.D0 p.T p.a - ScalarEnvelope.alpha p.T p.a * β at hsup
  linarith

#print axioms exactTargetClass_asymmetry_bddAbove
#print axioms exactTargetClass_optimal_deficit_of_normalizedDet_floor
end OQ7
