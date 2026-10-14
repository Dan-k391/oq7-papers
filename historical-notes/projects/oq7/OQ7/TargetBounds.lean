import OQ7.Target
import OQ7.PhysicalPassivity
import OQ7.Passivity

namespace OQ7

noncomputable section

def stackNormalizedAbsorptionDet (k : ℝ) (layers : List HomogeneousLayer) : ℝ :=
  normalizedAbsorptionDet (stackReflectionLeft k layers) (stackReflectionRight k layers)
    (stackTransmission k layers)

/-- The active deficit inequality for actual finite dielectric stacks with exact targets. -/
theorem exactTargetClass_deficit {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    ScalarEnvelope.alpha p.T p.a * stackNormalizedAbsorptionDet p.k layers ≤
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
      (stackMeanAbsorptance p.k layers) * stackNormalizedAbsorptionDet p.k layers ≤
    ScalarEnvelope.D0 (stackTransmissionPower p.k layers)
      (stackMeanAbsorptance p.k layers) - stackAsymmetry p.k layers at hb
  simpa only [ht, ha] using hb

theorem exactTargetClass_normalizedDet_nonneg {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    0 ≤ stackNormalizedAbsorptionDet p.k layers := by
  have hp := stack_scattering_passive p.k_pos hm.1
  apply div_nonneg (passive_det_nonneg hp)
  exact Complex.normSq_nonneg _

theorem exactTargetClass_asymmetry_le {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    stackAsymmetry p.k layers ≤ ScalarEnvelope.D0 p.T p.a := by
  have ha := (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hc := exactTargetClass_normalizedDet_nonneg hm
  have hb := exactTargetClass_deficit hm
  have hprod := mul_nonneg ha.le hc
  linarith

/-- The exact physical asymmetry image is bounded, including when the class is empty. -/
theorem exactTargetClass_bddAbove (p : PhysicalParameters) (L : ℝ) :
    BddAbove (stackAsymmetry p.k '' exactTargetClass p L) := by
  refine ⟨ScalarEnvelope.D0 p.T p.a, ?_⟩
  rintro d ⟨layers, hm, rfl⟩
  exact exactTargetClass_asymmetry_le hm

theorem optimalAsymmetry_le {p : PhysicalParameters} {L : ℝ}
    (hne : (exactTargetClass p L).Nonempty) :
    optimalAsymmetry p L ≤ ScalarEnvelope.D0 p.T p.a := by
  apply csSup_le (hne.image (stackAsymmetry p.k))
  rintro d ⟨layers, hm, rfl⟩
  exact exactTargetClass_asymmetry_le hm

theorem stackAsymmetry_le_optimal {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    stackAsymmetry p.k layers ≤ optimalAsymmetry p L := by
  exact le_csSup (exactTargetClass_bddAbove p L) (Set.mem_image_of_mem _ hm)

/-- A constructed exact-target physical stack gives the upper side of the deficit squeeze. -/
theorem optimal_deficit_le_stack_deficit {p : PhysicalParameters} {L : ℝ}
    {layers : List HomogeneousLayer} (hm : layers ∈ exactTargetClass p L) :
    ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L ≤
      ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k layers := by
  exact sub_le_sub_left (stackAsymmetry_le_optimal hm) _

/-- The lower side of the physical supremum squeeze from any proved uniform determinant floor.
Theorem 4.5 supplies this floor in the physical lower-asymptotic modules. -/
theorem uniform_floor_optimal_deficit {p : PhysicalParameters} {L beta : ℝ}
    (hne : (exactTargetClass p L).Nonempty)
    (hfloor : ∀ layers ∈ exactTargetClass p L,
      beta ≤ stackNormalizedAbsorptionDet p.k layers) :
    ScalarEnvelope.alpha p.T p.a * beta ≤
      ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L := by
  have ha := (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hsup : optimalAsymmetry p L ≤
      ScalarEnvelope.D0 p.T p.a - ScalarEnvelope.alpha p.T p.a * beta := by
    apply csSup_le (hne.image (stackAsymmetry p.k))
    rintro d ⟨layers, hm, rfl⟩
    have hd := exactTargetClass_deficit hm
    have hf := mul_le_mul_of_nonneg_left (hfloor layers hm) ha.le
    linarith
  linarith

#print axioms exactTargetClass_deficit
#print axioms exactTargetClass_normalizedDet_nonneg
#print axioms exactTargetClass_asymmetry_le
#print axioms exactTargetClass_bddAbove
#print axioms optimalAsymmetry_le
#print axioms stackAsymmetry_le_optimal
#print axioms optimal_deficit_le_stack_deficit
#print axioms uniform_floor_optimal_deficit

end
end OQ7
