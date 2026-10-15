import PrescribedExtinction.SmoothOutgoingFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

/-- Compact smooth currents separate actual locally integrable vector fields. -/
theorem field_zero_ae_of_compact_smooth_bilinear_tests (F : Field)
    (hF : LocallyIntegrable F volume)
    (hT : ∀ q : CompactPolarization, ContDiff ℝ (⊤ : ℕ∞) q.current →
      (∫ x : Position, bilinear (q.current x) (F x)) = 0) : F =ᵐ[volume] 0 := by
  apply fieldComponentDistribution_injective F 0 hF locallyIntegrable_zero
  funext i
  ext φ
  obtain ⟨R, hR, hb⟩ := scalarTest_support_radius φ
  let G : Field := fun x => φ x • basisC i
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := φ.contDiff.smul contDiff_const
  have hsG : HasCompactSupport G := φ.hasCompactSupport.smul_right (f' := fun _ => basisC i)
  let q : CompactPolarization := {
    current := G
    radius := R
    radius_nonneg := hR.le
    memLp := hG.continuous.memLp_of_hasCompactSupport hsG
    vanish := fun x hx => by
      have hz : φ x = 0 := by by_contra hn; exact (hb x hn).not_gt hx
      simp [G, hz] }
  have hz := hT q hG
  rw [fieldComponentDistribution_apply F hF,
    fieldComponentDistribution_apply 0 locallyIntegrable_zero]
  have hp (x : Position) : bilinear (q.current x) (F x) = (φ x : ℂ) * F x i := by
    simp [q, G, bilinear, basisC, Finset.sum_ite_eq', Complex.real_smul]
  simp_rw [hp] at hz
  simpa using hz

end OQ7Prescribed
