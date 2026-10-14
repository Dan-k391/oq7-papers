import PrescribedExtinction.RankOneScattering

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem volumeExtinction_current_work (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p) :
    extinction k B σ (volumeTotalElectric k σ p) =
      k * (∫ x in B.domain, pairing (incidentElectric k σ x) (p.current x)).im := by
  unfold extinction
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hp] with x hx
  rw [hx]

theorem bodyCurrent_incident_work (k : ℝ) (B : TwoLayerBody) (σ : Direction) (f : BodyCurrentL2 B) :
    (∫ x in B.domain, pairing (incidentElectric k σ x) ((bodyCurrentPolarization B f).current x)) =
      inner ℂ (bodyIncidentCurrent k B σ) f := by
  change _ = inner ℂ (bodyIncidentCurrent k B σ : VectorL2) (f : VectorL2)
  rw [L2.inner_def, ← integral_indicator (bodyDomain_isOpen B).measurableSet]
  apply integral_congr_ae
  filter_upwards [bodyIncidentCurrent_coe k B σ] with x hx
  rw [hx]
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd]
    change pairing (incidentElectric k σ x) (B.domain.indicator (fun y => (f : VectorL2) y) x) = _
    rw [indicator_of_mem hxd, pairing_eq_inner]
  · rw [indicator_of_notMem hxd, indicator_of_notMem hxd, inner_zero_left]

theorem activeProjection_inner (B : TwoLayerBody) (u v : Position)
    (f : BodyCurrentL2 B) (q : ScalarBodyCurrentL2 B) :
    inner ℂ f (activeInjection B u v q) = inner ℂ (activeProjection B u v f) q := by
  rw [← inner_conj_symm (𝕜 := ℂ) f, activeInjection_inner, inner_conj_symm]

theorem activePhysicalExtinction_work (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    extinction k (rankOneBody B u v α β) σ
      (volumeTotalElectric k σ (bodyCurrentPolarization B
        (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ)))) =
      k * (inner ℂ (activeProjection B u v (bodyIncidentCurrent k B σ))
        (activePhysicalSolution k hk B σ u v α β hα hβ)).im := by
  rw [volumeExtinction_current_work k _ _ _
    (activePhysicalSolution_physicalVolumeEquation k hk B σ u v α β hα hβ)]
  change k * (∫ x in B.domain, pairing (incidentElectric k σ x)
    ((bodyCurrentPolarization B (activeInjection B u v
      (activePhysicalSolution k hk B σ u v α β hα hβ))).current x)).im = _
  rw [bodyCurrent_incident_work, activeProjection_inner]

end OQ7Prescribed
