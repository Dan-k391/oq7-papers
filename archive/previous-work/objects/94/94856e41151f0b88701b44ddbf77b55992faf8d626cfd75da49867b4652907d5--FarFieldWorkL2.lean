import work.FarFieldWork
import work.FarFieldL2
import PrescribedExtinction.PhysicalAbsorptionWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem supportedCurrentFarField_eq (k R : ℝ) (hR : 0 ≤ R)
    (p : CompactPolarization) (hpR : p.radius ≤ R) :
    compactCurrentFarField k (supportedPolarization R hR (p.toSupportedLp R hpR)) = compactCurrentFarField k p :=
  compactCurrentFarField_congr_current k _ p
    ((supportedPolarization_current_ae R hR _).trans p.memLp.coeFn_toLp)

/-- Radiation/work equality for every original compact vector L² polarization,
with the actual Haar surface measure and no smooth-current restriction. -/
theorem physicalOutgoingVolume_farField_work (k : ℝ) (p : CompactPolarization) :
    k * (∫ x : Position, pairing (p.current x) (electricVolumeField k p x)).im =
      ∫ n : UnitSphere, ‖compactCurrentFarField k p n‖ ^ 2 ∂sphereArea := by
  let S := p.radius + 2
  have hS : 0 ≤ S := by dsimp [S]; linarith [p.radius_nonneg]
  have hpS : p.radius ≤ S := by dsimp [S]; linarith
  let x : SupportedVectorL2 S := p.toSupportedLp S hpS
  rw [← compactCurrent_outgoingOperator_inner k S hS p hpS,
    ← supportedCurrentFarField_eq k S hS p hpS]
  apply sub_eq_zero.mp
  let Q : SupportedVectorL2 S → ℝ := fun f =>
    k * (inner ℂ f (compactOutgoingOperator k S hS f)).im - supportedFarFieldPower k S hS f
  change Q x = 0
  have hQ : Continuous Q :=
    (continuous_const.mul (Complex.imCLM.continuous.comp
      (continuous_id.inner (compactOutgoingOperator k S hS).continuous))).sub
        (supportedFarFieldPower_continuous k S hS)
  by_contra hx
  have hU : IsOpen {f : SupportedVectorL2 S | Q f ≠ 0} := isOpen_ne_fun hQ continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨q, hqR, hq, hdist⟩ := compactPolarization_smooth_approximation p (δ / 2) (by positivity)
  have hqS : q.radius ≤ S := by dsimp [S]; rw [hqR]
  let y : SupportedVectorL2 S := q.toSupportedLp S hqS
  have hy : Q y = 0 := by
    have he := smoothPhysicalSource_farField_work k q hq
    rw [← compactCurrent_outgoingOperator_inner k S hS q hqS,
      ← supportedCurrentFarField_eq k S hS q hqS] at he
    exact sub_eq_zero.mpr he
  have hxy : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    change ‖p.memLp.toLp p.current - q.memLp.toLp q.current‖ < δ
    linarith
  exact hball hxy hy

theorem bodyOutgoingOperator_farField_work (k : ℝ) (B : TwoLayerBody) (f : BodyCurrentL2 B) :
    k * (inner ℂ f (bodyOutgoingOperator k B f)).im =
      ∫ n : UnitSphere, ‖compactCurrentFarField k (bodyCurrentPolarization B f) n‖ ^ 2 ∂sphereArea := by
  have h := physicalOutgoingVolume_farField_work k (bodyCurrentPolarization B f)
  rw [← compactCurrent_outgoingOperator_inner k (bodySupportRadius B) (bodySupportRadius_nonneg B)
    (bodyCurrentPolarization B f) (by rfl)] at h
  have he : (bodyCurrentPolarization B f).toSupportedLp (bodySupportRadius B) (by rfl) = bodyCurrentInclusion B f := by
    apply Subtype.ext
    exact Lp.ext ((bodyCurrentPolarization B f).memLp.coeFn_toLp.trans (bodyCurrentPolarization_current_ae B f))
  rw [he, ← bodyOutgoingOperator_inner] at h
  exact h

/-- Exact physical energy balance with the full vector Haar radiation integral.
The original theta/phi formula still needs its surface-coordinate conversion. -/
theorem physicalVolume_Haar_energy_balance (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    extinction k B σ (volumeTotalElectric k σ (bodyCurrentPolarization B f)) =
      absorption k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) +
        ∫ n : UnitSphere, ‖currentFarField k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) n‖ ^ 2 ∂sphereArea := by
  rw [physicalVolume_work_balance k B σ f hp, bodyOutgoingOperator_farField_work]
  simp_rw [volumePhysicalFarField_eq k B σ f hp]

end OQ7Prescribed
