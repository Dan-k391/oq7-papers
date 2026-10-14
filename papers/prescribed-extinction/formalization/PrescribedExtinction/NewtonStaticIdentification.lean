import PrescribedExtinction.NewtonCurrentFourier
import PrescribedExtinction.FourierL1L2
import PrescribedExtinction.StaticOperatorDistribution

/-! Identification of the actual distributional Newton volume operator on
every compactly supported vector L² current with the existing static Fourier
operator. Current/test Fubini and the genuine smooth correlation justify use
of the physical Newton Hessian's Fourier identity. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory FourierTransform

theorem potentialComponentDistribution_newtonTempered
    (p : CompactPolarization) (φ : ScalarTest) (j : Fin 3) :
    potentialComponentDistribution 0 p j φ =
      newtonTempered (newtonCurrentCorrelationSchwartz p φ j) := by
  rw [potentialComponentDistribution_newton_pairing, newtonTempered_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change outgoingGreen 0 z * newtonCurrentCorrelation p φ j z =
      newtonCurrentCorrelationSchwartz p φ j z * outgoingGreen 0 z
    rw [newtonCurrentCorrelationSchwartz_apply, mul_comm]

theorem outgoingVolumeDistribution_zero_hessian_pairing
    (p : CompactPolarization) (i : Fin 3) (φ : ScalarTest) :
    outgoingVolumeDistribution 0 p i φ =
      ∑ j : Fin 3, newtonTemperedHessian i j
        (newtonCurrentCorrelationSchwartz p φ j) := by
  have he : outgoingVolumeDistribution 0 p i φ =
      ∑ j : Fin 3, potentialComponentDistribution 0 p j
        (testPartial j (testPartial i φ)) := by
    simp [outgoingVolumeDistribution, distributionPartial, testPartial,
      Distribution.lineDerivCLM_apply]
  rw [he]
  congr 1
  ext j
  rw [newtonTemperedHessian_apply, newtonCurrentCorrelationSchwartz_secondPartial,
    potentialComponentDistribution_newtonTempered]

theorem newtonHessian_current_fourier_pairing
    (p : CompactPolarization) (i j : Fin 3) (φ : ScalarTest) :
    newtonTemperedHessian i j (newtonCurrentCorrelationSchwartz p φ j) =
      ∫ ξ : Position, (𝓕⁻ (scalarTestSchwartz φ)) ξ *
        newtonHessianFrequency i j ξ * (𝓕 p.current) ξ j := by
  have h := newtonTemperedHessian_fourier_integral
    (𝓕⁻ (newtonCurrentCorrelationSchwartz p φ j)) i j
  simp only [TemperedDistribution.fourier_apply, fourier_fourierInv_eq] at h
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    change (𝓕⁻ (newtonCurrentCorrelationSchwartz p φ j)) ξ *
      ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ) = _
    rw [newtonCurrentCorrelationSchwartz_fourierInv]
    unfold newtonHessianFrequency
    ring

/-- The exact physical static operator identity, on the entire existing
compactly supported vector L² input class and in the original distribution
framework. No scattering or Fourier identity is assumed of the current. -/
theorem outgoingVolumeDistribution_zero_eq_staticFourier
    (p : CompactPolarization) (i : Fin 3) :
    outgoingVolumeDistribution 0 p i =
      vectorL2ComponentDistribution (staticFourierOperator (p.memLp.toLp p.current)) i := by
  ext φ
  rw [outgoingVolumeDistribution_zero_hessian_pairing,
    staticFourierOperator_component_distribution_apply]
  congr 1
  ext j
  rw [newtonHessian_current_fourier_pairing]
  apply integral_congr_ae
  have hf := fourierIntegral_L1L2_ae
    (memLp_one_iff_integrable.mpr (compactPolarization_current_integrable p)) p.memLp
  filter_upwards [hf] with ξ hξ
  change (𝓕⁻ (scalarTestSchwartz φ)) ξ * newtonHessianFrequency i j ξ *
      (𝓕 p.current) ξ j =
    (𝓕⁻ (scalarTestSchwartz φ)) ξ * newtonHessianFrequency i j ξ *
      (𝓕 (p.memLp.toLp p.current) : VectorL2) ξ j
  rw [hξ]
  rfl

theorem outgoingVolumeDistribution_zero_bounded_L2_realization
    (p : CompactPolarization) :
    ∃ u : VectorL2, (∀ i : Fin 3, outgoingVolumeDistribution 0 p i =
      vectorL2ComponentDistribution u i) ∧ ‖u‖ ≤ ‖p.memLp.toLp p.current‖ := by
  refine ⟨staticFourierOperator (p.memLp.toLp p.current), ?_,
    staticFourierOperator_apply_norm_le _⟩
  exact outgoingVolumeDistribution_zero_eq_staticFourier p

end OQ7Prescribed
