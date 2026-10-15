import PrescribedExtinction.NewtonCurrentCorrelation
import Mathlib.Analysis.Fourier.Convolution

/-! Fourier transform of the genuine compact-current/test correlation.
Both convolution factors are integrable; the Newton kernel is not subjected
to an invalid globally-L1 convolution theorem. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory FourierTransform
open scoped Convolution

theorem current_component_fourier (p : CompactPolarization) (j : Fin 3) (ξ : Position) :
    (𝓕 (fun y : Position => p.current y j)) ξ = (𝓕 p.current) ξ j := by
  have hi := (Real.fourierIntegral_convergent_iff ξ).mpr
    (compactPolarization_current_integrable p)
  have h := (vectorCoordinate j).integral_comp_comm hi
  simpa only [Real.fourier_eq, vectorCoordinate, PiLp.proj_apply,
    Circle.smul_def, PiLp.smul_apply] using! h

theorem reflectedCurrentComponent_fourier_neg
    (p : CompactPolarization) (j : Fin 3) (ξ : Position) :
    (𝓕 (reflectedCurrentComponent p j)) (-ξ) = (𝓕 p.current) ξ j := by
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ)
    (fun y : Position => p.current y j) (-ξ)
  change (𝓕 (fun y : Position => p.current (-y) j)) (-ξ) =
    (𝓕 (fun y : Position => p.current y j)) (-(-ξ)) at h
  simpa only [neg_neg, reflectedCurrentComponent, current_component_fourier] using! h

theorem newtonCurrentCorrelation_complex_convolution
    (p : CompactPolarization) (φ : ScalarTest) (j : Fin 3) :
    newtonCurrentCorrelation p φ j =
      reflectedCurrentComponent p j ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (scalarTestSchwartz φ : Position → ℂ) := by
  rw [newtonCurrentCorrelation_eq_convolution]
  rfl

theorem newtonCurrentCorrelationSchwartz_fourierInv
    (p : CompactPolarization) (φ : ScalarTest) (j : Fin 3) (ξ : Position) :
    (𝓕⁻ (newtonCurrentCorrelationSchwartz p φ j)) ξ =
      (𝓕⁻ (scalarTestSchwartz φ)) ξ * (𝓕 p.current) ξ j := by
  rw [SchwartzMap.fourierInv_coe]
  change (𝓕⁻ (newtonCurrentCorrelation p φ j)) ξ = _
  rw [Real.fourierInv_eq_fourier_neg, newtonCurrentCorrelation_complex_convolution,
    Real.fourier_mul_convolution_eq (reflectedCurrentComponent_integrable p j)
      (scalarTestSchwartz φ).integrable, reflectedCurrentComponent_fourier_neg]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  exact mul_comm _ _

end OQ7Prescribed
