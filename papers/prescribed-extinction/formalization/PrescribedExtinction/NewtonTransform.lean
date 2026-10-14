import PrescribedExtinction.NewtonFourier
import PrescribedExtinction.NewtonHeatPairing
import PrescribedExtinction.NewtonHeatFourier
import PrescribedExtinction.NewtonFrequencyHeat
import PrescribedExtinction.NewtonSymbol

/-! Fourier correspondence for the actual Newton kernel as an equality on
all Schwartz tests. Both heat/time interchanges are justified by absolute
integrability. No division of a distribution by the frequency norm is used. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set FourierTransform

theorem newton_heat_fourier_pairing (φ : SchwartzMap Position ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ x : Position, (𝓕 φ) x * (newtonHeatKernel t x : ℂ)) =
      ∫ ξ : Position, φ ξ * newtonFrequencyHeatKernel t ξ := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ Position) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner φ.integrable
    (newtonHeatKernel_space_integrable_complex t ht)
  have h' : (∫ x : Position, (𝓕 φ) x * (newtonHeatKernel t x : ℂ)) =
      ∫ ξ : Position, φ ξ * (𝓕 (fun x : Position => (newtonHeatKernel t x : ℂ))) ξ := by
    simpa [SchwartzMap.fourier_coe] using! h
  rw [h']
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    change φ ξ * (𝓕 (fun x : Position => (newtonHeatKernel t x : ℂ))) ξ =
      φ ξ * newtonFrequencyHeatKernel t ξ
    rw [newtonHeatKernel_fourier t ht ξ]
    congr 1
    unfold newtonFrequencyHeatKernel
    congr 1
    push_cast
    ring

theorem newtonTempered_fourier_eq :
    𝓕 newtonTempered = newtonFrequencyTempered := by
  ext φ
  rw [newtonTempered_fourier_apply, newton_heat_schwartz_pairing,
    newtonFrequencyTempered_heat_pairing]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => newton_heat_fourier_pairing φ t ht

theorem newtonTempered_fourier_integral (φ : SchwartzMap Position ℂ) :
    𝓕 newtonTempered φ = ∫ ξ : Position, φ ξ * newtonFrequencyKernel ξ := by
  rw [newtonTempered_fourier_eq, newtonFrequencyTempered_apply]

/-- The complete physical Newton Hessian has exactly the static multiplier.
This equality includes the contact term through `newtonTemperedHessian`; it
holds on every Schwartz test, rather than merely away from zero frequency. -/
theorem newtonTemperedHessian_fourier_integral (φ : SchwartzMap Position ℂ) (i j : Fin 3) :
    𝓕 (newtonTemperedHessian i j) φ =
      ∫ ξ : Position, φ ξ * ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [newtonTemperedHessian_fourier, newtonTempered_fourier_eq]
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    newtonFrequencyTempered_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    have hg : (fun ξ : Position => (ξ i : ℂ) * (ξ j : ℂ)).HasTemperateGrowth := by
      have he : (fun ξ : Position => (ξ i : ℂ) * (ξ j : ℂ)) =
          (fun ξ : Position => (inner ℝ ξ (basisR i) : ℂ) * (inner ℝ ξ (basisR j) : ℂ)) := by
        funext ξ
        simp only [real_inner_basis]
      rw [he]
      fun_prop
    change (-(2 * Real.pi) ^ 2 : ℂ) *
        ((SchwartzMap.smulLeftCLM ℂ (fun ξ : Position => (ξ i : ℂ) * (ξ j : ℂ)) φ) ξ *
          newtonFrequencyKernel ξ) = φ ξ * ((-(ξ i * ξ j) / ‖ξ‖ ^ 2 : ℝ) : ℂ)
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [newtonFrequencyKernel, smul_eq_mul]
    by_cases hξ : ξ = 0
    · subst ξ
      simp
    · have hn : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
      have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp [hn, hp]
      ring

theorem newtonTemperedHessian_fourier_eq (i j : Fin 3) :
    𝓕 (newtonTemperedHessian i j) = newtonHessianFrequencyTempered i j := by
  ext φ
  rw [newtonTemperedHessian_fourier_integral, newtonHessianFrequencyTempered_apply]
  rfl

end OQ7Prescribed
