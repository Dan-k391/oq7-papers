import PrescribedExtinction.NewtonFrequency
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual frequency-side heat integral, with genuine absolute
integrability and Fubini on Schwartz pairings. The spatial frequency origin
is excluded from the time-integrability statements and removed only as a
Lebesgue null set in the joint-integral argument. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

def newtonFrequencyHeatKernel (t : ℝ) (ξ : Position) : ℂ :=
  Complex.exp ((-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) : ℝ) : ℂ)

theorem newtonFrequencyHeatKernel_eq_real (t : ℝ) (ξ : Position) :
    newtonFrequencyHeatKernel t ξ = (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) := by
  rw [newtonFrequencyHeatKernel, Complex.ofReal_exp]

theorem newton_frequency_heat_scalar_integrable (ξ : Position) (hξ : ξ ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2))) (Ioi 0) := by
  have hn := norm_pos_iff.mpr hξ
  have ha : -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) < 0 := neg_lt_zero.mpr (by positivity)
  have h := integrableOn_exp_mul_Ioi
    (a := -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) ha 0
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  change Real.exp ((-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) * t) =
    Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2))
  congr 1
  ring

theorem newton_frequency_heat_scalar_integral (ξ : Position) (hξ : ξ ≠ 0) :
    (∫ t : ℝ in Ioi 0, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2))) =
      (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ := by
  have hn := norm_pos_iff.mpr hξ
  have ha : -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) < 0 := neg_lt_zero.mpr (by positivity)
  calc
    _ = ∫ t : ℝ in Ioi 0, Real.exp ((-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) =
        Real.exp ((-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) * t)
      congr 1
      ring
    _ = _ := by
      rw [integral_exp_mul_Ioi ha 0]
      simp

theorem newtonFrequencyHeatKernel_joint_measurable :
    Measurable (fun p : Position × ℝ => newtonFrequencyHeatKernel p.2 p.1) := by
  unfold newtonFrequencyHeatKernel
  fun_prop

theorem newton_frequency_heat_time_integrable (φ : SchwartzMap Position ℂ)
    (ξ : Position) (hξ : ξ ≠ 0) :
    IntegrableOn (fun t : ℝ => φ ξ * newtonFrequencyHeatKernel t ξ) (Ioi 0) := by
  have h := (newton_frequency_heat_scalar_integrable ξ hξ).ofReal.const_mul (φ ξ)
  apply h.congr
  exact ae_of_all _ fun t => congrArg (fun z : ℂ => φ ξ * z)
    (newtonFrequencyHeatKernel_eq_real t ξ).symm

theorem newton_frequency_heat_time_norm (φ : SchwartzMap Position ℂ)
    (ξ : Position) (hξ : ξ ≠ 0) :
    (∫ t : ℝ in Ioi 0, ‖φ ξ * newtonFrequencyHeatKernel t ξ‖) =
      ‖φ ξ * newtonFrequencyKernel ξ‖ := by
  calc
    _ = ∫ t : ℝ in Ioi 0, ‖φ ξ‖ * Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change ‖φ ξ * newtonFrequencyHeatKernel t ξ‖ =
        ‖φ ξ‖ * Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2))
      rw [norm_mul, newtonFrequencyHeatKernel_eq_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    _ = ‖φ ξ‖ * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ := by
      rw [integral_const_mul, newton_frequency_heat_scalar_integral ξ hξ]
    _ = _ := by rw [norm_mul, newtonFrequencyKernel_norm]

theorem newton_frequency_heat_joint_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun p : Position × ℝ => φ p.1 * newtonFrequencyHeatKernel p.2 p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : Position × ℝ => φ p.1 * newtonFrequencyHeatKernel p.2 p.1) :=
    (φ.continuous.measurable.comp measurable_fst).mul newtonFrequencyHeatKernel_joint_measurable
  have hz : ∀ᵐ ξ : Position ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simp
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hz] with ξ hξ
    exact newton_frequency_heat_time_integrable φ ξ hξ
  · apply (newtonFrequency_schwartz_integrable φ).norm.congr
    filter_upwards [hz] with ξ hξ
    exact (newton_frequency_heat_time_norm φ ξ hξ).symm

theorem newton_frequency_heat_time_integral (φ : SchwartzMap Position ℂ)
    (ξ : Position) (hξ : ξ ≠ 0) :
    (∫ t : ℝ in Ioi 0, φ ξ * newtonFrequencyHeatKernel t ξ) =
      φ ξ * newtonFrequencyKernel ξ := by
  simp only [newtonFrequencyHeatKernel_eq_real]
  rw [integral_const_mul, integral_complex_ofReal,
    newton_frequency_heat_scalar_integral ξ hξ]
  rfl

theorem newtonFrequencyTempered_heat_pairing (φ : SchwartzMap Position ℂ) :
    newtonFrequencyTempered φ =
      ∫ t : ℝ in Ioi 0, ∫ ξ : Position, φ ξ * newtonFrequencyHeatKernel t ξ := by
  rw [newtonFrequencyTempered_apply]
  calc
    _ = ∫ ξ : Position, ∫ t : ℝ in Ioi 0, φ ξ * newtonFrequencyHeatKernel t ξ := by
      apply integral_congr_ae
      have hz : ∀ᵐ ξ : Position ∂volume, ξ ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [hz] with ξ hξ
      exact (newton_frequency_heat_time_integral φ ξ hξ).symm
    _ = _ := integral_integral_swap (newton_frequency_heat_joint_integrable φ)

end OQ7Prescribed
