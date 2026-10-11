import PrescribedExtinction.NewtonHeat
import PrescribedExtinction.NewtonTempered
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine absolute integrability of the Newton heat representation paired
with a Schwartz function, followed by justified Fubini. The exceptional spatial
origin is a Lebesgue null set; no time integrability there is asserted. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

theorem newtonHeatKernel_nonneg (t : ℝ) (ht : 0 < t) (x : Position) :
    0 ≤ newtonHeatKernel t x := by
  unfold newtonHeatKernel
  positivity

theorem newtonHeatKernel_joint_measurable :
    Measurable (fun p : Position × ℝ => newtonHeatKernel p.2 p.1) := by
  unfold newtonHeatKernel
  fun_prop

theorem newton_heat_pairing_time_integrable (φ : SchwartzMap Position ℂ)
    (x : Position) (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => φ x * (newtonHeatKernel t x : ℂ)) (Ioi 0) := by
  exact (newtonHeatKernel_integrable x hx).ofReal.const_mul (φ x)

theorem newton_heat_pairing_time_norm (φ : SchwartzMap Position ℂ)
    (x : Position) (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0, ‖φ x * (newtonHeatKernel t x : ℂ)‖) =
      ‖φ x * outgoingGreen 0 x‖ := by
  calc
    _ = ∫ t : ℝ in Ioi 0, ‖φ x‖ * newtonHeatKernel t x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change ‖φ x * (newtonHeatKernel t x : ℂ)‖ = ‖φ x‖ * newtonHeatKernel t x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (newtonHeatKernel_nonneg t ht x)]
    _ = ‖φ x‖ * newtonReal x := by
      rw [integral_const_mul, newton_heat_representation x hx]
    _ = ‖φ x * outgoingGreen 0 x‖ := by
      rw [← newtonReal_eq_green, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg]
      unfold newtonReal
      positivity

theorem newton_heat_pairing_joint_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun p : Position × ℝ => φ p.1 * (newtonHeatKernel p.2 p.1 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : Position × ℝ => φ p.1 * (newtonHeatKernel p.2 p.1 : ℂ)) := by
    exact (φ.continuous.measurable.comp measurable_fst).mul
      (Complex.continuous_ofReal.measurable.comp newtonHeatKernel_joint_measurable)
  have hz : ∀ᵐ x : Position ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hz] with x hx
    exact newton_heat_pairing_time_integrable φ x hx
  · apply (newton_schwartz_integrable φ).norm.congr
    filter_upwards [hz] with x hx
    exact (newton_heat_pairing_time_norm φ x hx).symm

theorem newton_heat_pairing_time_integral (φ : SchwartzMap Position ℂ)
    (x : Position) (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0, φ x * (newtonHeatKernel t x : ℂ)) =
      φ x * outgoingGreen 0 x := by
  rw [integral_const_mul, integral_complex_ofReal, newton_heat_representation x hx,
    newtonReal_eq_green]

theorem newton_heat_pairing_time_space_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun p : ℝ × Position => φ p.2 * (newtonHeatKernel p.1 p.2 : ℂ))
      ((volume.restrict (Ioi 0)).prod volume) := by
  exact (newton_heat_pairing_joint_integrable φ).swap

theorem newton_heat_schwartz_pairing (φ : SchwartzMap Position ℂ) :
    (∫ x : Position, φ x * outgoingGreen 0 x) =
      ∫ t : ℝ in Ioi 0, ∫ x : Position, φ x * (newtonHeatKernel t x : ℂ) := by
  calc
    _ = ∫ x : Position, ∫ t : ℝ in Ioi 0, φ x * (newtonHeatKernel t x : ℂ) := by
      apply integral_congr_ae
      have hz : ∀ᵐ x : Position ∂volume, x ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [hz] with x hx
      exact (newton_heat_pairing_time_integral φ x hx).symm
    _ = _ := integral_integral_swap (newton_heat_pairing_joint_integrable φ)

theorem newtonTempered_heat_pairing (φ : SchwartzMap Position ℂ) :
    newtonTempered φ =
      ∫ t : ℝ in Ioi 0, ∫ x : Position, φ x * (newtonHeatKernel t x : ℂ) := by
  rw [newtonTempered_apply, newton_heat_schwartz_pairing]

end OQ7Prescribed
