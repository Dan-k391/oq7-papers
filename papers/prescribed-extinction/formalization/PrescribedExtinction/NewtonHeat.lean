import PrescribedExtinction.NewtonContact
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The actual Newton kernel as an integral of positive-time heat kernels.
This identity is asserted only away from the origin. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

private theorem reciprocal_gamma_integrand (a t : ℝ) (ht : 0 < t) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) *
        ((t ^ (-1 : ℝ)) ^ ((1 / 2 : ℝ) - 1) *
          Real.exp (-(a * t ^ (-1 : ℝ)))) =
      t ^ (-(3 / 2 : ℝ)) * Real.exp (-a / t) := by
  simp only [abs_neg, abs_one, one_mul]
  rw [← Real.rpow_mul ht.le, ← mul_assoc, ← Real.rpow_add ht]
  have he : (-1 : ℝ) - 1 + (-1) * ((1 / 2 : ℝ) - 1) = -(3 / 2 : ℝ) := by ring
  rw [he]
  simp only [Real.rpow_neg_one, div_eq_mul_inv, neg_mul]

theorem newton_heat_scalar_integral (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ (-(3 / 2 : ℝ)) * Real.exp (-a / t)) =
      (1 / a) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi := by
  have h := integral_comp_rpow_Ioi
    (fun u : ℝ => u ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * u)))
    (p := (-1 : ℝ)) (by norm_num)
  simp only [smul_eq_mul] at h
  have hc : (∫ t : ℝ in Ioi 0,
      (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) *
        ((t ^ (-1 : ℝ)) ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * t ^ (-1 : ℝ))))) =
      ∫ t : ℝ in Ioi 0, t ^ (-(3 / 2 : ℝ)) * Real.exp (-a / t) := by
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => reciprocal_gamma_integrand a t ht
  rw [hc] at h
  rw [h, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : 0 < (1 / 2 : ℝ)) ha,
    Real.Gamma_one_half_eq]

theorem newton_heat_scalar_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * Real.exp (-a / t)) (Ioi 0) := by
  by_contra h
  have he := newton_heat_scalar_integral a ha
  rw [integral_undef h] at he
  have hp : 0 < (1 / a) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi := by positivity
  linarith

def newtonHeatKernel (t : ℝ) (x : Position) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖x‖ ^ 2 / (4 * t))

theorem newtonHeatKernel_factor (t : ℝ) (ht : 0 < t) (x : Position) :
    newtonHeatKernel t x =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖x‖ ^ 2 / 4) / t)) := by
  unfold newtonHeatKernel
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) ht.le]
  have he : -‖x‖ ^ 2 / (4 * t) = -(‖x‖ ^ 2 / 4) / t := by ring
  rw [he]
  ring

theorem newtonHeatKernel_integrable (x : Position) (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => newtonHeatKernel t x) (Ioi 0) := by
  have h := (newton_heat_scalar_integrable (‖x‖ ^ 2 / 4) (by positivity)).const_mul
    ((4 * Real.pi) ^ (-(3 / 2 : ℝ)))
  exact (integrableOn_congr_fun
    (fun t ht => newtonHeatKernel_factor t ht x) measurableSet_Ioi).mpr h

private theorem newton_heat_constant (r : ℝ) (hr : 0 < r) :
    (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (1 / (r ^ 2 / 4)) ^ (1 / 2 : ℝ) *
      Real.sqrt Real.pi = (4 * Real.pi * r)⁻¹ := by
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ)) using 1
    norm_num
  have hs : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), hs4]
  have hs' : Real.sqrt (1 / (r ^ 2 / 4)) = 2 / r := by
    rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ)), Real.sqrt_one,
      Real.sqrt_div (sq_nonneg r), Real.sqrt_sq hr.le]
    rw [hs4]
    field_simp
  rw [← Real.sqrt_eq_rpow, hs']
  rw [show -(3 / 2 : ℝ) = (-1 : ℝ) + -(1 / 2 : ℝ) by ring,
    Real.rpow_add (by positivity : 0 < 4 * Real.pi), Real.rpow_neg_one,
    Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi), ← Real.sqrt_eq_rpow, hs]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

theorem newton_heat_representation (x : Position) (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0, newtonHeatKernel t x) = newtonReal x := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖x‖ ^ 2 / 4) / t)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => newtonHeatKernel_factor t ht x
    _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        ((1 / (‖x‖ ^ 2 / 4)) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi) := by
      rw [integral_const_mul, newton_heat_scalar_integral (‖x‖ ^ 2 / 4) (by positivity)]
    _ = newtonReal x := by
      rw [← mul_assoc, newton_heat_constant ‖x‖ (norm_pos_iff.mpr hx)]
      rfl

theorem newtonHeatKernel_not_integrable_at_origin :
    ¬ IntegrableOn (fun t : ℝ => newtonHeatKernel t (0 : Position)) (Ioi 0) := by
  intro h
  have hc : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) ≠ 0 := (by positivity :
    0 < (4 * Real.pi) ^ (-(3 / 2 : ℝ))).ne'
  have hf : ∀ t ∈ Ioi (0 : ℝ), newtonHeatKernel t (0 : Position) =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by
    intro t ht
    rw [newtonHeatKernel_factor t ht]
    simp
  have hh := (integrableOn_congr_fun hf measurableSet_Ioi).mp h
  have hh' : IntegrableOn (fun t : ℝ => ((4 * Real.pi) ^ (-(3 / 2 : ℝ)))⁻¹ *
      ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)))) (Ioi 0) :=
    hh.const_mul (((4 * Real.pi) ^ (-(3 / 2 : ℝ)))⁻¹)
  apply not_integrableOn_Ioi_rpow (-(3 / 2 : ℝ))
  apply hh'.congr_fun _ measurableSet_Ioi
  intro t _
  change ((4 * Real.pi) ^ (-(3 / 2 : ℝ)))⁻¹ *
    ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ))) = _
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end OQ7Prescribed
