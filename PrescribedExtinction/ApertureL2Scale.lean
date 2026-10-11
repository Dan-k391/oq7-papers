import PrescribedExtinction.ApertureWindowScale
import PrescribedExtinction.SeparatedL2Product
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem scaledApertureWindow_integral_norm_sq (w : ℂ → ℂ) (R : ℝ) (hR : 0 < R) :
    (∫ x : ℂ, ‖scaledApertureWindow w R x‖ ^ 2) = R ^ 2 * ∫ x : ℂ, ‖w x‖ ^ 2 := by
  have he := Measure.integral_comp_smul (volume : Measure ℂ) (fun x : ℂ => ‖w x‖ ^ 2) R⁻¹
  simpa only [scaledApertureWindow, Complex.finrank_real_complex, inv_pow, inv_inv,
    abs_of_pos (sq_pos_of_pos hR), smul_eq_mul] using he

theorem scaledApertureWindow_L2_norm (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hc : HasCompactSupport w) (R : ℝ) (hR : 0 < R) :
    ‖((scaledApertureWindow_contDiff w hw R).continuous.memLp_of_hasCompactSupport
      (p := 2) (μ := volume) (scaledApertureWindow_hasCompactSupport w hc R hR.ne')).toLp
      (scaledApertureWindow w R)‖ = R * ‖(hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc).toLp w‖ := by
  let hW := (scaledApertureWindow_contDiff w hw R).continuous.memLp_of_hasCompactSupport
    (p := 2) (μ := volume) (scaledApertureWindow_hasCompactSupport w hc R hR.ne')
  let hwm := hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc
  have hs := scaledApertureWindow_integral_norm_sq w R hR
  rw [memLp_two_integral_norm_sq _ hW, memLp_two_integral_norm_sq _ hwm] at hs
  have hl := norm_nonneg (hW.toLp (scaledApertureWindow w R))
  have hr := mul_nonneg hR.le (norm_nonneg (hwm.toLp w))
  nlinarith

end OQ7Prescribed
