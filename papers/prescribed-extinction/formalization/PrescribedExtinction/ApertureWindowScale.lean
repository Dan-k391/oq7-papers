import PrescribedExtinction.ApertureCircleJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def scaledApertureWindow (w : ℂ → ℂ) (R : ℝ) (x : ℂ) : ℂ := w (R⁻¹ • x)

theorem scaledApertureWindow_contDiff (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledApertureWindow w R) :=
  hw.comp (contDiff_id.const_smul R⁻¹)

theorem scaledApertureWindow_hasCompactSupport (w : ℂ → ℂ) (hc : HasCompactSupport w)
    (R : ℝ) (hR : R ≠ 0) : HasCompactSupport (scaledApertureWindow w R) :=
  hc.comp_smul (inv_ne_zero hR)

theorem scaledApertureWindow_support (w : ℂ → ℂ) (R A : ℝ) (hR : 0 < R)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    tsupport (scaledApertureWindow w R) ⊆ Metric.closedBall 0 (R * A) := by
  have hs := tsupport_comp_subset_preimage w
    (continuous_const_smul R⁻¹ : Continuous (fun x : ℂ => R⁻¹ • x))
  intro x hx
  have hm := hA (hs hx)
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at hm ⊢
  have he : R * (R⁻¹ * ‖x‖) = ‖x‖ := by rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  nlinarith

theorem scaledApertureWindow_iteratedFDeriv (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (R : ℝ) (x : ℂ) :
    iteratedFDeriv ℝ n (scaledApertureWindow w R) x =
      (R⁻¹) ^ n • iteratedFDeriv ℝ n w (R⁻¹ • x) := by
  exact congrFun (iteratedFDeriv_comp_const_smul R⁻¹ (hw.of_le (by simp))) x

theorem scaledApertureWindow_jetBound (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (R C : ℝ) (hR : 0 < R)
    (hC : ∀ y, ‖iteratedFDeriv ℝ n w y‖ ≤ C) :
    ∀ x, ‖iteratedFDeriv ℝ n (scaledApertureWindow w R) x‖ ≤ C / R ^ n := by
  intro x
  rw [scaledApertureWindow_iteratedFDeriv n w hw R x, norm_smul]
  rw [Real.norm_eq_abs, inv_pow, abs_of_pos (inv_pos.mpr (pow_pos hR n))]
  simp only [div_eq_mul_inv]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr (pow_nonneg hR.le n))

end OQ7Prescribed
