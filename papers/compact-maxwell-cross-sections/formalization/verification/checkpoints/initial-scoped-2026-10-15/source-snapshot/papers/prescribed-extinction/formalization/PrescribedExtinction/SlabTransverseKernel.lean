import PrescribedExtinction.SlabHessianEstimate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped InnerProductSpace

def horizontalSlabTransverseKernel (k s : ℝ) (w : ℂ → ℂ) (x u v : ℂ) : ℂ :=
  (k ^ 2 * inner ℝ u v : ℝ) • horizontalSlabPotential k s w x +
    fderiv ℝ (fun y => fderiv ℝ (horizontalSlabPotential k s w) y u) x v

theorem horizontalSlabTransverseKernel_uniform_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R s : ℝ) (x u v : ℂ), 1 ≤ R → |s| ≤ L → ‖x‖ ≤ X * R →
      ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ‖horizontalSlabTransverseKernel k s (scaledApertureWindow w R) x u v -
        (k ^ 2 * inner ℝ u v : ℝ) • (planarScalarGreen k s * scaledApertureWindow w R x)‖ ≤ C / R := by
  obtain ⟨C₀, hC₀, h₀⟩ := horizontalSlabPotential_uniform_aperture_error k hk w hw hc A X L hA0 hX hL hA
  obtain ⟨C₂, h₂pos, h₂⟩ := hc.exists_bound_iteratedFDeriv hw 2
  obtain ⟨C₄, h₄pos, h₄⟩ := hc.exists_bound_iteratedFDeriv hw 4
  obtain ⟨C₆, h₆pos, h₆⟩ := hc.exists_bound_iteratedFDeriv hw 6
  let D := C₂ / (2 * k) +
    (L * C₄ + (A + X + 1 + L) * (C₄ + (A + X + 1 + L) ^ 2 * C₆ / 3)) / (2 * k ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := k ^ 2 * C₀ + D + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R s x u v hR hs hx hu hv
  have hR0 : 0 < R := by linarith
  have he := h₀ R s x hR hs hx
  have hh := horizontalSlabPotential_hessian_scaled_bound k hk w hw hc A X L C₂ C₄ C₆
    hA0 hX hL hA (h₂ 2 le_rfl) (h₄ 4 le_rfl) (h₆ 6 le_rfl) R s x u v hR hs hx hu hv
  have hi : |inner ℝ u v| ≤ 1 := by
    apply (abs_real_inner_le_norm u v).trans
    calc
      ‖u‖ * ‖v‖ ≤ 1 * 1 := mul_le_mul hu hv (norm_nonneg v) zero_le_one
      _ = _ := by norm_num
  have hn : ‖(k ^ 2 * inner ℝ u v : ℝ)‖ ≤ k ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg k)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (sq_nonneg k)
  have heq : horizontalSlabTransverseKernel k s (scaledApertureWindow w R) x u v -
      (k ^ 2 * inner ℝ u v : ℝ) • (planarScalarGreen k s * scaledApertureWindow w R x) =
      (k ^ 2 * inner ℝ u v : ℝ) •
        (horizontalSlabPotential k s (scaledApertureWindow w R) x -
          planarScalarGreen k s * scaledApertureWindow w R x) +
        fderiv ℝ (fun y => fderiv ℝ (horizontalSlabPotential k s (scaledApertureWindow w R)) y u) x v := by
    unfold horizontalSlabTransverseKernel
    rw [smul_sub]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  apply (add_le_add (mul_le_mul hn he (norm_nonneg _) (sq_nonneg k)) hh).trans
  calc
    _ ≤ k ^ 2 * (C₀ / R) + D / R := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_left hD hR0
      nlinarith
    _ ≤ C / R := by
      dsimp [C]
      rw [← mul_div_assoc, ← add_div]
      apply div_le_div_of_nonneg_right _ hR0.le
      linarith

end OQ7Prescribed
