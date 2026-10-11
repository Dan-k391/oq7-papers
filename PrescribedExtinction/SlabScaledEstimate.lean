import PrescribedExtinction.SlabConvolution
import PrescribedExtinction.ApertureWindowScale

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem slabScaled_radius_bound (s R c L : ℝ) (hR : 1 ≤ R) (hc : 0 ≤ c)
    (hL : 0 ≤ L) (hs : |s| ≤ L) :
    slabHeightRadius s (c * R) ≤ (c + L) * R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs2 : s ^ 2 ≤ L ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  have hLR : L ≤ L * R := by nlinarith
  have hLR2 : L ^ 2 ≤ (L * R) ^ 2 := by nlinarith
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (add_nonneg hc hL) hR0.le
  · nlinarith [mul_nonneg (mul_nonneg hc hR0.le) (mul_nonneg hL hR0.le)]

theorem slabScaled_error_algebra (k R L B C₂ C₄ T s : ℝ)
    (hk : 0 < k) (hR : 1 ≤ R) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (h₂ : 0 ≤ C₂) (h₄ : 0 ≤ C₄) (hs : |s| ≤ L)
    (hT0 : |s| < T) (hT : T ≤ B * R) :
    (|s| * (C₂ / R ^ 2) + (C₂ / R ^ 2 + T ^ 2 * (C₄ / R ^ 4) / 3) *
      (T - |s|)) / (2 * k ^ 2) ≤
      (L * C₂ + B * (C₂ + B ^ 2 * C₄ / 3)) / (2 * k ^ 2 * R) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ht0 : 0 ≤ T := (abs_nonneg s).trans hT0.le
  have ht1 : T - |s| ≤ B * R := by linarith [abs_nonneg s]
  calc
    _ ≤ (L * (C₂ / R ^ 2) +
        (C₂ / R ^ 2 + (B * R) ^ 2 * (C₄ / R ^ 4) / 3) * (B * R)) / (2 * k ^ 2) := by
      gcongr
    _ = (L * C₂ / R + B * (C₂ + B ^ 2 * C₄ / 3)) / (2 * k ^ 2 * R) := by
      field_simp
      <;> ring
    _ ≤ _ := by
      gcongr
      exact div_le_self (mul_nonneg hL h₂) hR

theorem horizontalSlabPotential_scaled_error (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w)
    (A X L C₂ C₄ : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A)
    (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄)
    (R s : ℝ) (x : ℂ) (hR : 1 ≤ R) (hs : |s| ≤ L) (hx : ‖x‖ ≤ X * R) :
    ‖horizontalSlabPotential k s (scaledApertureWindow w R) x -
      planarScalarGreen k s * scaledApertureWindow w R x‖ ≤
      (L * C₂ + (A + X + 1 + L) * (C₂ + (A + X + 1 + L) ^ 2 * C₄ / 3)) /
        (2 * k ^ 2 * R) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h₂0 := (norm_nonneg (iteratedFDeriv ℝ 2 w (0 : ℂ))).trans (h₂ 0)
  have h₄0 := (norm_nonneg (iteratedFDeriv ℝ 4 w (0 : ℂ))).trans (h₄ 0)
  have hc0 : 0 < A + X + 1 := by linarith
  have he := horizontalSlabPotential_error k hk s (scaledApertureWindow w R)
    (scaledApertureWindow_contDiff w hw R) (scaledApertureWindow_hasCompactSupport w hc R hR0.ne')
    x ((A + X + 1) * R) (R * A) (C₂ / R ^ 2) (C₄ / R ^ 4)
    (mul_pos hc0 hR0) (scaledApertureWindow_support w R A hR0 hA)
    (by nlinarith) (scaledApertureWindow_jetBound 2 w hw R C₂ hR0 h₂)
    (scaledApertureWindow_jetBound 4 w hw R C₄ hR0 h₄)
  exact he.trans (slabScaled_error_algebra k R L (A + X + 1 + L) C₂ C₄
    (slabHeightRadius s ((A + X + 1) * R)) s hk hR hL (by linarith) h₂0 h₄0 hs
    (slabHeightRadius_upper s _ (mul_pos hc0 hR0))
    (slabScaled_radius_bound s R (A + X + 1) L hR hc0.le hL hs))

theorem horizontalSlabPotential_uniform_aperture_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R s : ℝ) (x : ℂ), 1 ≤ R → |s| ≤ L → ‖x‖ ≤ X * R →
      ‖horizontalSlabPotential k s (scaledApertureWindow w R) x -
        planarScalarGreen k s * scaledApertureWindow w R x‖ ≤ C / R := by
  obtain ⟨C₂, h₂pos, h₂⟩ := hc.exists_bound_iteratedFDeriv hw 2
  obtain ⟨C₄, h₄pos, h₄⟩ := hc.exists_bound_iteratedFDeriv hw 4
  let B := A + X + 1 + L
  let C := (L * C₂ + B * (C₂ + B ^ 2 * C₄ / 3)) / (2 * k ^ 2) + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R s x hR hs hx
  apply (horizontalSlabPotential_scaled_error k hk w hw hc A X L C₂ C₄ hA0 hX hL hA
    (fun y => h₂ 2 le_rfl y) (fun y => h₄ 4 le_rfl y) R s x hR hs hx).trans
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  change (L * C₂ + B * (C₂ + B ^ 2 * C₄ / 3)) / (2 * k ^ 2 * R) ≤ C / R
  rw [div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hR0.le
  dsimp [C]
  linarith

end OQ7Prescribed
