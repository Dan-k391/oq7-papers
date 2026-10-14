import work.SlabSecondWindow

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarScalarGreen_norm (k s : ℝ) (hk : 0 < k) :
    ‖planarScalarGreen k s‖ = 1 / (2 * k) := by
  simp [planarScalarGreen, norm_mul, norm_div, apertureOscillation_norm,
    Complex.norm_real, abs_of_pos hk]

theorem horizontalSlabPotential_second_scaled_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w)
    (A X L C₄ C₆ : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄)
    (h₆ : ∀ y, ‖iteratedFDeriv ℝ 6 w y‖ ≤ C₆)
    (R s : ℝ) (x u v : ℂ) (hR : 1 ≤ R) (hs : |s| ≤ L) (hx : ‖x‖ ≤ X * R)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖horizontalSlabPotential k s (apertureWindowSecond (scaledApertureWindow w R) u v) x -
      planarScalarGreen k s * apertureWindowSecond (scaledApertureWindow w R) u v x‖ ≤
      (L * C₄ + (A + X + 1 + L) * (C₄ + (A + X + 1 + L) ^ 2 * C₆ / 3)) /
        (2 * k ^ 2 * R ^ 3) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h₄0 := (norm_nonneg (iteratedFDeriv ℝ 4 w (0 : ℂ))).trans (h₄ 0)
  have h₆0 := (norm_nonneg (iteratedFDeriv ℝ 6 w (0 : ℂ))).trans (h₆ 0)
  have hUR : 0 < A + X + 1 := by linarith
  let W := apertureWindowSecond (scaledApertureWindow w R) u v
  let U := (A + X + 1) * R
  let T := slabHeightRadius s U
  let B := A + X + 1 + L
  have hW : ContDiff ℝ (⊤ : ℕ∞) W :=
    apertureWindowSecond_contDiff _ (scaledApertureWindow_contDiff w hw R) u v
  have hWc : HasCompactSupport W :=
    apertureWindowSecond_hasCompactSupport _ (scaledApertureWindow_hasCompactSupport w hc R hR0.ne') u v
  have hWsupport : tsupport W ⊆ Metric.closedBall 0 (R * A) :=
    (apertureWindowSecond_support _ u v).trans (scaledApertureWindow_support w R A hR0 hA)
  have hW₂ : ∀ y, ‖iteratedFDeriv ℝ 2 W y‖ ≤ (C₄ / R ^ 2) / R ^ 2 := by
    have hh := scaledApertureWindow_second_jetBound 2 w hw R C₄ hR0 h₄ u v hu hv
    intro y
    apply (hh y).trans
    apply le_of_eq
    field_simp
    <;> ring
  have hW₄ : ∀ y, ‖iteratedFDeriv ℝ 4 W y‖ ≤ (C₆ / R ^ 2) / R ^ 4 := by
    have hh := scaledApertureWindow_second_jetBound 4 w hw R C₆ hR0 h₆ u v hu hv
    intro y
    apply (hh y).trans
    apply le_of_eq
    field_simp
    <;> ring
  have he := horizontalSlabPotential_error k hk s W hW hWc x U (R * A)
    ((C₄ / R ^ 2) / R ^ 2) ((C₆ / R ^ 2) / R ^ 4)
    (mul_pos hUR hR0) hWsupport (by dsimp [U]; nlinarith) hW₂ hW₄
  have hb := slabScaled_error_algebra k R L B (C₄ / R ^ 2) (C₆ / R ^ 2) T s
    hk hR hL (by dsimp [B]; linarith) (by positivity) (by positivity) hs
    (slabHeightRadius_upper s U (mul_pos hUR hR0))
    (slabScaled_radius_bound s R (A + X + 1) L hR hUR.le hL hs)
  apply (he.trans hb).trans
  apply le_of_eq
  dsimp [B]
  field_simp
  <;> ring

theorem horizontalSlabPotential_hessian_scaled_bound (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w)
    (A X L C₂ C₄ C₆ : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A)
    (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄)
    (h₆ : ∀ y, ‖iteratedFDeriv ℝ 6 w y‖ ≤ C₆)
    (R s : ℝ) (x u v : ℂ) (hR : 1 ≤ R) (hs : |s| ≤ L) (hx : ‖x‖ ≤ X * R)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fun y => fderiv ℝ (horizontalSlabPotential k s (scaledApertureWindow w R)) y u) x v‖ ≤
      (C₂ / (2 * k) +
        (L * C₄ + (A + X + 1 + L) * (C₄ + (A + X + 1 + L) ^ 2 * C₆ / 3)) / (2 * k ^ 2)) / R ^ 2 := by
  rw [horizontalSlabPotential_second_partial k s _ (scaledApertureWindow_contDiff w hw R)
    (scaledApertureWindow_hasCompactSupport w hc R (by linarith))]
  have he := horizontalSlabPotential_second_scaled_error k hk w hw hc A X L C₄ C₆ hA0 hX hL hA
    h₄ h₆ R s x u v hR hs hx hu hv
  have hR0 : 0 < R := by linarith
  have hW := scaledApertureWindow_second_jetBound 0 w hw R C₂ hR0 h₂ u v hu hv x
  simp only [norm_iteratedFDeriv_zero, zero_add] at hW
  have h₂0 := (norm_nonneg (iteratedFDeriv ℝ 2 w (0 : ℂ))).trans (h₂ 0)
  have h₄0 := (norm_nonneg (iteratedFDeriv ℝ 4 w (0 : ℂ))).trans (h₄ 0)
  have h₆0 := (norm_nonneg (iteratedFDeriv ℝ 6 w (0 : ℂ))).trans (h₆ 0)
  let N := L * C₄ + (A + X + 1 + L) * (C₄ + (A + X + 1 + L) ^ 2 * C₆ / 3)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hP : ‖planarScalarGreen k s * apertureWindowSecond (scaledApertureWindow w R) u v x‖ ≤
      (1 / (2 * k)) * (C₂ / R ^ 2) := by
    rw [norm_mul, planarScalarGreen_norm k s hk]
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  apply (norm_le_norm_sub_add
    (horizontalSlabPotential k s (apertureWindowSecond (scaledApertureWindow w R) u v) x)
    (planarScalarGreen k s * apertureWindowSecond (scaledApertureWindow w R) u v x)).trans
  apply (add_le_add he hP).trans
  calc
    _ = (N / (2 * k ^ 2) / R + C₂ / (2 * k)) / R ^ 2 := by
      field_simp
      <;> ring
    _ ≤ (N / (2 * k ^ 2) + C₂ / (2 * k)) / R ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg R)
      exact add_le_add (div_le_self (by positivity : 0 ≤ N / (2 * k ^ 2)) hR) le_rfl
    _ = _ := by simp only [N]; ring

end OQ7Prescribed
