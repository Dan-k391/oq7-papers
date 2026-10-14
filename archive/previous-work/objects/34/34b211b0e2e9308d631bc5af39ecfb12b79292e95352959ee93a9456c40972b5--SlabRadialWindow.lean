import work.SlabRadialCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabRadialWindow (k s : ℝ) (w : ℂ → ℂ) (x : ℂ) (U : ℝ) : ℂ :=
  (2 * Real.pi) • ∫ r in (0 : ℝ)..U,
    (r : ℂ) * slabGreen k s (circleMap 0 r 0) * apertureCircleJet 0 w x r

def planarScalarGreen (k s : ℝ) : ℂ :=
  Complex.I / (2 * (k : ℂ)) * apertureOscillation k |s|

theorem slabRadialWindow_identity (k s : ℝ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) (U : ℝ) (hU : 0 < U) :
    slabRadialWindow k s w x U = (1 / 2 : ℝ) •
      ∫ t in |s|..slabHeightRadius s U, apertureOscillation k t * apertureRadialLift w x s t := by
  unfold slabRadialWindow
  rw [← intervalIntegral.integral_smul]
  have he : (∫ r in (0 : ℝ)..U,
      (2 * Real.pi) • ((r : ℂ) * slabGreen k s (circleMap 0 r 0) * apertureCircleJet 0 w x r)) =
      ∫ r in (0 : ℝ)..U, (1 / 2 : ℝ) • (slabHeightRadiusDeriv s r •
        (apertureOscillation k (slabHeightRadius s r) * apertureCircleJet 0 w x r)) := by
    apply intervalIntegral.integral_congr_ae
    exact ae_of_all _ (fun r hr => by
      have hr0 : 0 < r := by simpa only [min_eq_left hU.le] using hr.1
      rw [slabGreen_radial, slabHeightRadiusDeriv_eq s r hr0]
      change (2 * Real.pi) • ((r : ℂ) *
        (apertureOscillation k (slabHeightRadius s r) /
          ((4 * Real.pi * slabHeightRadius s r : ℝ) : ℂ)) * apertureCircleJet 0 w x r) = _
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_one]
      field_simp
      <;> ring)
  rw [he, intervalIntegral.integral_smul, slabRadial_change_variables w hw x k s U hU]

theorem slabHeightRadius_upper (s U : ℝ) (hU : 0 < U) :
    |s| < slabHeightRadius s U := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg U) (sq_nonneg s))
  have h0 : 0 ≤ Real.sqrt (U ^ 2 + s ^ 2) := Real.sqrt_nonneg _
  change |s| < Real.sqrt (U ^ 2 + s ^ 2)
  nlinarith [sq_abs s, sq_pos_of_pos hU, abs_nonneg s]

theorem slabHeightRadius_root (s U : ℝ) (hU : 0 ≤ U) :
    Real.sqrt ((slabHeightRadius s U) ^ 2 - s ^ 2) = U := by
  rw [slabHeightRadius, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    add_sub_cancel_right, Real.sqrt_sq hU]

theorem slabRadialWindow_error (k : ℝ) (hk : 0 < k) (s : ℝ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (U A C₂ C₄ : ℝ)
    (hU : 0 < U) (hA : tsupport w ⊆ Metric.closedBall 0 A) (hUA : A + ‖x‖ < U)
    (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄) :
    ‖slabRadialWindow k s w x U - planarScalarGreen k s * w x‖ ≤
      (|s| * C₂ + (C₂ + (slabHeightRadius s U) ^ 2 * C₄ / 3) *
        (slabHeightRadius s U - |s|)) / (2 * k ^ 2) := by
  have he := apertureRadialLift_oscillatory_error k hk w hw hc x s
    (slabHeightRadius s U) A C₂ C₄ (slabHeightRadius_upper s U hU) hA
    (by simpa only [slabHeightRadius_root s U hU.le] using hUA) h₂ h₄
  have halg : slabRadialWindow k s w x U - planarScalarGreen k s * w x =
      (1 / 2 : ℝ) • ((∫ t in |s|..slabHeightRadius s U,
        apertureRadialLift w x s t * apertureOscillation k t) +
        (Complex.I * (k : ℂ))⁻¹ * w x * apertureOscillation k |s|) := by
    rw [slabRadialWindow_identity k s w hw x U hU]
    simp_rw [mul_comm (apertureOscillation k _)]
    unfold planarScalarGreen
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, mul_inv_rev, Complex.inv_I]
    field_simp
    <;> ring
  rw [halg, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
  apply le_of_eq
  ring

end OQ7Prescribed
