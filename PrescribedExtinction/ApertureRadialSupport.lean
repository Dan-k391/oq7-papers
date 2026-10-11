import PrescribedExtinction.ApertureRadialLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem apertureCircleJet_outside_support (n : ℕ) (w : ℂ → ℂ) (x : ℂ) (r A : ℝ)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (hr : A + ‖x‖ < r) :
    apertureCircleJet n w x r = 0 := by
  have hA0 : 0 ≤ A ∨ tsupport w = ∅ := by
    by_cases h : 0 ≤ A
    · exact Or.inl h
    · right
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hs := hA hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hs
      exact (not_le.mpr (lt_of_not_ge h)) ((norm_nonneg z).trans hs)
  by_cases hw : tsupport w = ∅
  · have hz : w = 0 := tsupport_eq_empty_iff.mp hw
    simp [apertureCircleJet, apertureDirectionalJet, hz]
  · have hp : 0 < r := lt_of_le_of_lt (add_nonneg (hA0.resolve_right hw) (norm_nonneg x)) hr
    have hz (θ : ℝ) : iteratedFDeriv ℝ n w (x + r • apertureCircleDirection θ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hpos := hA (tsupport_iteratedFDeriv_subset n hs)
      simp only [Metric.mem_closedBall, dist_zero_right] at hpos
      have hn := norm_add_le (x + r • apertureCircleDirection θ) (-x)
      have he : (x + r • apertureCircleDirection θ) + (-x) = r • apertureCircleDirection θ := by ring
      rw [he] at hn
      simp only [norm_neg, norm_smul, Real.norm_eq_abs,
        apertureCircleDirection_norm, mul_one, abs_of_pos hp] at hn
      linarith
    unfold apertureCircleJet apertureDirectionalJet
    simp only [hz, ContinuousMultilinearMap.zero_apply, intervalIntegral.integral_zero, smul_zero]

theorem apertureRadialLift_outside_support (w : ℂ → ℂ) (x : ℂ) (s t A : ℝ)
    (hA : tsupport w ⊆ Metric.closedBall 0 A)
    (ht : A + ‖x‖ < Real.sqrt (t ^ 2 - s ^ 2)) : apertureRadialLift w x s t = 0 :=
  apertureCircleJet_outside_support 0 w x _ A hA ht

theorem apertureRadialLiftDeriv_outside_support (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (s t A : ℝ)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (hr : 0 < Real.sqrt (t ^ 2 - s ^ 2))
    (ht : A + ‖x‖ < Real.sqrt (t ^ 2 - s ^ 2)) : apertureRadialLiftDeriv w x s t = 0 := by
  have hs := apertureMeanSlope_first_jet w hw hc x (Real.sqrt (t ^ 2 - s ^ 2))
  rw [apertureCircleJet_outside_support 1 w x _ A hA ht] at hs
  have hz := (smul_eq_zero.mp hs).resolve_left hr.ne'
  simp [apertureRadialLiftDeriv, hz]

end OQ7Prescribed
