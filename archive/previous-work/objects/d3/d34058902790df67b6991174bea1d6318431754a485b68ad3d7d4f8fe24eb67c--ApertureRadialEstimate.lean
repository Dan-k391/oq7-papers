import work.ApertureRadialSupport

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem apertureRadialLiftSecond_measurable (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) (s : ℝ) :
    Measurable (apertureRadialLiftSecond w x s) := by
  have hA := apertureMeanSlope_continuous w hw x
  have hD := apertureMeanSlopeDeriv_continuous w hw x
  unfold apertureRadialLiftSecond
  fun_prop

theorem apertureRadialLiftSecond_intervalIntegrable (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (s T C₂ C₄ : ℝ)
    (hT : |s| < T) (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄) :
    IntervalIntegrable (apertureRadialLiftSecond w x s) volume |s| T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
  have hi : IntegrableOn (fun _ : ℝ => C₂ + T ^ 2 * C₄ / 3) (Ioc |s| T) :=
    integrableOn_const (hs := by simp)
  apply hi.mono' (apertureRadialLiftSecond_measurable w hw x s).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply (apertureRadialLiftSecond_norm_le w hw hc x s t C₂ C₄ ht.1 h₂ h₄).trans
  have h₄0 := (norm_nonneg (iteratedFDeriv ℝ 4 w (0 : ℂ))).trans (h₄ 0)
  have ht0 := (abs_nonneg s).trans ht.1.le
  have hT0 := (abs_nonneg s).trans hT.le
  have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith [ht.2]
  gcongr

theorem apertureRadialLift_oscillatory_error (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (s T A C₂ C₄ : ℝ)
    (hT : |s| < T) (hA : tsupport w ⊆ Metric.closedBall 0 A)
    (hTA : A + ‖x‖ < Real.sqrt (T ^ 2 - s ^ 2))
    (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄) :
    ‖(∫ t in |s|..T, apertureRadialLift w x s t * apertureOscillation k t) +
      (Complex.I * (k : ℂ))⁻¹ * w x * apertureOscillation k |s|‖ ≤
      (|s| * C₂ + (C₂ + T ^ 2 * C₄ / 3) * (T - |s|)) / k ^ 2 := by
  have h₄0 := (norm_nonneg (iteratedFDeriv ℝ 4 w (0 : ℂ))).trans (h₄ 0)
  have hb : ∀ t ∈ Ioc |s| T, ‖apertureRadialLiftSecond w x s t‖ ≤ C₂ + T ^ 2 * C₄ / 3 := by
    intro t ht
    apply (apertureRadialLiftSecond_norm_le w hw hc x s t C₂ C₄ ht.1 h₂ h₄).trans
    have ht0 := (abs_nonneg s).trans ht.1.le
    have hT0 := (abs_nonneg s).trans hT.le
    have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith [ht.2]
    gcongr
  have he := apertureOscillation_error_bound k |s| T hk hT.le
    (apertureRadialLift w x s) (apertureRadialLiftDeriv w x s) (apertureRadialLiftSecond w x s)
    (apertureRadialLift_continuous w hw x s).continuousOn
    (apertureRadialLiftDeriv_continuous w hw x s).continuousOn
    (fun t ht => apertureRadialLift_hasDerivAt w hw hc x s t (by simpa [min_eq_left hT.le] using ht.1))
    (fun t ht => apertureRadialLiftDeriv_hasDerivAt w hw hc x s t (by simpa [min_eq_left hT.le] using ht.1))
    (apertureRadialLiftSecond_intervalIntegrable w hw hc x s T C₂ C₄ hT h₂ h₄)
    (apertureRadialLift_outside_support w x s T A hA hTA)
    (apertureRadialLiftDeriv_outside_support w hw hc x s T A hA (apertureRadialRoot_pos s T hT) hTA)
    (C₂ + T ^ 2 * C₄ / 3) hb
  rw [apertureRadialLift_at_lower] at he
  apply he.trans
  gcongr
  exact apertureRadialLiftDeriv_lower_norm_le w x s C₂ h₂

end OQ7Prescribed
