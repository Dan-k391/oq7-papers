import PrescribedExtinction.SlabGreen
import PrescribedExtinction.ApertureRadialEstimate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabHeightRadius (s r : ℝ) : ℝ := Real.sqrt (r ^ 2 + s ^ 2)

def slabHeightRadiusDeriv (s r : ℝ) : ℝ := if s = 0 then 1 else r / slabHeightRadius s r

theorem slabHeightRadius_continuous (s : ℝ) : Continuous (slabHeightRadius s) := by
  unfold slabHeightRadius
  fun_prop

theorem slabHeightRadius_pos (s r : ℝ) (hr : 0 < r) : 0 < slabHeightRadius s r := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg s]

theorem slabHeightRadius_lower (s : ℝ) : slabHeightRadius s 0 = |s| := by
  simp [slabHeightRadius, Real.sqrt_sq_eq_abs]

theorem slabHeightRadiusDeriv_continuous (s : ℝ) : Continuous (slabHeightRadiusDeriv s) := by
  by_cases hs : s = 0
  · have hf : slabHeightRadiusDeriv s = fun _ : ℝ => (1 : ℝ) := by
      funext r
      simp [slabHeightRadiusDeriv, hs]
    rw [hf]
    exact continuous_const
  · change Continuous (fun r : ℝ => slabHeightRadiusDeriv s r)
    simp only [slabHeightRadiusDeriv, hs, ite_false]
    exact continuous_id.div (slabHeightRadius_continuous s) (fun r => by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      nlinarith [sq_pos_of_ne_zero hs, sq_nonneg r])

theorem slabHeightRadiusDeriv_eq (s r : ℝ) (hr : 0 < r) :
    slabHeightRadiusDeriv s r = r / slabHeightRadius s r := by
  by_cases hs : s = 0
  · simp [slabHeightRadiusDeriv, slabHeightRadius, hs, Real.sqrt_sq hr.le, hr.ne']
  · simp [slabHeightRadiusDeriv, hs]

theorem slabHeightRadius_hasDerivAt (s r : ℝ) (hr : 0 < r) :
    HasDerivAt (slabHeightRadius s) (slabHeightRadiusDeriv s r) r := by
  rw [slabHeightRadiusDeriv_eq s r hr]
  have hn : r ^ 2 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  have he := (((hasDerivAt_id r).pow 2).add_const (s ^ 2)).sqrt hn
  convert he using 1
  · rfl
  · norm_num only [Pi.pow_apply, id_eq, Nat.cast_ofNat, pow_one, mul_one,
      show (2 : ℕ) - 1 = 1 from rfl]
    unfold slabHeightRadius
    field_simp

theorem slabHeightRadius_lift (w : ℂ → ℂ) (x : ℂ) (s r : ℝ) (hr : 0 ≤ r) :
    apertureRadialLift w x s (slabHeightRadius s r) = apertureCircleJet 0 w x r := by
  unfold apertureRadialLift slabHeightRadius
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), add_sub_cancel_right,
    Real.sqrt_sq hr]

theorem slabRadial_change_variables (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (x : ℂ) (k s U : ℝ) (hU : 0 < U) :
    (∫ r in (0 : ℝ)..U, slabHeightRadiusDeriv s r •
      (apertureOscillation k (slabHeightRadius s r) * apertureCircleJet 0 w x r)) =
      ∫ t in |s|..slabHeightRadius s U, apertureOscillation k t * apertureRadialLift w x s t := by
  have hg : Continuous (fun t => apertureOscillation k t * apertureRadialLift w x s t) :=
    (apertureOscillation_continuous k).mul (apertureRadialLift_continuous w hw x s)
  have he := intervalIntegral.integral_deriv_smul_comp''
    (a := 0) (b := U) (f := slabHeightRadius s) (f' := slabHeightRadiusDeriv s)
    (g := fun t => apertureOscillation k t * apertureRadialLift w x s t)
    (slabHeightRadius_continuous s).continuousOn
    (fun r hr => (slabHeightRadius_hasDerivAt s r (by simpa [min_eq_left hU.le] using hr.1)).hasDerivWithinAt)
    (slabHeightRadiusDeriv_continuous s).continuousOn hg.continuousOn
  rw [slabHeightRadius_lower] at he
  rw [← he]
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ (fun r hr => by
    have hr0 : 0 < r := by simpa only [min_eq_left hU.le] using hr.1
    simp only [Function.comp_apply, slabHeightRadius_lift w x s r hr0.le])

end OQ7Prescribed
