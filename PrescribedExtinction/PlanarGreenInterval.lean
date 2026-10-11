import PrescribedExtinction.SlabRadialWindow

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem apertureOscillation_sub (k z t : ℝ) :
    apertureOscillation k (z - t) = apertureOscillation k z * apertureOscillation (-k) t := by
  unfold apertureOscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem apertureOscillation_opposite_mul (k z : ℝ) :
    apertureOscillation k z * apertureOscillation (-k) z = 1 := by
  rw [← apertureOscillation_sub, sub_self]
  simp [apertureOscillation]

theorem planarGreen_interval_left (k a b z : ℝ) (hab : a ≤ b) (hbz : b ≤ z) (q : ℝ → ℂ) :
    (∫ t in a..b, planarScalarGreen k (z - t) * q t) =
      (Complex.I / (2 * (k : ℂ))) * apertureOscillation k z *
        (∫ t in a..b, apertureOscillation (-k) t * q t) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have htz : t ≤ z := (by simpa only [max_eq_right hab] using ht.2 : t ≤ b).trans hbz
  change planarScalarGreen k (z - t) * q t =
    (Complex.I / (2 * (k : ℂ)) * apertureOscillation k z) * (apertureOscillation (-k) t * q t)
  rw [planarScalarGreen, abs_of_nonneg (sub_nonneg.mpr htz), apertureOscillation_sub]
  ring

theorem planarGreen_interval_right (k a b z : ℝ) (hab : a ≤ b) (hza : z ≤ a) (q : ℝ → ℂ) :
    (∫ t in a..b, planarScalarGreen k (z - t) * q t) =
      (Complex.I / (2 * (k : ℂ))) * apertureOscillation (-k) z *
        (∫ t in a..b, apertureOscillation k t * q t) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hzt : z ≤ t := hza.trans (by simpa only [min_eq_left hab] using ht.1 : a ≤ t)
  change planarScalarGreen k (z - t) * q t =
    (Complex.I / (2 * (k : ℂ)) * apertureOscillation (-k) z) * (apertureOscillation k t * q t)
  rw [planarScalarGreen, abs_of_nonpos (sub_nonpos.mpr hzt), neg_sub, apertureOscillation_sub]
  ring

theorem planarGreen_interval_split (k a b z : ℝ) (haz : a ≤ z) (hzb : z ≤ b) (q : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b)) :
    (∫ t in a..b, planarScalarGreen k (z - t) * q t) =
      (Complex.I / (2 * (k : ℂ))) *
        (apertureOscillation k z * (∫ t in a..z, apertureOscillation (-k) t * q t) +
         apertureOscillation (-k) z * (∫ t in z..b, apertureOscillation k t * q t)) := by
  have hg : Continuous (planarScalarGreen k) :=
    continuous_const.mul ((apertureOscillation_continuous k).comp continuous_abs)
  have hc : ContinuousOn (fun t => planarScalarGreen k (z - t) * q t) (Icc a b) :=
    (hg.comp (continuous_const.sub continuous_id)).continuousOn.mul hq
  have hleft : IntervalIntegrable (fun t => planarScalarGreen k (z - t) * q t) volume a z := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le haz]
    exact hc.mono (Icc_subset_Icc le_rfl hzb)
  have hright : IntervalIntegrable (fun t => planarScalarGreen k (z - t) * q t) volume z b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hzb]
    exact hc.mono (Icc_subset_Icc haz le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    planarGreen_interval_left k a z z haz le_rfl q,
    planarGreen_interval_right k z b z hzb le_rfl q]
  ring

end OQ7Prescribed
