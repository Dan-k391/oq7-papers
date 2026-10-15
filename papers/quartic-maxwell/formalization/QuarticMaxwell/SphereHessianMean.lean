import QuarticMaxwell.SphereExterior

/-! Pointwise and double-ball mean identities for the actual Newton Hessian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QuarticMaxwell.SphereHessianMean
open OQ7Prescribed SphereStatic SphereExterior StaticOffSupport StaticHessian MeasureTheory Set

theorem hessian_continuousAt (x : Position) (hx : x ≠ 0) :
    ContinuousAt newtonHessianOperator x := by
  let d := ‖x‖ / 2
  have hd : 0 < d := half_pos (norm_pos_iff.mpr hx)
  let C := 6 / (Real.pi * d ^ 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min d (ε / (C + 1)), lt_min hd (div_pos hε (by linarith)), ?_⟩
  intro y hy
  rw [dist_eq_norm] at hy ⊢
  have hdy : ‖y - x‖ < d := lt_of_lt_of_le hy (min_le_left _ _)
  have hny : d ≤ ‖y‖ := by
    have hh := norm_add_le (x - y) y
    rw [sub_add_cancel, norm_sub_rev] at hh
    dsimp [d] at hdy ⊢
    linarith
  have hh := newtonHessianOperator_difference y x hd hny (by dsimp [d]; linarith [norm_nonneg x])
  have he : (C + 1) * ‖y - x‖ < ε := by
    have hy' := lt_of_lt_of_le hy (min_le_right d (ε / (C + 1)))
    nlinarith [(lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hy']
  change ‖newtonHessianOperator y - newtonHessianOperator x‖ ≤ C * ‖y - x‖ at hh
  nlinarith [norm_nonneg (y - x)]

def ballHessian (c : Position) (a : ℝ) (v : Vector) (x : Position) : Vector :=
  ∫ y in Metric.ball c a, newtonHessianOperator (x - y) v

theorem ball_separation (c : Position) (a d : ℝ) {x y : Position}
    (hx : a + d < ‖x - c‖) (hy : y ∈ Metric.ball c a) : d ≤ ‖x - y‖ := by
  have hy' : ‖y - c‖ < a := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hh : ‖x - c‖ ≤ ‖x - y‖ + ‖y - c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (x - y) (y - c)
  linarith

theorem ballHessian_continuousOn (c : Position) (a : ℝ) {d : ℝ} (hd : 0 < d) (v : Vector) :
    ContinuousOn (ballHessian c a v) {x | a + d < ‖x - c‖} := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball c a)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (ball_measure_ne_top c a).lt_top⟩
  apply continuousOn_of_dominated (bound := fun _ : Position => 1 / (2 * Real.pi * d ^ 3) * ‖v‖)
  · intro x _
    exact ((ContinuousLinearMap.apply ℂ Vector v).continuous.measurable.comp
      (newtonHessianOperator_measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · intro x hx
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hsep := ball_separation c a d hx hy
    have hn : x - y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hd hsep))
    apply ((newtonHessianOperator (x - y)).le_opNorm v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (newtonHessianOperator_norm_le _ hn).trans
    gcongr
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    intro x hx
    have hsep := ball_separation c a d hx hy
    have hn : x - y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hd hsep))
    have hH : ContinuousAt (fun z : Position => newtonHessianOperator (z - y)) x :=
      (hessian_continuousAt (x - y) hn).comp (f := fun z : Position => z - y)
        (continuousAt_id.sub continuousAt_const)
    exact ((ContinuousLinearMap.apply ℂ Vector v).continuous.continuousAt.comp
      (f := fun z : Position => newtonHessianOperator (z - y)) hH).continuousWithinAt

theorem vectorKernelField_ball (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector)
    {d : ℝ} (hd : 0 < d) (x : Position) (hx : a + d < ‖x - c‖) :
    vectorKernelField (ballPolarization c a ha.le v) (d / 2) x = ballHessian c a v x := by
  unfold vectorKernelField ballHessian
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [ballPolarization_current c a ha.le v] with y hy
  rw [hy]
  by_cases hym : y ∈ Metric.ball c a
  · have hs : d / 2 < ‖x - y‖ := lt_of_lt_of_le (by linarith) (ball_separation c a d hx hym)
    simp [Set.indicator, hym, exteriorHessian, hs]
  · simp [Set.indicator, hym]

end QuarticMaxwell.SphereHessianMean
