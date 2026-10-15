import QuarticMaxwell.SphereDoubleMean
import QuarticMaxwell.SphereResponse
import QuarticMaxwell.StaticCrossIdentification
import QuarticMaxwell.MomentOperator
import QuarticMaxwell.BallAffineMoments

/-! Actual first static interaction moments and centered-current cancellation
between two finite balls. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QuarticMaxwell.SphereCrossMoment
open OQ7Prescribed StaticHessian SphereStatic SphereResponse StaticCrossIdentification
  SphereExterior SphereDoubleMean CrossBlockOperator MeasureTheory Set

theorem kernel_joint_integrable (T S : Set OQ7Prescribed.Position)
    (hT : MeasurableSet T) (hS : MeasurableSet S) (hfinT : volume T ≠ ⊤) (hfinS : volume S ≠ ⊤)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ T, ∀ y ∈ S, d ≤ ‖x - y‖) (q : VectorL2) :
    Integrable (fun z : OQ7Prescribed.Position × OQ7Prescribed.Position =>
      newtonHessianOperator (z.1 - z.2) (q z.2)) ((volume.restrict T).prod (volume.restrict S)) := by
  let : IsFiniteMeasure (volume.restrict T) := ⟨by simpa using hfinT.lt_top⟩
  let C := 1 / (2 * Real.pi * d ^ 3)
  have hK : Measurable (fun z : OQ7Prescribed.Position × OQ7Prescribed.Position =>
      newtonHessianOperator (z.1 - z.2)) :=
    newtonHessianOperator_measurable.comp (measurable_fst.sub measurable_snd)
  have hm : AEStronglyMeasurable
      (fun z : OQ7Prescribed.Position × OQ7Prescribed.Position => newtonHessianOperator (z.1 - z.2) (q z.2))
      ((volume.restrict T).prod (volume.restrict S)) :=
    (ContinuousLinearMap.id ℂ (Vector →L[ℂ] Vector)).aestronglyMeasurable_comp₂
      hK.aestronglyMeasurable (Lp.aestronglyMeasurable q).restrict.comp_snd
  have hi := (integrable_const C : Integrable (fun _ : OQ7Prescribed.Position => C) (volume.restrict T)).mul_prod
    (integrableOn_Lp_of_measure_ne_top q (by norm_num) hfinS).norm
  apply Integrable.mono' hi hm
  have hmem : ∀ᵐ z ∂((volume.restrict T).prod (volume.restrict S)), z.1 ∈ T ∧ z.2 ∈ S := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hT.prod hS)
  filter_upwards [hmem] with z hz
  exact ((newtonHessianOperator (z.1 - z.2)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (kernel_norm_bound hd hgap z.1 hz.1 z.2 hz.2) (norm_nonneg _))

theorem separated_ball_point (c1 c2 : OQ7Prescribed.Position) {a b : ℝ}
    (hsep : a + b < ‖c1 - c2‖) (y : OQ7Prescribed.Position) (hy : y ∈ Metric.ball c2 b) :
    a < ‖y - c1‖ := by
  have hyb : ‖y - c2‖ < b := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hn : ‖c1 - c2‖ ≤ ‖y - c1‖ + ‖y - c2‖ := by
    have h := norm_add_le (c1 - y) (y - c2)
    simpa only [sub_add_sub_cancel, norm_sub_rev] using h
  linarith

theorem cross_moment (c1 c2 : OQ7Prescribed.Position) {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖)
    (q : DomainL2 (Metric.ball c2 b)) :
    MomentOperator.map (Metric.ball c1 a) (ball_measure_ne_top c1 a)
      (staticCrossBlock (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball q) =
      (ballVolume a : ℂ) • ∫ y in Metric.ball c2 b, newtonHessianOperator (c1 - y) ((q : VectorL2) y) := by
  rw [staticCrossBlock_eq_kernel (Metric.ball c1 a) (Metric.ball c2 b) Metric.isOpen_ball measurableSet_ball
    (ball_measure_ne_top c1 a) (ball_measure_ne_top c2 b) (by positivity : 0 ≤ ‖c2‖ + b)
    (ball_support_bound c2 b) d hd hgap, MomentOperator.map_apply]
  have ho := output_coe (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball
    (ball_measure_ne_top c1 a) (ball_measure_ne_top c2 b) d hd hgap q
  have he : (∫ x in Metric.ball c1 a,
      (operator (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball
        (ball_measure_ne_top c1 a) (ball_measure_ne_top c2 b) d hd hgap q : VectorL2) x) =
      ∫ x in Metric.ball c1 a, ∫ y in Metric.ball c2 b,
        newtonHessianOperator (x - y) ((q : VectorL2) y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ho, ae_restrict_mem measurableSet_ball] with x hx hmem
    change (output (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball
      (ball_measure_ne_top c1 a) (ball_measure_ne_top c2 b) d hd hgap q : VectorL2) x = _
    rw [hx, indicator_of_mem hmem]
    rfl
  rw [he, integral_integral_swap (kernel_joint_integrable _ _ measurableSet_ball measurableSet_ball
    (ball_measure_ne_top c1 a) (ball_measure_ne_top c2 b) hd hgap (q : VectorL2))]
  calc
    _ = ∫ y in Metric.ball c2 b, (ballVolume a : ℂ) • newtonHessianOperator (c1 - y) ((q : VectorL2) y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact ball_mean_reverse c1 ha ((q : VectorL2) y) y (separated_ball_point c1 c2 hsep y hy)
    _ = _ := integral_smul _ _

end QuarticMaxwell.SphereCrossMoment

namespace QuarticMaxwell.SphereCrossMoment
open OQ7Prescribed StaticHessian SphereStatic SphereResponse StaticCrossIdentification
  SphereExterior SphereDoubleMean CrossBlockOperator MeasureTheory Set

theorem cross_zero_mean_bound (c1 c2 : OQ7Prescribed.Position) {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖)
    (q : DomainL2 (Metric.ball c2 b))
    (hzero : MomentOperator.map (Metric.ball c2 b) (ball_measure_ne_top c2 b) q = 0) :
    ‖MomentOperator.map (Metric.ball c1 a) (ball_measure_ne_top c1 a)
      (staticCrossBlock (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball q)‖ ≤
      ballVolume a * (6 / (Real.pi * d ^ 4)) *
        ∫ y in Metric.ball c2 b, ‖y - c2‖ * ‖(q : VectorL2) y‖ := by
  have hc1 : c1 ∈ Metric.ball c1 a := Metric.mem_ball_self ha
  have hc2 : c2 ∈ Metric.ball c2 b := Metric.mem_ball_self hb
  have hcenter := hgap c1 hc1 c2 hc2
  have hqi : IntegrableOn (fun y : OQ7Prescribed.Position => (q : VectorL2) y) (Metric.ball c2 b) volume :=
    integrableOn_Lp_of_measure_ne_top (q : VectorL2) (by norm_num) (ball_measure_ne_top c2 b)
  have hi := integrand_integrable measurableSet_ball (ball_measure_ne_top c2 b) hd hgap (q : VectorL2) c1 hc1
  have hc := (newtonHessianOperator (c1 - c2)).integrable_comp hqi
  have he : (∫ y in Metric.ball c2 b, newtonHessianOperator (c1 - y) ((q : VectorL2) y)) =
      ∫ y in Metric.ball c2 b, (newtonHessianOperator (c1 - y) - newtonHessianOperator (c1 - c2)) ((q : VectorL2) y) := by
    have hz : ∫ y in Metric.ball c2 b, (q : VectorL2) y = 0 := hzero
    have hconst := (newtonHessianOperator (c1 - c2)).integral_comp_comm hqi
    rw [hz, map_zero] at hconst
    simp_rw [sub_apply]
    rw [integral_sub hi hc, hconst, sub_zero]
  have hwi : IntegrableOn (fun y : OQ7Prescribed.Position => ‖y - c2‖ * ‖(q : VectorL2) y‖)
      (Metric.ball c2 b) volume := by
    have hm : AEStronglyMeasurable (fun y : OQ7Prescribed.Position => ‖y - c2‖)
        (volume.restrict (Metric.ball c2 b)) := (continuous_id.sub continuous_const).norm.aestronglyMeasurable
    apply hqi.norm.bdd_mul hm
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hn : ‖y - c2‖ < b := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hn.le
  have hnorm : ‖∫ y in Metric.ball c2 b,
      (newtonHessianOperator (c1 - y) - newtonHessianOperator (c1 - c2)) ((q : VectorL2) y)‖ ≤
      (6 / (Real.pi * d ^ 4)) * ∫ y in Metric.ball c2 b, ‖y - c2‖ * ‖(q : VectorL2) y‖ := by
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hi.sub hc).norm (hwi.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hdiff := newtonHessianOperator_difference (c1 - y) (c1 - c2) hd (hgap c1 hc1 y hy) hcenter
    have hdist : ‖(c1 - y) - (c1 - c2)‖ = ‖y - c2‖ := by
      have heq : (c1 - y) - (c1 - c2) = -(y - c2) := by abel
      rw [heq, norm_neg]
    rw [hdist] at hdiff
    exact (((newtonHessianOperator (c1 - y) - newtonHessianOperator (c1 - c2)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))).trans_eq (by ring)
  rw [cross_moment c1 c2 ha hb hd hsep hgap, he, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by unfold ballVolume; positivity)]
  apply (mul_le_mul_of_nonneg_left hnorm (by unfold ballVolume; positivity)).trans_eq
  ring

end QuarticMaxwell.SphereCrossMoment

namespace QuarticMaxwell.SphereCrossMoment
open OQ7Prescribed StaticHessian SphereStatic SphereResponse StaticCrossIdentification
  SphereExterior SphereDoubleMean CrossBlockOperator MeasureTheory Set

theorem isolated_moment (c : OQ7Prescribed.Position) {a : ℝ} (ha : 0 < a) (χ : ℂ) (hχ : 0 < χ.im)
    (q : DomainL2 (Metric.ball c a)) :
    MomentOperator.map (Metric.ball c a) (ball_measure_ne_top c a) ((ballEquiv c a χ hχ).symm q) =
      beta χ • MomentOperator.map (Metric.ball c a) (ball_measure_ne_top c a) q := by
  rw [MomentOperator.full_integral _ measurableSet_ball, MomentOperator.full_integral _ measurableSet_ball]
  exact ball_inverse_mean c ha χ hχ q

theorem cross_constant_moment (c1 c2 : OQ7Prescribed.Position) {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖) (v : Vector) :
    MomentOperator.map (Metric.ball c1 a) (ball_measure_ne_top c1 a)
      (staticCrossBlock (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball (ballSource c2 b v)) =
      ((ballVolume a * ballVolume b : ℝ) : ℂ) • newtonHessianOperator (c1 - c2) v := by
  rw [cross_moment c1 c2 ha hb hd hsep hgap]
  have he : (∫ y in Metric.ball c2 b, newtonHessianOperator (c1 - y) ((ballSource c2 b v : VectorL2) y)) =
      ∫ y in Metric.ball c2 b, newtonHessianOperator (c1 - y) v := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ballSource_coe c2 b v), ae_restrict_mem measurableSet_ball] with y hy hm
    rw [hy, indicator_of_mem hm]
  rw [he]
  change (ballVolume a : ℂ) • SphereHessianMean.ballHessian c2 b v c1 = _
  rw [ball_mean c2 hb v c1 (by linarith), smul_smul]
  congr 1
  push_cast
  ring

theorem first_constant_cross_moment (c1 c2 : OQ7Prescribed.Position) {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖)
    (χ1 χ2 : ℂ) (hχ1 : 0 < χ1.im) (hχ2 : 0 < χ2.im) (v : Vector) :
    MomentOperator.map (Metric.ball c1 a) (ball_measure_ne_top c1 a)
      ((ballEquiv c1 a χ1 hχ1).symm
        (staticCrossBlock (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball
          ((ballEquiv c2 b χ2 hχ2).symm (ballSource c2 b v)))) =
      (beta χ1 * beta χ2 * ((ballVolume a * ballVolume b : ℝ) : ℂ)) •
        newtonHessianOperator (c1 - c2) v := by
  rw [isolated_moment c1 ha, ball_inverse_source c2 hb, map_smul, map_smul,
    cross_constant_moment c1 c2 ha hb hd hsep hgap, smul_smul, smul_smul]

end QuarticMaxwell.SphereCrossMoment
