import QuarticMaxwell.SphereCrossMoment
import QuarticMaxwell.BlockSourceMoments
import QuarticMaxwell.TwoSupportBounds

/-! Exact first-interaction moments of finite scalar spheres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace QuarticMaxwell.BlockInteractionMoments
open OQ7Prescribed SourceTaylor SphereStatic SphereResponse SphereExterior SphereDoubleMean
  SphereCrossMoment BlockSourceMoments TwoSupportStatic TwoSupportBounds SupportBlocks StaticCrossIdentification
  MeasureTheory Set

theorem constantSource_ball_eq (c : OQ7Prescribed.Position) (a : ℝ) (v : Vector) :
    constantSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) v = ballSource c a v := by
  apply Subtype.ext
  apply Lp.ext
  exact (constantSource_coe _ measurableSet_ball _ v).trans (ballSource_coe c a v).symm

theorem isolated_inverse_constant (c : OQ7Prescribed.Position) (a : ℝ) (ha : 0 < a)
    (χ : ℂ) (hχ : 0 < χ.im) (v : Vector) :
    (isolatedEquiv (Metric.ball c a) measurableSet_ball χ hχ).symm
      (constantSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) v) =
        beta χ • constantSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) v := by
  rw [constantSource_ball_eq]
  exact ball_inverse_source c ha χ hχ v

theorem first_constant_moment (c1 c2 : OQ7Prescribed.Position) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (d : ℝ) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖)
    (P : ScalarPair) (v : Vector) :
    MomentOperator.map (joined c1 c2 a b) (joined_finite c1 c2 a b)
      (blockInverse (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball P
        (interaction (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball
          (blockInverse (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball P
            (constantSource (joined c1 c2 a b) (measurableSet_ball.union measurableSet_ball)
              (joined_finite c1 c2 a b) v)))) =
      (2 * beta P.left * beta P.right * ((ballVolume a * ballVolume b : ℝ) : ℂ)) •
        StaticHessian.newtonHessianOperator (c1 - c2) v := by
  have hdis := gap_disjoint (Metric.ball c1 a) (Metric.ball c2 b) hd hgap
  rw [moment_blockInverse c1 c2 a b ha hb P]
  rw [interaction, projectLeft_offDiagonal _ _ measurableSet_ball measurableSet_ball hdis,
    projectRight_offDiagonal _ _ measurableSet_ball measurableSet_ball hdis]
  rw [blockInverse, projectRight_diagonal _ _ measurableSet_ball measurableSet_ball hdis,
    projectLeft_diagonal _ _ measurableSet_ball measurableSet_ball hdis]
  change beta P.left • MomentOperator.map _ _
      (staticCrossBlock _ _ measurableSet_ball
        ((isolatedEquiv (Metric.ball c2 b) measurableSet_ball P.right P.right_loss).symm
          (restriction (Metric.ball c2 b) (joined c1 c2 a b) measurableSet_ball
            (constantSource (joined c1 c2 a b) (measurableSet_ball.union measurableSet_ball) (joined_finite c1 c2 a b) v)))) +
    beta P.right • MomentOperator.map _ _
      (staticCrossBlock _ _ measurableSet_ball
        ((isolatedEquiv (Metric.ball c1 a) measurableSet_ball P.left P.left_loss).symm
          (restriction (Metric.ball c1 a) (joined c1 c2 a b) measurableSet_ball
            (constantSource (joined c1 c2 a b) (measurableSet_ball.union measurableSet_ball) (joined_finite c1 c2 a b) v)))) = _
  dsimp only [joined]
  rw [restriction_constantSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (ball_measure_ne_top c2 b) _ subset_union_right,
    restriction_constantSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (ball_measure_ne_top c1 a) _ subset_union_left,
    isolated_inverse_constant c2 b hb, isolated_inverse_constant c1 a ha,
    map_smul, map_smul, map_smul, map_smul, constantSource_ball_eq, constantSource_ball_eq]
  have hrev : ∀ x ∈ Metric.ball c2 b, ∀ y ∈ Metric.ball c1 a, d ≤ ‖x - y‖ := by
    intro x hx y hy
    simpa only [norm_sub_rev] using hgap y hy x hx
  rw [cross_constant_moment c1 c2 ha hb hd hsep hgap,
    cross_constant_moment c2 c1 hb ha hd (by rw [norm_sub_rev]; linarith) hrev]
  have heven : StaticHessian.newtonHessianOperator (c2 - c1) = StaticHessian.newtonHessianOperator (c1 - c2) := by
    rw [← hessian_even (c1 - c2), neg_sub]
  rw [heven, smul_smul, smul_smul, smul_smul, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

end QuarticMaxwell.BlockInteractionMoments

namespace QuarticMaxwell.BlockInteractionMoments
open OQ7Prescribed SourceTaylor SphereStatic SphereResponse SphereExterior SphereDoubleMean
  SphereCrossMoment BlockSourceMoments TwoSupportStatic TwoSupportBounds SupportBlocks StaticCrossIdentification
  MeasureTheory Set

def oddResponse (c : OQ7Prescribed.Position) (a : ℝ) (χ : ℂ) (hχ : 0 < χ.im)
    (n : OQ7Prescribed.Position) (e : Vector) : DomainL2 (Metric.ball c a) :=
  (isolatedEquiv (Metric.ball c a) measurableSet_ball χ hχ).symm (BallAffineMoments.oddSource c a n e)

theorem oddResponse_mean_zero (c : OQ7Prescribed.Position) (a : ℝ) (ha : 0 < a)
    (χ : ℂ) (hχ : 0 < χ.im) (n : OQ7Prescribed.Position) (e : Vector) :
    MomentOperator.map (Metric.ball c a) (ball_measure_ne_top c a) (oddResponse c a χ hχ n e) = 0 := by
  rw [oddResponse, ball_inverse_moment c a ha χ hχ, MomentOperator.full_integral _ measurableSet_ball,
    BallAffineMoments.oddSource_integral, smul_zero]

theorem homogeneous_isolated_norm (c : OQ7Prescribed.Position) (a : ℝ) (μ : ℝ) (hμ : 0 < μ) :
    ‖(isolatedEquiv (Metric.ball c a) measurableSet_ball (Complex.I * (μ : ℂ))
      (by simpa using hμ)).symm.toContinuousLinearMap‖ ≤ μ := by
  have h := isolatedEquiv_inverse_norm_le (Metric.ball c a) measurableSet_ball (Complex.I * (μ : ℂ))
    (by simpa using hμ)
  have he : ‖Complex.I * (μ : ℂ)‖ ^ 2 / (Complex.I * (μ : ℂ)).im = μ := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ,
      one_mul, Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
      Complex.I_im, Complex.ofReal_re, zero_add]
    field_simp
  rw [he] at h
  exact h

theorem homogeneous_odd_weight (c : OQ7Prescribed.Position) (a : ℝ) (ha : 0 < a)
    (μ : ℝ) (hμ : 0 < μ) (n : OQ7Prescribed.Position) (hn : ‖n‖ = 1) (e : Vector) (he : ‖e‖ = 1) :
    (∫ x in Metric.ball c a, ‖x - c‖ *
      ‖(oddResponse c a (Complex.I * (μ : ℂ)) (by simpa using hμ) n e : VectorL2) x‖) ≤
        μ * (Real.sqrt 3 / 5) * a ^ 2 * volume.real (Metric.ball c a) := by
  have hnorm := BallAffineMoments.oddResponse_norm c a ha n e
    (isolatedEquiv (Metric.ball c a) measurableSet_ball (Complex.I * (μ : ℂ))
      (by simpa using hμ)).symm.toContinuousLinearMap (homogeneous_isolated_norm c a μ hμ)
  rw [hn, he, mul_one, mul_one] at hnorm
  apply BallAffineMoments.weighted_current_from_norm_bound c a ha _ hμ.le
  simpa only [oddResponse, ContinuousLinearEquiv.coe_coe, mul_assoc] using hnorm

end QuarticMaxwell.BlockInteractionMoments

namespace QuarticMaxwell.BlockInteractionMoments
open OQ7Prescribed SourceTaylor SphereStatic SphereResponse SphereExterior SphereDoubleMean
  SphereCrossMoment BlockSourceMoments TwoSupportStatic TwoSupportBounds SupportBlocks StaticCrossIdentification
  MeasureTheory Set

theorem first_odd_cross_norm (c1 c2 : OQ7Prescribed.Position) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (d : ℝ) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (n : OQ7Prescribed.Position) (hn : ‖n‖ = 1) (e : Vector) (he : ‖e‖ = 1) :
    ‖MomentOperator.map (Metric.ball c1 a) (ball_measure_ne_top c1 a)
      ((isolatedEquiv (Metric.ball c1 a) measurableSet_ball (Complex.I * (μ : ℂ)) (by simpa using hμ)).symm
        (staticCrossBlock (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball
          (oddResponse c2 b (Complex.I * (μ : ℂ)) (by simpa using hμ) n e)))‖ ≤
      (6 * Real.sqrt 3 / (5 * Real.pi * d ^ 4)) * ‖beta (Complex.I * (μ : ℂ))‖ * μ * b ^ 2 *
        volume.real (Metric.ball c1 a) * volume.real (Metric.ball c2 b) := by
  rw [ball_inverse_moment c1 a ha, norm_smul]
  have hc := cross_zero_mean_bound c1 c2 ha hb hd hsep hgap
    (oddResponse c2 b (Complex.I * (μ : ℂ)) (by simpa using hμ) n e)
    (oddResponse_mean_zero c2 b hb _ (by simpa using hμ) n e)
  have hw := homogeneous_odd_weight c2 b hb μ hμ n hn e he
  have hV : ballVolume a = volume.real (Metric.ball c1 a) := ballVolume_eq_measure c1 a ha.le
  rw [hV] at hc
  calc
    _ ≤ ‖beta (Complex.I * (μ : ℂ))‖ * (volume.real (Metric.ball c1 a) * (6 / (Real.pi * d ^ 4)) *
      (μ * (Real.sqrt 3 / 5) * b ^ 2 * volume.real (Metric.ball c2 b))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply hc.trans
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

end QuarticMaxwell.BlockInteractionMoments

namespace QuarticMaxwell.BlockInteractionMoments
open OQ7Prescribed SourceTaylor SphereStatic SphereResponse SphereExterior SphereDoubleMean
  SphereCrossMoment BlockSourceMoments TwoSupportStatic TwoSupportBounds SupportBlocks StaticCrossIdentification
  MeasureTheory Set

theorem isolated_inverse_affine (c : OQ7Prescribed.Position) (a : ℝ) (ha : 0 < a)
    (χ : ℂ) (hχ : 0 < χ.im) (n : UnitSphere) (v : Vector) (R : ℝ)
    (hsub : Metric.ball c a ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R) :
    (isolatedEquiv (Metric.ball c a) measurableSet_ball χ hχ).symm
      (momentSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) n v R hsub) =
      (((inner ℝ (n : OQ7Prescribed.Position) c : ℝ) : ℂ) * beta χ) •
        constantSource (Metric.ball c a) measurableSet_ball (ball_measure_ne_top c a) v +
      oddResponse c a χ hχ (n : OQ7Prescribed.Position) v := by
  rw [BallAffineMoments.affineSource_decomposition, map_add, map_smul,
    isolated_inverse_constant c a ha, smul_smul]
  rfl

set_option maxHeartbeats 5000000 in
theorem first_affine_moment (c1 c2 : OQ7Prescribed.Position) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (d : ℝ) (hd : 0 < d) (hsep : a + b < ‖c1 - c2‖)
    (hgap : ∀ x ∈ Metric.ball c1 a, ∀ y ∈ Metric.ball c2 b, d ≤ ‖x - y‖)
    (P : ScalarPair) (n : UnitSphere) (v : Vector) (R : ℝ)
    (hsub : joined c1 c2 a b ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R) :
    MomentOperator.map (joined c1 c2 a b) (joined_finite c1 c2 a b)
      (blockInverse (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball P
        (interaction (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball
          (blockInverse (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball measurableSet_ball P
            (momentSource (joined c1 c2 a b) (measurableSet_ball.union measurableSet_ball)
              (joined_finite c1 c2 a b) n v R hsub)))) =
      (beta P.left * beta P.right * (((inner ℝ (n : OQ7Prescribed.Position) c1 +
        inner ℝ (n : OQ7Prescribed.Position) c2) * ballVolume a * ballVolume b : ℝ) : ℂ)) •
          StaticHessian.newtonHessianOperator (c1 - c2) v +
      beta P.left • MomentOperator.map (Metric.ball c1 a) (ball_measure_ne_top c1 a)
        (staticCrossBlock (Metric.ball c1 a) (Metric.ball c2 b) measurableSet_ball
          (oddResponse c2 b P.right P.right_loss (n : OQ7Prescribed.Position) v)) +
      beta P.right • MomentOperator.map (Metric.ball c2 b) (ball_measure_ne_top c2 b)
        (staticCrossBlock (Metric.ball c2 b) (Metric.ball c1 a) measurableSet_ball
          (oddResponse c1 a P.left P.left_loss (n : OQ7Prescribed.Position) v)) := by
  have hdis := gap_disjoint (Metric.ball c1 a) (Metric.ball c2 b) hd hgap
  rw [moment_blockInverse c1 c2 a b ha hb P]
  rw [interaction, projectLeft_offDiagonal _ _ measurableSet_ball measurableSet_ball hdis,
    projectRight_offDiagonal _ _ measurableSet_ball measurableSet_ball hdis]
  rw [blockInverse, projectRight_diagonal _ _ measurableSet_ball measurableSet_ball hdis,
    projectLeft_diagonal _ _ measurableSet_ball measurableSet_ball hdis]
  change beta P.left • MomentOperator.map _ _
      (staticCrossBlock _ _ measurableSet_ball
        ((isolatedEquiv (Metric.ball c2 b) measurableSet_ball P.right P.right_loss).symm
          (restriction (Metric.ball c2 b) (joined c1 c2 a b) measurableSet_ball
            (momentSource (joined c1 c2 a b) (measurableSet_ball.union measurableSet_ball)
              (joined_finite c1 c2 a b) n v R hsub)))) +
    beta P.right • MomentOperator.map _ _
      (staticCrossBlock _ _ measurableSet_ball
        ((isolatedEquiv (Metric.ball c1 a) measurableSet_ball P.left P.left_loss).symm
          (restriction (Metric.ball c1 a) (joined c1 c2 a b) measurableSet_ball
            (momentSource (joined c1 c2 a b) (measurableSet_ball.union measurableSet_ball)
              (joined_finite c1 c2 a b) n v R hsub)))) = _
  dsimp only [joined] at hsub ⊢
  rw [restriction_momentSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (ball_measure_ne_top c2 b) _ subset_union_right,
    restriction_momentSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (ball_measure_ne_top c1 a) _ subset_union_left,
    isolated_inverse_affine c2 b hb, isolated_inverse_affine c1 a ha]
  simp only [map_add, map_smul]
  rw [constantSource_ball_eq, constantSource_ball_eq]
  have hrev : ∀ x ∈ Metric.ball c2 b, ∀ y ∈ Metric.ball c1 a, d ≤ ‖x - y‖ := by
    intro x hx y hy
    simpa only [norm_sub_rev] using hgap y hy x hx
  rw [cross_constant_moment c1 c2 ha hb hd hsep hgap,
    cross_constant_moment c2 c1 hb ha hd (by rw [norm_sub_rev]; linarith) hrev]
  have heven : StaticHessian.newtonHessianOperator (c2 - c1) = StaticHessian.newtonHessianOperator (c1 - c2) := by
    rw [← hessian_even (c1 - c2), neg_sub]
  rw [heven]
  simp only [smul_add, smul_smul, Complex.ofReal_mul, Complex.ofReal_add]
  module

end QuarticMaxwell.BlockInteractionMoments
