import QuarticMaxwell.TwoSupportStatic
import QuarticMaxwell.BallAffineMoments
import QuarticMaxwell.MomentOperator

/-! Exact source restrictions and isolated-block integral moments. These use
the genuine arbitrary-input continuum ball mean identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QuarticMaxwell.BlockSourceMoments
open MeasureTheory Set OQ7Prescribed SourceTaylor SupportBlocks TwoSupportStatic

theorem union_finite (D E : Set Position) (hD : volume D ≠ ⊤) (hE : volume E ≠ ⊤) :
    volume (D ∪ E) ≠ ⊤ :=
  ne_of_lt ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hD.lt_top, hE.lt_top⟩))

theorem restriction_constantSource (D E : Set Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hfinD : volume D ≠ ⊤) (hfinE : volume E ≠ ⊤)
    (hsub : D ⊆ E) (e : Vector) :
    restriction D E hD (constantSource E hE hfinE e) = constantSource D hD hfinD e := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [restriction_coe D E hD (constantSource E hE hfinE e),
    constantSource_coe E hE hfinE e, constantSource_coe D hD hfinD e] with x hr he hd
  rw [hr, hd]
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx, he, indicator_of_mem (hsub hx), indicator_of_mem hx]
  · simp only [indicator_of_notMem hx]

theorem restriction_momentSource (D E : Set Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hfinD : volume D ≠ ⊤) (hfinE : volume E ≠ ⊤)
    (hsub : D ⊆ E) (n : UnitSphere) (e : Vector) (R : ℝ)
    (hR : E ⊆ Metric.closedBall (0 : Position) R) :
    restriction D E hD (momentSource E hE hfinE n e R hR) =
      momentSource D hD hfinD n e R (hsub.trans hR) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [restriction_coe D E hD (momentSource E hE hfinE n e R hR),
    momentSource_coe E hE hfinE n e R hR,
    momentSource_coe D hD hfinD n e R (hsub.trans hR)] with x hr he hd
  rw [hr, hd]
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx, he, indicator_of_mem (hsub hx), indicator_of_mem hx]
  · simp only [indicator_of_notMem hx]

theorem moment_constantSource (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) (e : Vector) :
    MomentOperator.map D hfin (constantSource D hD hfin e) = ((volume.real D : ℝ) : ℂ) • e := by
  rw [MomentOperator.map_apply]
  calc
    _ = ∫ x in D, e := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (constantSource_coe D hD hfin e), ae_restrict_mem hD] with x hx hmem
      rw [hx, indicator_of_mem hmem]
    _ = _ := by simp [Measure.real]

theorem moment_inclusion (D E : Set Position) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hfinD : volume D ≠ ⊤) (hfinE : volume E ≠ ⊤) (hsub : D ⊆ E) (p : DomainL2 D) :
    MomentOperator.map E hfinE (inclusion D E hsub p) = MomentOperator.map D hfinD p := by
  rw [MomentOperator.full_integral E hE, MomentOperator.full_integral D hD]
  rfl

theorem ball_inverse_moment (c : Position) (a : ℝ) (ha : 0 < a) (χ : ℂ) (hχ : 0 < χ.im)
    (f : DomainL2 (Metric.ball c a)) :
    MomentOperator.map (Metric.ball c a) (BallAffineMoments.ball_measure_ne_top c a)
      ((isolatedEquiv (Metric.ball c a) measurableSet_ball χ hχ).symm f) =
      SphereResponse.beta χ • MomentOperator.map (Metric.ball c a) (BallAffineMoments.ball_measure_ne_top c a) f := by
  rw [MomentOperator.full_integral _ measurableSet_ball, MomentOperator.full_integral _ measurableSet_ball]
  exact SphereResponse.ball_inverse_mean c ha χ hχ f

theorem moment_ball_affine (c : Position) (a : ℝ) (n : UnitSphere) (e : Vector)
    (R : ℝ) (hsub : Metric.ball c a ⊆ Metric.closedBall (0 : Position) R) :
    MomentOperator.map (Metric.ball c a) (BallAffineMoments.ball_measure_ne_top c a)
      (momentSource (Metric.ball c a) measurableSet_ball (BallAffineMoments.ball_measure_ne_top c a) n e R hsub) =
        (((inner ℝ (n : Position) c * volume.real (Metric.ball c a) : ℝ) : ℂ)) • e := by
  rw [BallAffineMoments.affineSource_decomposition, map_add, map_smul,
    moment_constantSource, MomentOperator.full_integral _ measurableSet_ball,
    BallAffineMoments.oddSource_integral, add_zero, smul_smul]
  push_cast
  rfl

section Blocks
variable (c1 c2 : Position) (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (P : ScalarPair)

def joined : Set Position := Metric.ball c1 a1 ∪ Metric.ball c2 a2

theorem joined_finite : volume (joined c1 c2 a1 a2) ≠ ⊤ :=
  union_finite _ _ (BallAffineMoments.ball_measure_ne_top c1 a1) (BallAffineMoments.ball_measure_ne_top c2 a2)

include ha1 ha2 in
theorem moment_blockInverse (f : DomainL2 (joined c1 c2 a1 a2)) :
    MomentOperator.map (joined c1 c2 a1 a2) (joined_finite c1 c2 a1 a2)
      (blockInverse (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball measurableSet_ball P f) =
      SphereResponse.beta P.left •
        MomentOperator.map (Metric.ball c1 a1) (BallAffineMoments.ball_measure_ne_top c1 a1)
          (projectLeft (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball f) +
      SphereResponse.beta P.right •
        MomentOperator.map (Metric.ball c2 a2) (BallAffineMoments.ball_measure_ne_top c2 a2)
          (projectRight (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball f) := by
  dsimp only [joined] at f ⊢
  unfold blockInverse SupportBlocks.diagonal
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
  simp only [injectLeft, injectRight]
  rw [moment_inclusion _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (BallAffineMoments.ball_measure_ne_top c1 a1) (joined_finite c1 c2 a1 a2) subset_union_left,
    moment_inclusion _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (BallAffineMoments.ball_measure_ne_top c2 a2) (joined_finite c1 c2 a1 a2) subset_union_right]
  exact congrArg₂ (fun u v : Vector => u + v)
    (ball_inverse_moment c1 a1 ha1 P.left P.left_loss
      (projectLeft (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball f))
    (ball_inverse_moment c2 a2 ha2 P.right P.right_loss
      (projectRight (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball f))

include ha1 ha2 in
theorem moment_blockInverse_constant (e : Vector) :
    MomentOperator.map (joined c1 c2 a1 a2) (joined_finite c1 c2 a1 a2)
      (blockInverse (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball measurableSet_ball P
        (constantSource (joined c1 c2 a1 a2) (measurableSet_ball.union measurableSet_ball)
          (joined_finite c1 c2 a1 a2) e)) =
      (SphereResponse.beta P.left * ((volume.real (Metric.ball c1 a1) : ℝ) : ℂ) +
        SphereResponse.beta P.right * ((volume.real (Metric.ball c2 a2) : ℝ) : ℂ)) • e := by
  rw [moment_blockInverse c1 c2 a1 a2 ha1 ha2 P]
  dsimp only [projectLeft, projectRight, joined]
  rw [restriction_constantSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (BallAffineMoments.ball_measure_ne_top c1 a1) _ subset_union_left,
    restriction_constantSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (BallAffineMoments.ball_measure_ne_top c2 a2) _ subset_union_right,
    moment_constantSource, moment_constantSource, smul_smul, smul_smul, ← add_smul]

include ha1 ha2 in
theorem moment_blockInverse_affine (n : UnitSphere) (e : Vector) (R : ℝ)
    (hsub : joined c1 c2 a1 a2 ⊆ Metric.closedBall (0 : Position) R) :
    MomentOperator.map (joined c1 c2 a1 a2) (joined_finite c1 c2 a1 a2)
      (blockInverse (Metric.ball c1 a1) (Metric.ball c2 a2) measurableSet_ball measurableSet_ball P
        (momentSource (joined c1 c2 a1 a2) (measurableSet_ball.union measurableSet_ball)
          (joined_finite c1 c2 a1 a2) n e R hsub)) =
      (SphereResponse.beta P.left * (((inner ℝ (n : Position) c1 * volume.real (Metric.ball c1 a1) : ℝ) : ℂ)) +
        SphereResponse.beta P.right * (((inner ℝ (n : Position) c2 * volume.real (Metric.ball c2 a2) : ℝ) : ℂ))) • e := by
  rw [moment_blockInverse c1 c2 a1 a2 ha1 ha2 P]
  dsimp only [joined] at hsub
  dsimp only [projectLeft, projectRight, joined]
  rw [restriction_momentSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (BallAffineMoments.ball_measure_ne_top c1 a1) _ subset_union_left,
    restriction_momentSource _ _ measurableSet_ball (measurableSet_ball.union measurableSet_ball)
      (BallAffineMoments.ball_measure_ne_top c2 a2) _ subset_union_right,
    moment_ball_affine, moment_ball_affine, smul_smul, smul_smul, ← add_smul]

end Blocks
end QuarticMaxwell.BlockSourceMoments
