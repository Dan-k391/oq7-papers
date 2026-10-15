import QuarticMaxwell.SphereHessianMean

/-! The exact ball and double-ball mean, with the physical Fourier-field
identification proved before continuity upgrades the almost-everywhere result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell.SphereDoubleMean
open OQ7Prescribed SphereStatic SphereExterior SphereHessianMean StaticOffSupport StaticHessian MeasureTheory Set

theorem ball_mean (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) (x : Position)
    (hx : a < ‖x - c‖) :
    ballHessian c a v x = (ballVolume a : ℂ) • newtonHessianOperator (x - c) v := by
  let d := (‖x - c‖ - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let U : Set Position := {y | a + d < ‖y - c‖}
  have hU : IsOpen U := isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm)
  have hxU : x ∈ U := by change a + d < ‖x - c‖; dsimp [d]; linarith
  let p := ballPolarization c a ha.le v
  have hp : ∀ᵐ y ∂volume, y ∉ Metric.ball c a → p.current y = 0 := by
    filter_upwards [ballPolarization_current c a ha.le v] with y hy hnot
    simpa only [indicator_of_notMem hnot] using hy
  have hsep : ∀ y ∈ U, ∀ z ∈ Metric.ball c a, d ≤ ‖y - z‖ :=
    fun y hy z hz => ball_separation c a d hy hz
  have hi := staticFourier_vector_separated_ae p (Metric.ball c a) U hU hp hd hsep
  have hto : p.memLp.toLp p.current = (ballSource c a v : VectorL2) :=
    domainPolarization_toLp _ measurableSet_ball (by positivity) (ball_support_bound c a) _
  rw [hto] at hi
  have he : (ballHessian c a v) =ᵐ[volume.restrict U]
      (fun y => (ballVolume a : ℂ) • newtonHessianOperator (y - c) v) := by
    filter_upwards [ae_restrict_of_ae hi,
      ae_restrict_of_ae (staticFourier_ball_exterior_ae c ha v), ae_restrict_mem hU.measurableSet]
      with y hy hext hyU
    have hya : a < ‖y - c‖ := lt_trans (by linarith : a < a + d) hyU
    exact (vectorKernelField_ball c ha v hd y hyU).symm.trans ((hy hyU).symm.trans (hext hya))
  have hc : ContinuousOn (fun y : Position =>
      (ballVolume a : ℂ) • newtonHessianOperator (y - c) v) U := by
    intro y hy
    have hy' : a + d < ‖y - c‖ := hy
    have hy0 : y - c ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖y - c‖))
    have hH : ContinuousAt (fun z : Position => newtonHessianOperator (z - c)) y :=
      (hessian_continuousAt (y - c) hy0).comp (f := fun z : Position => z - c)
        (continuousAt_id.sub continuousAt_const)
    have hs : ContinuousAt (fun _ : Position => (ballVolume a : ℂ)) y := continuousAt_const
    have hv : ContinuousAt (fun z : Position => newtonHessianOperator (z - c) v) y :=
      (ContinuousLinearMap.apply ℂ Vector v).continuous.continuousAt.comp
        (f := fun z : Position => newtonHessianOperator (z - c)) hH
    exact (hs.smul hv).continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq he hU (ballHessian_continuousOn c a hd v) hc hxU

theorem hessian_even (r : Position) : newtonHessianOperator (-r) = newtonHessianOperator r := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  simp only [newtonHessianOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp only [newtonHessianKernel, norm_neg, PiLp.neg_apply]
  ring

theorem ball_mean_reverse (c : Position) {a : ℝ} (ha : 0 < a) (v : Vector) (x : Position)
    (hx : a < ‖x - c‖) :
    (∫ y in Metric.ball c a, newtonHessianOperator (y - x) v) =
      (ballVolume a : ℂ) • newtonHessianOperator (c - x) v := by
  have he (y : Position) : newtonHessianOperator (y - x) = newtonHessianOperator (x - y) := by
    rw [← hessian_even (x - y), neg_sub]
  simp_rw [he]
  exact ball_mean c ha v x hx

/-- Exact double-ball integral; no point-dipole approximation is assumed. -/
theorem double_ball_mean (c1 c2 : Position) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsep : a + b < ‖c1 - c2‖) (v : Vector) :
    (∫ x in Metric.ball c1 a, ∫ y in Metric.ball c2 b, newtonHessianOperator (x - y) v) =
      ((ballVolume a * ballVolume b : ℝ) : ℂ) • newtonHessianOperator (c1 - c2) v := by
  have hin (x : Position) (hx : x ∈ Metric.ball c1 a) : b < ‖x - c2‖ := by
    have hxa : ‖x - c1‖ < a := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn : ‖c1 - c2‖ ≤ ‖x - c1‖ + ‖x - c2‖ := by
      have h := norm_add_le (c1 - x) (x - c2)
      simpa only [sub_add_sub_cancel, norm_sub_rev] using h
    linarith
  have he : (∫ x in Metric.ball c1 a, ∫ y in Metric.ball c2 b, newtonHessianOperator (x - y) v) =
      ∫ x in Metric.ball c1 a, (ballVolume b : ℂ) • newtonHessianOperator (x - c2) v := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ball_mean c2 hb v x (hin x hx)
  rw [he, integral_smul]
  rw [ball_mean_reverse c1 ha v c2 (by rw [norm_sub_rev]; linarith)]
  rw [smul_smul]
  congr 1
  push_cast
  ring

end QuarticMaxwell.SphereDoubleMean
