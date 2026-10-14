import PrescribedExtinction.FarFieldCurrent
import PrescribedExtinction.OutgoingDissipativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Topology

def supportedCurrentL1Bound (R : ℝ) : ℝ :=
  ‖indicatorConstLp (μ := (volume : Measure Position)) 2
    Metric.isClosed_closedBall.measurableSet (isCompact_closedBall (0 : Position) R).measure_ne_top (1 : ℝ)‖

theorem supportedCurrent_integral_norm_le (R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    (∫ y : Position, ‖(supportedPolarization R hR f).current y‖) ≤
      supportedCurrentL1Bound R * ‖f‖ := by
  let p := supportedPolarization R hR f
  let g : Lp (α := Position) ℝ 2 volume := p.memLp.norm.toLp (fun y => ‖p.current y‖)
  let u : Lp (α := Position) ℝ 2 volume := indicatorConstLp 2
    Metric.isClosed_closedBall.measurableSet (isCompact_closedBall (0 : Position) R).measure_ne_top (1 : ℝ)
  have hg : ‖g‖ = ‖f‖ := by
    rw [Lp.norm_toLp]
    rw [eLpNorm_norm p.current p.memLp.aestronglyMeasurable]
    rw [← Lp.norm_toLp p.current p.memLp, supportedPolarization_toLp]
    rfl
  have hi : inner ℝ u g = ∫ y : Position, ‖p.current y‖ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure Position))
      (hs := Metric.isClosed_closedBall.measurableSet)
      (hμs := (isCompact_closedBall (0 : Position) R).measure_ne_top) (c := (1 : ℝ)),
      p.memLp.norm.coeFn_toLp] with y hu hg
    rw [hu, hg]
    by_cases hy : y ∈ Metric.closedBall (0 : Position) R
    · simp [indicator_of_mem hy, RCLike.inner_apply]
    · have hz : p.current y = 0 := p.vanish y (by
        change R < ‖y‖
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy)
      simp [indicator_of_notMem hy, hz]
  rw [← hi]
  apply (real_inner_le_norm u g).trans
  rw [hg]
  rfl

theorem compactCurrentFarField_congr_current (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : compactCurrentFarField k p = compactCurrentFarField k q := by
  funext n
  unfold compactCurrentFarField
  congr 2
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem compactCurrentFarField_add (k : ℝ) (p q : CompactPolarization) :
    compactCurrentFarField k (p.add q) = compactCurrentFarField k p + compactCurrentFarField k q := by
  funext n
  unfold compactCurrentFarField CompactPolarization.add
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (compactCurrent_phase_integrable k p n) (compactCurrent_phase_integrable k q n)]
  simp only [← transverseProjectionMap_apply, map_add, smul_add, Pi.add_apply]

theorem compactCurrentFarField_scale (k : ℝ) (p : CompactPolarization) (z : ℂ) :
    compactCurrentFarField k (p.scale z) = z • compactCurrentFarField k p := by
  funext n
  unfold compactCurrentFarField CompactPolarization.scale
  simp only [Pi.smul_apply, smul_comm (currentPlanePhase k n _) z]
  rw [integral_smul]
  simp only [← transverseProjectionMap_apply, map_smul, Pi.smul_apply]
  exact smul_comm _ _ _

def supportedFarFieldLinear (k R : ℝ) (hR : 0 ≤ R) (n : Position) : SupportedVectorL2 R →ₗ[ℂ] Vector where
  toFun f := compactCurrentFarField k (supportedPolarization R hR f) n
  map_add' f g := by
    rw [compactCurrentFarField_congr_current k _ _ (supportedPolarization_add_current_ae R hR f g),
      compactCurrentFarField_add]
    rfl
  map_smul' z f := by
    rw [compactCurrentFarField_congr_current k _ _ (supportedPolarization_smul_current_ae R hR z f),
      compactCurrentFarField_scale]
    rfl

theorem supportedFarFieldLinear_bound (k R : ℝ) (hR : 0 ≤ R) (n : Position) (hn : ‖n‖ = 1)
    (f : SupportedVectorL2 R) :
    ‖supportedFarFieldLinear k R hR n f‖ ≤
      ((k ^ 2 / (4 * Real.pi)) * supportedCurrentL1Bound R) * ‖f‖ := by
  apply (compactCurrentFarField_norm_le k (supportedPolarization R hR f) n hn).trans
  calc
    _ ≤ (k ^ 2 / (4 * Real.pi)) * (supportedCurrentL1Bound R * ‖f‖) :=
      mul_le_mul_of_nonneg_left (supportedCurrent_integral_norm_le R hR f) (by positivity)
    _ = _ := by ring

def supportedFarFieldMap (k R : ℝ) (hR : 0 ≤ R) (n : UnitSphere) : SupportedVectorL2 R →L[ℂ] Vector :=
  (supportedFarFieldLinear k R hR n).mkContinuous
    ((k ^ 2 / (4 * Real.pi)) * supportedCurrentL1Bound R)
      (supportedFarFieldLinear_bound k R hR n (unitSphere_norm n))

def supportedFarFieldPower (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) : ℝ :=
  ∫ n : UnitSphere, ‖compactCurrentFarField k (supportedPolarization R hR f) n‖ ^ 2 ∂sphereArea

theorem supportedFarFieldPower_continuous (k R : ℝ) (hR : 0 ≤ R) :
    Continuous (supportedFarFieldPower k R hR) := by
  apply continuous_iff_continuousAt.mpr
  intro f₀
  let C := (k ^ 2 / (4 * Real.pi)) * supportedCurrentL1Bound R
  have hC : 0 ≤ C := by dsimp [C, supportedCurrentL1Bound]; positivity
  apply continuousAt_of_dominated (bound := fun _ : UnitSphere => (C * (‖f₀‖ + 1)) ^ 2)
  · filter_upwards with f
    exact (((compactCurrentFarField_continuous k (supportedPolarization R hR f)).comp
      continuous_subtype_val).norm.pow 2).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds f₀ (by norm_num : (0 : ℝ) < 1)] with f hf
    have hn : ‖f‖ ≤ ‖f₀‖ + 1 := by
      have hdist : ‖f₀ - f‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hf
      exact (norm_le_norm_add_norm_sub f₀ f).trans (by linarith)
    apply ae_of_all
    intro n
    have hb := (supportedFarFieldLinear_bound k R hR n (unitSphere_norm n) f).trans
      (mul_le_mul_of_nonneg_left hn hC)
    change ‖‖compactCurrentFarField k (supportedPolarization R hR f) n‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  · exact integrable_const _
  · apply ae_of_all
    intro n
    change ContinuousAt (fun f : SupportedVectorL2 R => ‖supportedFarFieldMap k R hR n f‖ ^ 2) f₀
    exact (supportedFarFieldMap k R hR n).continuous.continuousAt.norm.pow 2

end OQ7Prescribed
