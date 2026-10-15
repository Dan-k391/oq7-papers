import PrescribedExtinction.NewtonPV

/-! The spherical principal value of the actual Newton Hessian kernel. The
distributional integration-by-parts identity remains a separate obligation. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Metric Filter Function
open scoped Topology NNReal

def newtonCompensated (φ : ScalarTest) (i j : Fin 3) (x : Position) : ℝ :=
  newtonHessianKernel i j x *
    (φ x - (closedBall (0 : Position) 1).indicator (fun _ => φ 0) x)

theorem newtonCompensated_measurable (φ : ScalarTest) (i j : Fin 3) :
    Measurable (newtonCompensated φ i j) := by
  unfold newtonCompensated
  exact (newtonHessianKernel_measurable i j).mul (φ.continuous.measurable.sub
    (measurable_const.indicator isClosed_closedBall.measurableSet))

theorem newtonCompensated_bound (φ : ScalarTest) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖newtonCompensated φ i j x‖ ≤ C * ‖x‖⁻¹ ^ 2 := by
  obtain ⟨L, hL⟩ := scalarTest_global_lipschitz φ
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  have hd (x : Position) :
      ‖φ x - (closedBall (0 : Position) 1).indicator (fun _ => φ 0) x‖ ≤
        ((L : ℝ) + M) * ‖x‖ := by
    by_cases hx : x ∈ closedBall (0 : Position) 1
    · simp only [indicator_of_mem hx]
      apply (hL.norm_sub_le x 0).trans
      simp only [sub_zero]
      gcongr
      exact le_add_of_nonneg_right hM0
    · simp only [indicator_of_notMem hx, sub_zero]
      have hr : 1 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
      apply (hM x).trans
      nlinarith [L.coe_nonneg]
  refine ⟨Real.pi⁻¹ * ((L : ℝ) + M), by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    simp [newtonCompensated, newtonHessianKernel]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    _ = ‖newtonHessianKernel i j x‖ *
        ‖φ x - (closedBall (0 : Position) 1).indicator (fun _ => φ 0) x‖ := norm_mul _ _
    _ ≤ (Real.pi⁻¹ * ‖x‖⁻¹ ^ 3) * (((L : ℝ) + M) * ‖x‖) :=
      mul_le_mul (newtonHessianKernel_norm_le i j x) (hd x) (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem newtonCompensated_integrable (φ : ScalarTest) (i j : Fin 3) :
    Integrable (newtonCompensated φ i j) volume := by
  obtain ⟨C, hC, hbound⟩ := newtonCompensated_bound φ i j
  have hloc : LocallyIntegrable (newtonCompensated φ i j) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := C) (α := 2)
      (by norm_num [Position, finrank_euclideanSpace_fin])
      (by norm_num [Position, finrank_euclideanSpace_fin])
      ?_ (newtonCompensated_measurable φ i j).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa using hbound x
  have hs : support (newtonCompensated φ i j) ⊆ tsupport φ ∪ closedBall 0 1 := by
    intro x hx
    by_contra hn
    simp only [mem_union, not_or] at hn
    have hz := image_eq_zero_of_notMem_tsupport hn.1
    exact hx (by simp [newtonCompensated, hz, hn.2])
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (hloc.integrableOn_isCompact (φ.hasCompactSupport.union (isCompact_closedBall _ _)))

def newtonAnnulus (i j : Fin 3) (r T : ℝ) : Position → ℝ :=
  {x : Position | r < ‖x‖ ∧ ‖x‖ ≤ T}.indicator (newtonHessianKernel i j)

theorem newtonAnnulus_measurableSet (r T : ℝ) :
    MeasurableSet {x : Position | r < ‖x‖ ∧ ‖x‖ ≤ T} :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet

theorem newtonAnnulus_integrable (i j : Fin 3) (r T : ℝ) (hr : 0 < r) :
    Integrable (newtonAnnulus i j r T) volume := by
  classical
  have hm : AEStronglyMeasurable (newtonAnnulus i j r T) volume := ((newtonHessianKernel_measurable i j).indicator
    (newtonAnnulus_measurableSet r T)).aestronglyMeasurable
  have hb (x : Position) : ‖newtonAnnulus i j r T x‖ ≤ Real.pi⁻¹ * r⁻¹ ^ 3 := by
    by_cases hx : r < ‖x‖ ∧ ‖x‖ ≤ T
    · unfold newtonAnnulus
      rw [indicator_of_mem (show x ∈ {x : Position | r < ‖x‖ ∧ ‖x‖ ≤ T} from hx)]
      apply (newtonHessianKernel_norm_le i j x).trans
      gcongr
      exact hx.1.le
    · simp [newtonAnnulus, hx]
      positivity
  have hs : support (newtonAnnulus i j r T) ⊆ closedBall 0 T := by
    intro x hx
    by_contra hn
    have ht : ¬‖x‖ ≤ T := by simpa only [mem_closedBall, dist_zero_right] using hn
    exact hx (by simp [newtonAnnulus, ht])
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (Measure.integrableOn_of_bounded (isCompact_closedBall (0 : Position) T).measure_lt_top.ne
      hm (ae_of_all _ hb))

theorem newtonAnnulus_integral_zero (i j : Fin 3) (r T : ℝ) :
    (∫ x, newtonAnnulus i j r T x) = 0 := by
  classical
  have h := newtonHessian_radial_integral_zero i j (fun s => if r < s ∧ s ≤ T then 1 else 0)
  convert h using 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : r < ‖x‖ ∧ ‖x‖ ≤ T <;> simp [newtonAnnulus, hx]

def newtonPVTruncated (φ : ScalarTest) (i j : Fin 3) (r : ℝ) : ℝ :=
  ∫ x in {x : Position | r < ‖x‖}, newtonHessianKernel i j x * φ x

def newtonPVValue (φ : ScalarTest) (i j : Fin 3) : ℝ := ∫ x, newtonCompensated φ i j x

theorem newtonPV_indicator_decomposition (φ : ScalarTest) (i j : Fin 3) (r : ℝ) :
    {x : Position | r < ‖x‖}.indicator (fun x => newtonHessianKernel i j x * φ x) =
      {x : Position | r < ‖x‖}.indicator (newtonCompensated φ i j) +
        (fun x => φ 0 * newtonAnnulus i j r 1 x) := by
  classical
  funext x
  by_cases hx : r < ‖x‖ <;> by_cases hb : ‖x‖ ≤ 1 <;>
    simp [newtonCompensated, newtonAnnulus, mem_closedBall, dist_zero_right, hx, hb]
  ring

theorem newtonPVTruncated_integrable (φ : ScalarTest) (i j : Fin 3) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x => newtonHessianKernel i j x * φ x) {x : Position | r < ‖x‖} volume := by
  have hm : MeasurableSet {x : Position | r < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integrable_indicator_iff hm, newtonPV_indicator_decomposition]
  exact ((newtonCompensated_integrable φ i j).indicator hm).add
    ((newtonAnnulus_integrable i j r 1 hr).const_mul (φ 0))

theorem newtonPVTruncated_eq_compensated (φ : ScalarTest) (i j : Fin 3) (r : ℝ) (hr : 0 < r) :
    newtonPVTruncated φ i j r = ∫ x in {x : Position | r < ‖x‖}, newtonCompensated φ i j x := by
  classical
  have hm : MeasurableSet {x : Position | r < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  unfold newtonPVTruncated
  rw [← integral_indicator hm, newtonPV_indicator_decomposition]
  simp only [Pi.add_apply]
  rw [integral_add
    ((newtonCompensated_integrable φ i j).indicator hm)
    ((newtonAnnulus_integrable i j r 1 hr).const_mul (φ 0)),
    integral_const_mul, newtonAnnulus_integral_zero, mul_zero, add_zero, integral_indicator hm]

theorem newton_compensated_cutoff_tendsto (φ : ScalarTest) (i j : Fin 3) :
    Tendsto (fun r : ℝ => ∫ x in {x : Position | r < ‖x‖}, newtonCompensated φ i j x)
      (𝓝 (0 : ℝ)) (𝓝 (newtonPVValue φ i j)) := by
  classical
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝 (0 : ℝ))
    (F := fun r => {x : Position | r < ‖x‖}.indicator (newtonCompensated φ i j))
    (f := newtonCompensated φ i j) (fun x => ‖newtonCompensated φ i j x‖)
    (Eventually.of_forall fun r => (newtonCompensated_measurable φ i j).aestronglyMeasurable.indicator
      (isOpen_lt continuous_const continuous_norm).measurableSet)
    (Eventually.of_forall fun _ => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
    (newtonCompensated_integrable φ i j).norm ?_
  · simpa only [integral_indicator (isOpen_lt continuous_const continuous_norm).measurableSet,
      newtonPVValue] using h
  · exact ae_of_all _ fun x => by
      by_cases hx : x = 0
      · subst x
        have hz : newtonCompensated φ i j 0 = 0 := by simp [newtonCompensated, newtonHessianKernel]
        simp only [indicator_apply, hz, ite_self]
        exact tendsto_const_nhds
      · have he : (fun r : ℝ => {x : Position | r < ‖x‖}.indicator (newtonCompensated φ i j) x)
            =ᶠ[𝓝 0] fun _ => newtonCompensated φ i j x := by
          filter_upwards [Iio_mem_nhds (norm_pos_iff.mpr hx)] with r hr
          exact indicator_of_mem (show x ∈ {x : Position | r < ‖x‖} from hr) _
        exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem newtonPrincipalValue_tendsto (φ : ScalarTest) (i j : Fin 3) :
    Tendsto (newtonPVTruncated φ i j) (𝓝[>] (0 : ℝ)) (𝓝 (newtonPVValue φ i j)) := by
  have he : newtonPVTruncated φ i j =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => ∫ x in {x : Position | r < ‖x‖}, newtonCompensated φ i j x) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact newtonPVTruncated_eq_compensated φ i j r hr
  exact (tendsto_congr' he).mpr ((newton_compensated_cutoff_tendsto φ i j).mono_left inf_le_left)

end OQ7Prescribed
