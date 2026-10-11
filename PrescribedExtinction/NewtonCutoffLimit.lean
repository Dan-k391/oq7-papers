import PrescribedExtinction.NewtonCutoff

/-! Dominated convergence of radial cutoffs to the actual exterior-domain
integral, at a fixed positive puncture radius. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter Metric
open scoped Topology

theorem exteriorCutoff_tendsto (r : ℝ) (x : Position) :
    Tendsto (fun t => exteriorCutoff r t x) (𝓝[>] (0 : ℝ))
      (𝓝 (if r < ‖x‖ then (1 : ℝ) else 0)) := by
  by_cases hx : r < ‖x‖
  · simp only [hx, ite_true]
    have he : (fun t => exteriorCutoff r t x) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_inf_of_left (Iio_mem_nhds (sub_pos.mpr hx))] with t ht hsmall
      change t < ‖x‖ - r at hsmall
      exact exteriorCutoff_one ht x (by linarith)
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  · simp only [hx, ite_false]
    have he : (fun t => exteriorCutoff r t x) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact exteriorCutoff_zero ht x (le_of_not_gt hx)
    exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem exteriorCutoff_integral_tendsto (r : ℝ) (f : Position → ℝ)
    (hf : AEStronglyMeasurable f volume)
    (hfi : IntegrableOn f {x : Position | r < ‖x‖} volume) :
    Tendsto (fun t => ∫ x, exteriorCutoff r t x * f x) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in {x : Position | r < ‖x‖}, f x)) := by
  classical
  let s : Set Position := {x | r < ‖x‖}
  have hs : MeasurableSet s := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hi : Integrable (s.indicator f) volume := (integrable_indicator_iff hs).mpr hfi
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ)) (F := fun t x => exteriorCutoff r t x * f x)
    (f := s.indicator f) (fun x => ‖s.indicator f x‖) ?_ ?_ hi.norm ?_
  · simpa only [integral_indicator hs] using h
  · filter_upwards with t
    have hc : Continuous (exteriorCutoff r t) :=
      Real.smoothTransition.continuous.comp ((continuous_norm.sub continuous_const).div_const t)
    exact hc.aestronglyMeasurable.mul hf
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx, norm_mul, Real.norm_of_nonneg (exteriorCutoff_nonneg r t x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (exteriorCutoff_le_one r t x)
      · have hx' : ‖x‖ ≤ r := le_of_not_gt hx
        rw [exteriorCutoff_zero ht x hx', zero_mul, norm_zero, indicator_of_notMem hx, norm_zero]
  · exact ae_of_all _ fun x => by
      have hx := (exteriorCutoff_tendsto r x).mul_const (f x)
      simpa only [s, indicator_apply, mem_ofPred_eq, ite_mul, one_mul, zero_mul] using hx

theorem integrable_polar_actual (f : Position → ℝ) (hf : Integrable f volume) :
    Integrable (fun p : UnitSphere × Ioi (0 : ℝ) => f (p.2.1 • (p.1 : Position)))
      (sphereArea.prod (Measure.volumeIoiPow 2)) := by
  have hs : Integrable (fun x : ({(0 : Position)}ᶜ : Set Position) => f x)
      ((volume : Measure Position).comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (by measurability)).mp hf.integrableOn
  have h := ((volume : Measure Position).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd Position))
    (g := fun p => f (((homeomorphUnitSphereProd Position).symm p : ({(0 : Position)}ᶜ : Set Position)) : Position))).mp
      (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hs)
  simpa [sphereArea, Position, homeomorphUnitSphereProd_symm_apply_coe] using h

theorem integral_polar_iterated_actual (f : Position → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ s in Ioi (0 : ℝ), s ^ 2 *
      (∫ n : UnitSphere, f (s • (n : Position)) ∂sphereArea) := by
  rw [integral_polar_actual, integral_prod_symm _ (integrable_polar_actual f hf)]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const 2 |>.real_toNNReal)]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun s : ℝ => Real.toNNReal (s ^ 2) • ∫ n : UnitSphere, f (s • (n : Position)) ∂sphereArea)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg s), smul_eq_mul]

end OQ7Prescribed
