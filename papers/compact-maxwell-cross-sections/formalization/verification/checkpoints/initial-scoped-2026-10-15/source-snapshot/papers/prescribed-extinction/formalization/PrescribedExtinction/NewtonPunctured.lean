import PrescribedExtinction.NewtonShell

/-! The fixed-radius Newtonian integration-by-parts bridge. All test functions
are the original smooth compactly supported `ScalarTest` functions. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter Metric
open scoped Topology

theorem newtonHessianKernel_contDiffAt (i j : Fin 3) (x : Position) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (newtonHessianKernel i j) x := by
  have hi : ContDiffAt ℝ 1 (fun y : Position => y i) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : Position →L[ℝ] ℝ).contDiff.contDiffAt
  have hj : ContDiffAt ℝ 1 (fun y : Position => y j) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Position →L[ℝ] ℝ).contDiff.contDiffAt
  exact ((contDiffAt_const.mul hi |>.mul hj).sub
    ((contDiffAt_norm ℝ hx).pow 2 |>.mul contDiffAt_const)).div
    (contDiffAt_const.mul ((contDiffAt_norm ℝ hx).pow 5))
    (mul_ne_zero (by positivity) (pow_ne_zero 5 (norm_ne_zero_iff.mpr hx)))

theorem newton_cutoff_double_ibp (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (φ : ScalarTest) (i j : Fin 3) :
    (∫ x, exteriorCutoff r t x * newtonReal x * (testPartial j (testPartial i φ)) x) =
      (∫ x, exteriorCutoff r t x * newtonHessianKernel i j x * φ x) +
      (∫ x, exteriorCutoffPartial r t i x * newtonGradient j x * φ x) -
      (∫ x, exteriorCutoffPartial r t j x * newtonReal x * (testPartial i φ) x) := by
  have hD := exteriorCutoffPartial_mul_integrable r t hr ht j
    (fun x => newtonReal x * (testPartial i φ) x)
    (fun x hx => (newtonReal_contDiffAt x hx).continuousAt.mul (testPartial i φ).continuous.continuousAt)
  have hB := exteriorCutoffPartial_mul_integrable r t hr ht i
    (fun x => newtonGradient j x * φ x)
    (fun x hx => (newtonGradient_contDiffAt j x hx).continuousAt.mul φ.continuous.continuousAt)
  have hG := ((exteriorCutoff_mul_contDiff r t hr ht (newtonGradient j)
    (newtonGradient_contDiffAt j)).continuous.mul (testPartial i φ).continuous).integrable_of_hasCompactSupport (μ := volume)
      (testPartial i φ).hasCompactSupport.mul_left
  have hK := ((exteriorCutoff_mul_contDiff r t hr ht (newtonHessianKernel i j)
    (newtonHessianKernel_contDiffAt i j)).continuous.mul φ.continuous).integrable_of_hasCompactSupport (μ := volume)
      φ.hasCompactSupport.mul_left
  change Integrable (fun x => exteriorCutoff r t x * newtonGradient j x * (testPartial i φ) x) volume at hG
  change Integrable (fun x => exteriorCutoff r t x * newtonHessianKernel i j x * φ x) volume at hK
  have h1 := exteriorCutoff_newton_ibp r t hr ht (testPartial i φ) j
  have h2 := exteriorCutoff_gradient_ibp r t hr ht φ i j
  simp_rw [add_mul] at h1 h2
  have hD' : Integrable (fun x => exteriorCutoffPartial r t j x * newtonReal x * (testPartial i φ) x) volume := by
    simpa only [mul_assoc] using hD
  have hB' : Integrable (fun x => exteriorCutoffPartial r t i x * newtonGradient j x * φ x) volume := by
    simpa only [mul_assoc] using hB
  rw [integral_add hD' hG] at h1
  rw [integral_add hB' hK] at h2
  linarith

theorem newton_cutoff_contact_shell (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (φ : ScalarTest) (i j : Fin 3) :
    (∫ x, exteriorCutoffPartial r t i x * newtonGradient j x * φ x) =
      -(4 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..1, transitionDerivative u *
        (∫ n : UnitSphere, (n : Position) i * (n : Position) j *
          φ ((r + t * u) • (n : Position)) ∂sphereArea) := by
  have hf := exteriorCutoffPartial_mul_integrable r t hr ht i
    (fun x => newtonGradient j x * φ x)
    (fun x hx => (newtonGradient_contDiffAt j x hx).continuousAt.mul φ.continuous.continuousAt)
  rw [integral_polar_iterated_actual _ (by simpa only [mul_assoc] using hf)]
  have hp (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ 2 * (∫ n : UnitSphere,
        exteriorCutoffPartial r t i (s • (n : Position)) *
          newtonGradient j (s • (n : Position)) * φ (s • (n : Position)) ∂sphereArea) =
      (-(4 * Real.pi)⁻¹ * t⁻¹) * (transitionDerivative ((s - r) / t) *
        (∫ n : UnitSphere, (n : Position) i * (n : Position) j * φ (s • (n : Position)) ∂sphereArea)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun n => by
      simp only [exteriorCutoffPartial, newtonGradient, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show 0 < s from hs), unitSphere_norm, mul_one, PiLp.smul_apply, smul_eq_mul]
      field_simp [ne_of_gt (show 0 < s from hs)]
  rw [setIntegral_congr_fun measurableSet_Ioi hp, integral_const_mul,
    transition_radial_integral r t hr ht,
    mul_assoc, transition_radial_rescale r t ht]

theorem newton_cutoff_derivative_shell (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (φ : ScalarTest) (i j : Fin 3) :
    (∫ x, exteriorCutoffPartial r t j x * newtonReal x * (testPartial i φ) x) =
      (4 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..1, transitionDerivative u *
        ((r + t * u) * (∫ n : UnitSphere, (n : Position) j *
          (testPartial i φ) ((r + t * u) • (n : Position)) ∂sphereArea)) := by
  have hf := exteriorCutoffPartial_mul_integrable r t hr ht j
    (fun x => newtonReal x * (testPartial i φ) x)
    (fun x hx => (newtonReal_contDiffAt x hx).continuousAt.mul (testPartial i φ).continuous.continuousAt)
  rw [integral_polar_iterated_actual _ (by simpa only [mul_assoc] using hf)]
  have hp (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ 2 * (∫ n : UnitSphere,
        exteriorCutoffPartial r t j (s • (n : Position)) *
          newtonReal (s • (n : Position)) * (testPartial i φ) (s • (n : Position)) ∂sphereArea) =
      ((4 * Real.pi)⁻¹ * t⁻¹) * (transitionDerivative ((s - r) / t) *
        (s * (∫ n : UnitSphere, (n : Position) j * (testPartial i φ) (s • (n : Position)) ∂sphereArea))) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun n => by
      simp only [exteriorCutoffPartial, newtonReal, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show 0 < s from hs), unitSphere_norm, mul_one, PiLp.smul_apply, smul_eq_mul]
      field_simp [ne_of_gt (show 0 < s from hs)]
  rw [setIntegral_congr_fun measurableSet_Ioi hp, integral_const_mul,
    transition_radial_integral r t hr ht,
    mul_assoc, transition_radial_rescale r t ht]

theorem newton_cutoff_contact_shell_tendsto (r : ℝ) (hr : 0 < r)
    (φ : ScalarTest) (i j : Fin 3) :
    Tendsto (fun t => ∫ x, exteriorCutoffPartial r t i x * newtonGradient j x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (newtonContactBoundary φ i j r)) := by
  have h := (transition_average_tendsto r
    (fun s => ∫ n : UnitSphere, (n : Position) i * (n : Position) j * φ (s • (n : Position)) ∂sphereArea)
    (sphere_test_moment_continuous φ i j)).const_mul (-(4 * Real.pi)⁻¹)
  have he : (fun t => ∫ x, exteriorCutoffPartial r t i x * newtonGradient j x * φ x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => -(4 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..1, transitionDerivative u *
        (∫ n : UnitSphere, (n : Position) i * (n : Position) j *
          φ ((r + t * u) • (n : Position)) ∂sphereArea)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact newton_cutoff_contact_shell r t hr ht φ i j
  exact (tendsto_congr' he).mpr (h.mono_left inf_le_left)

theorem newton_cutoff_derivative_shell_tendsto (r : ℝ) (hr : 0 < r)
    (φ : ScalarTest) (i j : Fin 3) :
    Tendsto (fun t => ∫ x, exteriorCutoffPartial r t j x * newtonReal x * (testPartial i φ) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (-newtonDerivativeBoundary φ i j r)) := by
  have h := (transition_average_tendsto r
    (fun s => s * (∫ n : UnitSphere, (n : Position) j * (testPartial i φ) (s • (n : Position)) ∂sphereArea))
    (continuous_id.mul (sphere_test_derivative_continuous φ i j))).const_mul (4 * Real.pi)⁻¹
  have he : (fun t => ∫ x, exteriorCutoffPartial r t j x * newtonReal x * (testPartial i φ) x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => (4 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..1, transitionDerivative u *
        ((r + t * u) * (∫ n : UnitSphere, (n : Position) j *
          (testPartial i φ) ((r + t * u) • (n : Position)) ∂sphereArea))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact newton_cutoff_derivative_shell r t hr ht φ i j
  apply (tendsto_congr' he).mpr
  simpa only [newtonDerivativeBoundary, neg_div, neg_mul, neg_neg, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using h.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

theorem newtonReal_locallyIntegrable : LocallyIntegrable newtonReal volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi)⁻¹) (α := 1)
    (by norm_num [Position, finrank_euclideanSpace_fin])
    (by norm_num [Position, finrank_euclideanSpace_fin])
  · exact ae_of_all _ fun x => by
      simp [newtonReal, Real.rpow_neg_one, mul_inv_rev, mul_comm]
  · exact (show Measurable newtonReal by unfold newtonReal; fun_prop).aestronglyMeasurable

theorem newtonReal_test_integrable (φ : ScalarTest) :
    Integrable (fun x => newtonReal x * φ x) volume := by
  simpa only [smul_eq_mul] using newtonReal_locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    φ.continuous φ.hasCompactSupport

theorem newton_punctured_double_ibp (r : ℝ) (hr : 0 < r) (φ : ScalarTest) (i j : Fin 3) :
    (∫ x in {x : Position | r < ‖x‖}, newtonReal x * (testPartial j (testPartial i φ)) x) =
      newtonPVTruncated φ i j r + newtonContactBoundary φ i j r + newtonDerivativeBoundary φ i j r := by
  have hL := exteriorCutoff_integral_tendsto r
    (fun x => newtonReal x * (testPartial j (testPartial i φ)) x)
    (newtonReal_test_integrable (testPartial j (testPartial i φ))).aestronglyMeasurable
    (newtonReal_test_integrable (testPartial j (testPartial i φ))).integrableOn
  have hK := exteriorCutoff_integral_tendsto r (fun x => newtonHessianKernel i j x * φ x)
    ((newtonHessianKernel_measurable i j).mul φ.continuous.measurable).aestronglyMeasurable
    (newtonPVTruncated_integrable φ i j r hr)
  have hR := (hK.add (newton_cutoff_contact_shell_tendsto r hr φ i j)).sub
    (newton_cutoff_derivative_shell_tendsto r hr φ i j)
  have he : (fun t => ∫ x, exteriorCutoff r t x * (newtonReal x * (testPartial j (testPartial i φ)) x)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => (∫ x, exteriorCutoff r t x * (newtonHessianKernel i j x * φ x)) +
        (∫ x, exteriorCutoffPartial r t i x * newtonGradient j x * φ x) -
        (∫ x, exteriorCutoffPartial r t j x * newtonReal x * (testPartial i φ) x)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [mul_assoc] using newton_cutoff_double_ibp r t hr ht φ i j
  have h := tendsto_nhds_unique hL ((tendsto_congr' he).mpr hR)
  simpa only [newtonPVTruncated, sub_neg_eq_add] using h

theorem newton_inner_derivative_normal (r : ℝ) (hr : 0 < r) (φ : ScalarTest)
    (i j : Fin 3) (n : UnitSphere) :
    r ^ 2 * newtonReal (r • (n : Position)) * (testPartial i φ) (r • (n : Position)) *
      (-(n : Position) j) =
        -r / (4 * Real.pi) * ((n : Position) j * (testPartial i φ) (r • (n : Position))) := by
  simp only [newtonReal, norm_smul, Real.norm_eq_abs, abs_of_pos hr, unitSphere_norm, mul_one]
  field_simp

theorem newton_inner_contact_normal (r : ℝ) (hr : 0 < r) (φ : ScalarTest)
    (i j : Fin 3) (n : UnitSphere) :
    -(r ^ 2 * newtonGradient j (r • (n : Position)) * φ (r • (n : Position)) *
      (-(n : Position) i)) =
        -(4 * Real.pi)⁻¹ * ((n : Position) i * (n : Position) j * φ (r • (n : Position))) := by
  simp only [newtonGradient, norm_smul, Real.norm_eq_abs, abs_of_pos hr, unitSphere_norm,
    mul_one, PiLp.smul_apply, smul_eq_mul]
  field_simp

theorem newton_outer_boundary_vanishes (φ : ScalarTest) (i j : Fin 3) :
    ∃ R : ℝ, 0 < R ∧ ∀ T : ℝ, R ≤ T →
      newtonContactBoundary φ i j T = 0 ∧ newtonDerivativeBoundary φ i j T = 0 := by
  obtain ⟨R, hR, hbound⟩ := (φ.hasCompactSupport.union
    (testPartial i φ).hasCompactSupport).isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun T hT => ?_⟩
  have hn (n : UnitSphere) : ‖T • (n : Position)‖ = T := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hR.le.trans hT), unitSphere_norm, mul_one]
  have hφ (n : UnitSphere) : φ (T • (n : Position)) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs =>
      (hbound _ (Or.inl hs)).not_ge (by rw [hn]; exact hT))
  have hDerivative (n : UnitSphere) : (testPartial i φ) (T • (n : Position)) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs =>
      (hbound _ (Or.inr hs)).not_ge (by rw [hn]; exact hT))
  simp [newtonContactBoundary, newtonDerivativeBoundary, hφ, hDerivative]

end OQ7Prescribed
