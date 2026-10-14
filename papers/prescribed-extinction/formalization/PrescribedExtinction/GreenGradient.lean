import PrescribedExtinction.YoungConvolution
import PrescribedExtinction.OutgoingDynamicIdentity

/-! First outgoing Green derivatives and their genuine compact-current
convolutions. The locally L¹ pole is handled by Young's L¹/L² bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def outgoingGradient (k : ℝ) (j : Fin 3) (x : Position) : ℂ :=
  (x j / ‖x‖) • outgoingRadialFirst k ‖x‖

theorem outgoingGradient_eq_static_add_dynamic (k : ℝ) (j : Fin 3) :
    outgoingGradient k j = outgoingGradient 0 j + dynamicGradientRemainder k j := by
  funext x
  simp only [outgoingGradient, dynamicGradientRemainder, smul_sub, Pi.add_apply]
  abel

theorem outgoingGradient_measurable (k : ℝ) (j : Fin 3) :
    Measurable (outgoingGradient k j) := by
  unfold outgoingGradient outgoingRadialFirst
  fun_prop

theorem outgoingGradient_zero_norm_le (j : Fin 3) (x : Position) :
    ‖outgoingGradient 0 j x‖ ≤ (4 * Real.pi)⁻¹ * ‖x‖⁻¹ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [outgoingGradient, outgoingRadialFirst]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc : ‖x j / ‖x‖‖ ≤ 1 := by
    rw [norm_div, Real.norm_of_nonneg hr.le]
    exact (div_le_one hr).mpr (PiLp.norm_apply_le x j)
  have hn : ‖outgoingRadialFirst 0 ‖x‖‖ = (4 * Real.pi)⁻¹ * ‖x‖⁻¹ ^ 2 := by
    simp [outgoingRadialFirst, norm_pow, abs_of_pos Real.pi_pos,
      div_eq_mul_inv, mul_inv_rev, inv_pow, mul_comm]
  rw [outgoingGradient, norm_smul, hn]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (by positivity)

theorem outgoingGradient_zero_locallyIntegrable (j : Fin 3) :
    LocallyIntegrable (outgoingGradient 0 j) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi)⁻¹) (α := 2)
    (by norm_num [Position, finrank_euclideanSpace_fin])
    (by norm_num [Position, finrank_euclideanSpace_fin])
    ?_ (outgoingGradient_measurable 0 j).aestronglyMeasurable
  exact ae_of_all _ fun x => by simpa using outgoingGradient_zero_norm_le j x

theorem outgoingGradient_locallyIntegrable (k : ℝ) (j : Fin 3) :
    LocallyIntegrable (outgoingGradient k j) volume := by
  rw [outgoingGradient_eq_static_add_dynamic]
  exact (outgoingGradient_zero_locallyIntegrable j).add
    (dynamicGradientRemainder_locallyIntegrable k j)

def cutoffOutgoingGradient (k R : ℝ) (j : Fin 3) : Position → ℂ :=
  (Metric.closedBall 0 R).indicator (outgoingGradient k j)

theorem cutoffOutgoingGradient_integrable (k R : ℝ) (j : Fin 3) :
    Integrable (cutoffOutgoingGradient k R j) volume := by
  exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
    ((outgoingGradient_locallyIntegrable k j).integrableOn_isCompact (isCompact_closedBall _ _))

def gradientPotential (k : ℝ) (p : CompactPolarization) (j : Fin 3) : Field :=
  fun x => ∫ y : Position, outgoingGradient k j (x - y) • p.current y

theorem outgoingGradient_hasLineDerivAt (k : ℝ) (j : Fin 3)
    (x : Position) (hx : x ≠ 0) :
    HasLineDerivAt ℝ (outgoingGreen k) (outgoingGradient k j x) x (basisR j) := by
  have h := (outgoingRadial_hasDerivAt k ‖x‖ (norm_ne_zero_iff.mpr hx)).hasFDerivAt.comp x
    (radialNorm_hasFDerivAt x hx)
  rw [show outgoingGreen k = fun y : Position => outgoingRadial k ‖y‖ from
    funext (outgoingGreen_eq_radial k)]
  convert! h.hasLineDerivAt (basisR j) using 1
  simp [outgoingGradient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_apply, innerSL_apply_apply,
    real_inner_basis, div_eq_mul_inv]
  ring

theorem gradientPotential_integrand_cutoff (k S : ℝ) (p : CompactPolarization)
    (j : Fin 3) (x y : Position) (hx : ‖x‖ ≤ S) :
    outgoingGradient k j (x - y) • p.current y =
      cutoffOutgoingGradient k (S + p.radius) j (x - y) • p.current y := by
  by_cases hy : ‖y‖ ≤ p.radius
  · have hxy : x - y ∈ Metric.closedBall 0 (S + p.radius) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact (norm_sub_le _ _).trans (add_le_add hx hy)
    simp only [cutoffOutgoingGradient, indicator_of_mem hxy]
  · simp [p.vanish y (lt_of_not_ge hy), smul_zero]

/-- The actual, untruncated first-derivative integrals exist almost everywhere
on every compact region; their L² realization does not rely on totalizing an
undefined Bochner integral. -/
theorem gradientPotential_ae_integrable_on_compact (k : ℝ) (p : CompactPolarization)
    (j : Fin 3) (K : Set Position) (hK : IsCompact K) :
    ∀ᵐ x ∂volume.restrict K,
      Integrable (fun y : Position => outgoingGradient k j (x - y) • p.current y) volume := by
  obtain ⟨S, hS, hKS⟩ := hK.isBounded.exists_pos_norm_lt
  have h := (compactPolarization_current_integrable p).ae_convolution_exists vectorScalarMul
    (cutoffOutgoingGradient_integrable k (S + p.radius) j)
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hK.measurableSet] with x hx hxK
  apply hx.congr
  exact ae_of_all _ fun y =>
    (gradientPotential_integrand_cutoff k S p j x y (hKS x hxK).le).symm

theorem gradientPotential_eq_cutoff (k S : ℝ) (p : CompactPolarization)
    (j : Fin 3) (x : Position) (hx : ‖x‖ ≤ S) :
    gradientPotential k p j x =
      scalarVectorConvolution (cutoffOutgoingGradient k (S + p.radius) j) p.current x := by
  unfold scalarVectorConvolution gradientPotential
  rw [← integral_sub_left_eq_self
    (fun y : Position => outgoingGradient k j (x - y) • p.current y) volume x]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [sub_sub_cancel]
    by_cases hy : ‖x - y‖ ≤ p.radius
    · have hys : y ∈ Metric.closedBall 0 (S + p.radius) := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        have he : y = x - (x - y) := by abel
        rw [he]
        exact (norm_sub_le _ _).trans (add_le_add hx hy)
      simp only [cutoffOutgoingGradient, indicator_of_mem hys]
    · simp [p.vanish (x - y) (lt_of_not_ge hy), smul_zero]

theorem gradientPotential_memLp_on_compact (k : ℝ) (p : CompactPolarization)
    (j : Fin 3) (K : Set Position) (hK : IsCompact K) :
    MemLp (gradientPotential k p j) 2 (volume.restrict K) := by
  obtain ⟨S, hS, hKS⟩ := hK.isBounded.exists_pos_norm_lt
  have h := (scalarVectorConvolution_memLp_two
    (cutoffOutgoingGradient k (S + p.radius) j) p.current
    (cutoffOutgoingGradient_integrable k (S + p.radius) j)
    (compactPolarization_current_integrable p) p.memLp).1.restrict K
  have he : scalarVectorConvolution (cutoffOutgoingGradient k (S + p.radius) j) p.current
      =ᵐ[volume.restrict K] gradientPotential k p j := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (gradientPotential_eq_cutoff k S p j x (hKS x hx).le).symm
  exact (memLp_congr_ae he).mp h

end OQ7Prescribed
