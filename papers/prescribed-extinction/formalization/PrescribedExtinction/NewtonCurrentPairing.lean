import PrescribedExtinction.NewtonTransform
import PrescribedExtinction.VolumePotential
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual compact L² current/test correlations and the Newton potential
pairing. All current and double-integral integrability obligations are proved
from compact support and the existing physical kernel. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Convolution ENNReal

theorem compactPolarization_current_hasCompactSupport (p : CompactPolarization) :
    HasCompactSupport p.current := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) p.radius)
  intro x hx
  apply p.vanish
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx

theorem compactPolarization_current_integrable (p : CompactPolarization) :
    Integrable p.current volume := by
  have hs : Function.support p.current ⊆ Metric.closedBall (0 : Position) p.radius := by
    intro x hx
    by_contra hn
    have hz := p.vanish x (by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn)
    exact hx hz
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact (p.memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrableOn_isCompact
    (isCompact_closedBall _ _)

theorem current_component_integrable (p : CompactPolarization) (i : Fin 3) :
    Integrable (fun y : Position => p.current y i) volume := by
  exact (vectorCoordinate i).integrable_comp (compactPolarization_current_integrable p)

theorem cutoffGreen_integrable (k T : ℝ) : Integrable (cutoffGreen k T) volume := by
  unfold cutoffGreen
  apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
  exact (outgoingGreen_locallyIntegrable k).integrableOn_isCompact (isCompact_closedBall _ _)

def newtonCurrentCorrelation (p : CompactPolarization) (φ : ScalarTest)
    (j : Fin 3) (z : Position) : ℂ :=
  ∫ y : Position, p.current y j * (φ (z + y) : ℂ)

theorem scalarTest_support_radius (φ : ScalarTest) :
    ∃ S : ℝ, 0 < S ∧ ∀ x : Position, φ x ≠ 0 → ‖x‖ ≤ S := by
  obtain ⟨S, hS, hb⟩ := φ.hasCompactSupport.isBounded.exists_pos_norm_lt
  exact ⟨S, hS, fun x hx => (hb x (subset_tsupport φ hx)).le⟩

theorem newton_current_pairing_integrand_cutoff (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) (S : ℝ)
    (hS : ∀ x : Position, φ x ≠ 0 → ‖x‖ ≤ S) (x y : Position) :
    (φ x : ℂ) * outgoingGreen 0 (x - y) * p.current y i =
      (φ x : ℂ) * cutoffGreen 0 (S + p.radius) (x - y) * p.current y i := by
  by_cases hφ : φ x = 0
  · simp [hφ]
  · have h := outgoingPotential_integrand_cutoff 0 p S x y (hS x hφ)
    have hc := congrArg (fun v : Vector => (φ x : ℂ) * v i) h
    simpa only [vectorScalarMul_apply, PiLp.smul_apply, smul_eq_mul, mul_assoc] using hc

theorem newton_current_test_joint_integrable (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun q : Position × Position =>
      (φ q.1 : ℂ) * outgoingGreen 0 (q.1 - q.2) * p.current q.2 i) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (current_component_integrable p i).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) (cutoffGreen_integrable 0 (S + p.radius))
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ q.1 : ℂ))
      (volume.prod volume) := by
    exact (Complex.continuous_ofReal.comp (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  have h := hb.bdd_mul hφ (ae_of_all _ fun q =>
    SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) q.1)
  apply h.congr
  exact ae_of_all _ fun q => by
    change (φ q.1 : ℂ) * (p.current q.2 i * cutoffGreen 0 (S + p.radius) (q.1 - q.2)) =
      (φ q.1 : ℂ) * outgoingGreen 0 (q.1 - q.2) * p.current q.2 i
    rw [newton_current_pairing_integrand_cutoff p φ i S hS q.1 q.2]
    ring

theorem newton_current_correlation_joint_integrable (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun q : Position × Position =>
      (φ (q.1 + q.2) : ℂ) * outgoingGreen 0 q.1 * p.current q.2 i) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (cutoffGreen_integrable 0 (S + p.radius)).mul_prod (current_component_integrable p i)
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ (q.1 + q.2) : ℂ))
      (volume.prod volume) := by
    exact (Complex.continuous_ofReal.comp
      (φ.continuous.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have h := hb.bdd_mul hφ (ae_of_all _ fun q =>
    SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) (q.1 + q.2))
  apply h.congr
  exact ae_of_all _ fun q => by
    change (φ (q.1 + q.2) : ℂ) * (cutoffGreen 0 (S + p.radius) q.1 * p.current q.2 i) = _
    have he := newton_current_pairing_integrand_cutoff p φ i S hS (q.1 + q.2) q.2
    simp only [add_sub_cancel_right] at he
    exact (mul_assoc _ _ _).symm.trans he.symm

theorem outgoingPotential_zero_component_integral (p : CompactPolarization)
    (i : Fin 3) (x : Position) :
    outgoingPotential 0 p x i = ∫ y : Position, outgoingGreen 0 (x - y) * p.current y i := by
  exact ((vectorCoordinate i).integral_comp_comm (outgoingPotential_integrable 0 p x)).symm

theorem potentialComponentDistribution_zero_apply_integral (p : CompactPolarization)
    (i : Fin 3) (φ : ScalarTest) :
    potentialComponentDistribution 0 p i φ =
      ∫ x : Position, (φ x : ℂ) * outgoingPotential 0 p x i := by
  rw [potentialComponentDistribution_apply]
  have h := ((vectorCoordinate i).integral_comp_comm
    (φ.integrable_smul ((outgoingPotential_locallyIntegrable 0 p).locallyIntegrableOn _))).symm
  simpa only [vectorCoordinate, PiLp.proj_apply, PiLp.smul_apply, Complex.real_smul] using h

theorem newton_current_correlation_pairing_integrable (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun z : Position => outgoingGreen 0 z * newtonCurrentCorrelation p φ i z) volume := by
  have h := (newton_current_correlation_joint_integrable p φ i).integral_prod_left
  apply h.congr
  exact ae_of_all _ fun z => by
    change (∫ y : Position, (φ (z + y) : ℂ) * outgoingGreen 0 z * p.current y i) =
      outgoingGreen 0 z * newtonCurrentCorrelation p φ i z
    unfold newtonCurrentCorrelation
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by ring

theorem potentialComponentDistribution_newton_pairing (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    potentialComponentDistribution 0 p i φ =
      ∫ z : Position, outgoingGreen 0 z * newtonCurrentCorrelation p φ i z := by
  rw [potentialComponentDistribution_zero_apply_integral]
  calc
    _ = ∫ x : Position, ∫ y : Position,
        (φ x : ℂ) * outgoingGreen 0 (x - y) * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change (φ x : ℂ) * outgoingPotential 0 p x i =
          ∫ y : Position, (φ x : ℂ) * outgoingGreen 0 (x - y) * p.current y i
        rw [outgoingPotential_zero_component_integral, ← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun y => (mul_assoc _ _ _).symm
    _ = ∫ y : Position, ∫ x : Position,
        (φ x : ℂ) * outgoingGreen 0 (x - y) * p.current y i :=
      integral_integral_swap (newton_current_test_joint_integrable p φ i)
    _ = ∫ y : Position, ∫ z : Position,
        (φ (z + y) : ℂ) * outgoingGreen 0 z * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x : Position, (φ x : ℂ) * outgoingGreen 0 (x - y) * p.current y i) =
          ∫ z : Position, (φ (z + y) : ℂ) * outgoingGreen 0 z * p.current y i
        have h := integral_add_right_eq_self (μ := (volume : Measure Position))
          (fun x : Position => (φ x : ℂ) * outgoingGreen 0 (x - y) * p.current y i) y
        simpa only [add_sub_cancel_right] using h.symm
    _ = ∫ z : Position, ∫ y : Position,
        (φ (z + y) : ℂ) * outgoingGreen 0 z * p.current y i :=
      (integral_integral_swap (newton_current_correlation_joint_integrable p φ i)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change (∫ y : Position, (φ (z + y) : ℂ) * outgoingGreen 0 z * p.current y i) =
          outgoingGreen 0 z * newtonCurrentCorrelation p φ i z
        unfold newtonCurrentCorrelation
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by ring

end OQ7Prescribed
