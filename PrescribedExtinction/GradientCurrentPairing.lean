import PrescribedExtinction.GreenFirstDerivative
import PrescribedExtinction.VolumeFundamental

/-! Identification of the actual first Green derivative convolution with the
distributional derivative of the original scalar volume potential. Both
Fubini interchanges and almost-everywhere convolution existence are proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem gradientPotential_locallyIntegrable (k : ℝ) (p : CompactPolarization) (j : Fin 3) :
    LocallyIntegrable (gradientPotential k p j) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_one_iff_integrable.mp
    ((gradientPotential_memLp_on_compact k p j K hK).mono_exponent (by norm_num))

def gradientPotentialComponentDistribution (k : ℝ) (p : CompactPolarization)
    (j i : Fin 3) : ScalarDistribution :=
  Distribution.ofFun ⊤ (fun x : Position => gradientPotential k p j x i) volume ⊤

theorem gradientPotentialComponentDistribution_apply (k : ℝ) (p : CompactPolarization)
    (j i : Fin 3) (φ : ScalarTest) :
    gradientPotentialComponentDistribution k p j i φ =
      ∫ x : Position, (φ x : ℂ) * gradientPotential k p j x i := by
  rw [gradientPotentialComponentDistribution, Distribution.ofFun_apply]
  · simp only [Complex.real_smul]
  · have hl : LocallyIntegrable (fun x : Position => gradientPotential k p j x i) volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      exact (vectorCoordinate i).integrable_comp
        ((gradientPotential_locallyIntegrable k p j).integrableOn_isCompact hK)
    exact hl.locallyIntegrableOn _

theorem gradient_current_pairing_integrand_cutoff (k : ℝ) (p : CompactPolarization)
    (j : Fin 3) (φ : ScalarTest) (i : Fin 3) (S : ℝ)
    (hS : ∀ x : Position, φ x ≠ 0 → ‖x‖ ≤ S) (x y : Position) :
    (φ x : ℂ) * outgoingGradient k j (x - y) * p.current y i =
      (φ x : ℂ) * cutoffOutgoingGradient k (S + p.radius) j (x - y) * p.current y i := by
  by_cases hφ : φ x = 0
  · simp [hφ]
  · have h := gradientPotential_integrand_cutoff k S p j x y (hS x hφ)
    have hc := congrArg (fun v : Vector => (φ x : ℂ) * v i) h
    simpa only [PiLp.smul_apply, smul_eq_mul, mul_assoc] using hc

theorem gradient_current_test_joint_integrable (k : ℝ) (p : CompactPolarization)
    (j : Fin 3) (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun q : Position × Position =>
      (φ q.1 : ℂ) * outgoingGradient k j (q.1 - q.2) * p.current q.2 i) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (current_component_integrable p i).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) (cutoffOutgoingGradient_integrable k (S + p.radius) j)
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ q.1 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  have h := hb.bdd_mul hφ (ae_of_all _ fun q =>
    SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) q.1)
  apply h.congr
  exact ae_of_all _ fun q => by
    change (φ q.1 : ℂ) * (p.current q.2 i * cutoffOutgoingGradient k (S + p.radius) j (q.1 - q.2)) =
      (φ q.1 : ℂ) * outgoingGradient k j (q.1 - q.2) * p.current q.2 i
    rw [gradient_current_pairing_integrand_cutoff k p j φ i S hS q.1 q.2]
    ring

theorem gradient_current_correlation_joint_integrable (k : ℝ) (p : CompactPolarization)
    (j : Fin 3) (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun q : Position × Position =>
      (φ (q.1 + q.2) : ℂ) * outgoingGradient k j q.1 * p.current q.2 i) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (cutoffOutgoingGradient_integrable k (S + p.radius) j).mul_prod
    (current_component_integrable p i)
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ (q.1 + q.2) : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      (φ.continuous.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have h := hb.bdd_mul hφ (ae_of_all _ fun q =>
    SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) (q.1 + q.2))
  apply h.congr
  exact ae_of_all _ fun q => by
    change (φ (q.1 + q.2) : ℂ) * (cutoffOutgoingGradient k (S + p.radius) j q.1 * p.current q.2 i) = _
    have he := gradient_current_pairing_integrand_cutoff k p j φ i S hS (q.1 + q.2) q.2
    simp only [add_sub_cancel_right] at he
    exact (mul_assoc _ _ _).symm.trans he.symm

theorem gradientPotentialComponentDistribution_pairing (k : ℝ) (p : CompactPolarization)
    (j i : Fin 3) (φ : ScalarTest) :
    gradientPotentialComponentDistribution k p j i φ =
      ∫ z : Position, outgoingGradient k j z * newtonCurrentCorrelation p φ i z := by
  rw [gradientPotentialComponentDistribution_apply]
  obtain ⟨S, hSpos, hS⟩ := scalarTest_support_radius φ
  have hi : ∀ᵐ x ∂volume, x ∈ Metric.closedBall 0 S →
      Integrable (fun y : Position => outgoingGradient k j (x - y) • p.current y) volume :=
    (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).mp
      (gradientPotential_ae_integrable_on_compact k p j _ (isCompact_closedBall _ _))
  calc
    _ = ∫ x : Position, ∫ y : Position,
        (φ x : ℂ) * outgoingGradient k j (x - y) * p.current y i := by
      apply integral_congr_ae
      filter_upwards [hi] with x hx
      by_cases hφ : φ x = 0
      · simp [hφ]
      · have hxK : x ∈ Metric.closedBall 0 S := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hS x hφ
        have hp := ((vectorCoordinate i).integral_comp_comm (hx hxK)).symm
        change gradientPotential k p j x i =
          ∫ y : Position, outgoingGradient k j (x - y) * p.current y i at hp
        rw [hp, ← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun y => (mul_assoc _ _ _).symm
    _ = ∫ y : Position, ∫ x : Position,
        (φ x : ℂ) * outgoingGradient k j (x - y) * p.current y i :=
      integral_integral_swap (gradient_current_test_joint_integrable k p j φ i)
    _ = ∫ y : Position, ∫ z : Position,
        (φ (z + y) : ℂ) * outgoingGradient k j z * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        have h := integral_add_right_eq_self (μ := (volume : Measure Position))
          (fun x : Position => (φ x : ℂ) * outgoingGradient k j (x - y) * p.current y i) y
        simpa only [add_sub_cancel_right] using h.symm
    _ = ∫ z : Position, ∫ y : Position,
        (φ (z + y) : ℂ) * outgoingGradient k j z * p.current y i :=
      (integral_integral_swap (gradient_current_correlation_joint_integrable k p j φ i)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change (∫ y : Position, (φ (z + y) : ℂ) * outgoingGradient k j z * p.current y i) =
          outgoingGradient k j z * newtonCurrentCorrelation p φ i z
        unfold newtonCurrentCorrelation
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by ring

theorem currentCorrelation_green_first_ibp (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i j : Fin 3) :
    (∫ z : Position, newtonCurrentCorrelation p (testPartial j φ) i z * outgoingGreen k z) =
      -(∫ z : Position, newtonCurrentCorrelation p φ i z * outgoingGradient k j z) := by
  rw [currentCorrelation_pairing_re_im p _ i (outgoingGreen_locallyIntegrable k),
    currentCorrelation_pairing_re_im p φ i (outgoingGradient_locallyIntegrable k j)]
  rw [← currentCorrelationRealTest_partial, ← currentCorrelationRealTest_partial]
  rw [outgoingGreen_first_test_ibp, outgoingGreen_first_test_ibp]
  ring

/-- The genuine locally L² first-derivative convolution represents the exact
distributional derivative of the actual scalar volume potential, for every
original compact vector L² current, including nonsmooth currents. -/
theorem potentialComponent_first_distribution (k : ℝ) (p : CompactPolarization)
    (j i : Fin 3) :
    distributionPartial j (potentialComponentDistribution k p i) =
      gradientPotentialComponentDistribution k p j i := by
  ext φ
  simp only [distributionPartial, Distribution.lineDerivCLM_apply]
  rw [potentialComponentDistribution_outgoing_pairing,
    gradientPotentialComponentDistribution_pairing]
  have h := currentCorrelation_green_first_ibp k p φ i j
  simpa only [testPartial, neg_neg, mul_comm] using congrArg (fun z : ℂ => -z) h

end OQ7Prescribed
