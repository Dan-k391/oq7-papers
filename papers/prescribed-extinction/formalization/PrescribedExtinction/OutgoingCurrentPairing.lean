import PrescribedExtinction.NewtonCurrentPairing

/-! Actual compact L² current/test pairing with the physical scalar outgoing
Green kernel at arbitrary frequency. Both Fubini interchanges are justified
with finite cutoffs and absolute integrability. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Convolution ENNReal

theorem outgoing_current_pairing_integrand_cutoff (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) (S : ℝ)
    (hS : ∀ x : Position, φ x ≠ 0 → ‖x‖ ≤ S) (x y : Position) :
    (φ x : ℂ) * outgoingGreen k (x - y) * p.current y i =
      (φ x : ℂ) * cutoffGreen k (S + p.radius) (x - y) * p.current y i := by
  by_cases hφ : φ x = 0
  · simp [hφ]
  · have h := outgoingPotential_integrand_cutoff k p S x y (hS x hφ)
    have hc := congrArg (fun v : Vector => (φ x : ℂ) * v i) h
    simpa only [vectorScalarMul_apply, PiLp.smul_apply, smul_eq_mul, mul_assoc] using hc

theorem outgoing_current_test_joint_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun q : Position × Position =>
      (φ q.1 : ℂ) * outgoingGreen k (q.1 - q.2) * p.current q.2 i) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (current_component_integrable p i).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) (cutoffGreen_integrable k (S + p.radius))
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ q.1 : ℂ))
      (volume.prod volume) := by
    exact (Complex.continuous_ofReal.comp (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  have h := hb.bdd_mul hφ (ae_of_all _ fun q =>
    SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) q.1)
  apply h.congr
  exact ae_of_all _ fun q => by
    change (φ q.1 : ℂ) * (p.current q.2 i * cutoffGreen k (S + p.radius) (q.1 - q.2)) =
      (φ q.1 : ℂ) * outgoingGreen k (q.1 - q.2) * p.current q.2 i
    rw [outgoing_current_pairing_integrand_cutoff k p φ i S hS q.1 q.2]
    ring

theorem outgoing_current_correlation_joint_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun q : Position × Position =>
      (φ (q.1 + q.2) : ℂ) * outgoingGreen k q.1 * p.current q.2 i) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (cutoffGreen_integrable k (S + p.radius)).mul_prod (current_component_integrable p i)
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ (q.1 + q.2) : ℂ))
      (volume.prod volume) := by
    exact (Complex.continuous_ofReal.comp
      (φ.continuous.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have h := hb.bdd_mul hφ (ae_of_all _ fun q =>
    SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) (q.1 + q.2))
  apply h.congr
  exact ae_of_all _ fun q => by
    change (φ (q.1 + q.2) : ℂ) * (cutoffGreen k (S + p.radius) q.1 * p.current q.2 i) = _
    have he := outgoing_current_pairing_integrand_cutoff k p φ i S hS (q.1 + q.2) q.2
    simp only [add_sub_cancel_right] at he
    exact (mul_assoc _ _ _).symm.trans he.symm

theorem outgoingPotential_component_integral (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) (x : Position) :
    outgoingPotential k p x i = ∫ y : Position, outgoingGreen k (x - y) * p.current y i := by
  exact ((vectorCoordinate i).integral_comp_comm (outgoingPotential_integrable k p x)).symm

theorem potentialComponentDistribution_apply_integral (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) (φ : ScalarTest) :
    potentialComponentDistribution k p i φ =
      ∫ x : Position, (φ x : ℂ) * outgoingPotential k p x i := by
  rw [potentialComponentDistribution_apply]
  have h := ((vectorCoordinate i).integral_comp_comm
    (φ.integrable_smul ((outgoingPotential_locallyIntegrable k p).locallyIntegrableOn _))).symm
  simpa only [vectorCoordinate, PiLp.proj_apply, PiLp.smul_apply, Complex.real_smul] using h

theorem outgoing_current_correlation_pairing_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun z : Position => outgoingGreen k z * newtonCurrentCorrelation p φ i z) volume := by
  have h := (outgoing_current_correlation_joint_integrable k p φ i).integral_prod_left
  apply h.congr
  exact ae_of_all _ fun z => by
    change (∫ y : Position, (φ (z + y) : ℂ) * outgoingGreen k z * p.current y i) =
      outgoingGreen k z * newtonCurrentCorrelation p φ i z
    unfold newtonCurrentCorrelation
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by ring

theorem potentialComponentDistribution_outgoing_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    potentialComponentDistribution k p i φ =
      ∫ z : Position, outgoingGreen k z * newtonCurrentCorrelation p φ i z := by
  rw [potentialComponentDistribution_apply_integral]
  calc
    _ = ∫ x : Position, ∫ y : Position,
        (φ x : ℂ) * outgoingGreen k (x - y) * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change (φ x : ℂ) * outgoingPotential k p x i =
          ∫ y : Position, (φ x : ℂ) * outgoingGreen k (x - y) * p.current y i
        rw [outgoingPotential_component_integral, ← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun y => (mul_assoc _ _ _).symm
    _ = ∫ y : Position, ∫ x : Position,
        (φ x : ℂ) * outgoingGreen k (x - y) * p.current y i :=
      integral_integral_swap (outgoing_current_test_joint_integrable k p φ i)
    _ = ∫ y : Position, ∫ z : Position,
        (φ (z + y) : ℂ) * outgoingGreen k z * p.current y i := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x : Position, (φ x : ℂ) * outgoingGreen k (x - y) * p.current y i) =
          ∫ z : Position, (φ (z + y) : ℂ) * outgoingGreen k z * p.current y i
        have h := integral_add_right_eq_self (μ := (volume : Measure Position))
          (fun x : Position => (φ x : ℂ) * outgoingGreen k (x - y) * p.current y i) y
        simpa only [add_sub_cancel_right] using h.symm
    _ = ∫ z : Position, ∫ y : Position,
        (φ (z + y) : ℂ) * outgoingGreen k z * p.current y i :=
      (integral_integral_swap (outgoing_current_correlation_joint_integrable k p φ i)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change (∫ y : Position, (φ (z + y) : ℂ) * outgoingGreen k z * p.current y i) =
          outgoingGreen k z * newtonCurrentCorrelation p φ i z
        unfold newtonCurrentCorrelation
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by ring

end OQ7Prescribed
