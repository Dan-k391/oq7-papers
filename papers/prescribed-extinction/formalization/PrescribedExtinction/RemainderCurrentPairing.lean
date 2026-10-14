import PrescribedExtinction.OutgoingCurrentPairing
import PrescribedExtinction.RemainderConvolution

/-! Genuine vector Fubini pairings for the existing dynamic-minus-static
remainder convolution on compact L² currents. This file identifies that
convolution's action on tests, but does not assume its still separate
distributional kernel identification. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Convolution ENNReal

theorem cutoffDyadicRemainder_integrable (k T : ℝ) :
    Integrable (cutoffDyadicRemainder k T) volume := by
  apply Integrable.mono' ((cutoffGreen_integrable 0 T).norm.const_mul
    (dyadicRemainderCutoffConstant k T)) (cutoffDyadicRemainder_memLp k T).aestronglyMeasurable
  exact ae_of_all _ fun x => cutoffDyadicRemainder_norm_le k T x

def currentTestCorrelationVector (p : CompactPolarization) (φ : ScalarTest)
    (z : Position) : Vector :=
  ∫ y : Position, (φ (z + y) : ℂ) • p.current y

theorem currentTestCorrelationVector_integrable (p : CompactPolarization)
    (φ : ScalarTest) (z : Position) :
    Integrable (fun y : Position => (φ (z + y) : ℂ) • p.current y) volume := by
  apply (compactPolarization_current_integrable p).bdd_smul
    (SchwartzMap.seminorm ℂ 0 0 (scalarTestSchwartz φ))
    (Complex.continuous_ofReal.comp
      (φ.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  exact ae_of_all _ fun y => SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) (z + y)

theorem currentTestCorrelationVector_coordinate (p : CompactPolarization)
    (φ : ScalarTest) (z : Position) (i : Fin 3) :
    currentTestCorrelationVector p φ z i = newtonCurrentCorrelation p φ i z := by
  have h := ((vectorCoordinate i).integral_comp_comm
    (currentTestCorrelationVector_integrable p φ z)).symm
  change currentTestCorrelationVector p φ z i =
    ∫ y : Position, (φ (z + y) : ℂ) * p.current y i at h
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ fun y => mul_comm _ _

theorem remainder_current_pairing_integrand_cutoff (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (S : ℝ)
    (hS : ∀ x : Position, φ x ≠ 0 → ‖x‖ ≤ S) (x y : Position) :
    (φ x : ℂ) • dyadicRemainder k (x - y) (p.current y) =
      (φ x : ℂ) • cutoffDyadicRemainder k (S + p.radius) (x - y) (p.current y) := by
  by_cases hφ : φ x = 0
  · simp [hφ]
  · rw [remainderPotential_integrand_cutoff k p S x y (hS x hφ)]

theorem remainder_current_test_joint_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    Integrable (fun q : Position × Position =>
      (φ q.1 : ℂ) • dyadicRemainder k (q.1 - q.2) (p.current q.2)) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  have hb := (compactPolarization_current_integrable p).convolution_integrand
    vectorOperatorApply (cutoffDyadicRemainder_integrable k (S + p.radius))
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ q.1 : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  have h := hb.bdd_smul (SchwartzMap.seminorm ℂ 0 0 (scalarTestSchwartz φ)) hφ
    (ae_of_all _ fun q => SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) q.1)
  apply h.congr
  exact ae_of_all _ fun q =>
    (remainder_current_pairing_integrand_cutoff k p φ S hS q.1 q.2).symm

theorem remainder_current_correlation_joint_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    Integrable (fun q : Position × Position =>
      (φ (q.1 + q.2) : ℂ) • dyadicRemainder k q.1 (p.current q.2)) (volume.prod volume) := by
  obtain ⟨S, _, hS⟩ := scalarTest_support_radius φ
  let B : (Vector →L[ℂ] Vector) →L[ℂ] Vector →L[ℂ] Vector := vectorOperatorApply.flip
  have hb := (cutoffDyadicRemainder_integrable k (S + p.radius)).op_fst_snd
    B.continuous₂ ⟨‖B‖, fun A v => B.le_opNorm₂ A v⟩ (compactPolarization_current_integrable p)
  have hφ : AEStronglyMeasurable (fun q : Position × Position => (φ (q.1 + q.2) : ℂ))
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      (φ.continuous.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have h := hb.bdd_smul (SchwartzMap.seminorm ℂ 0 0 (scalarTestSchwartz φ)) hφ
    (ae_of_all _ fun q => SchwartzMap.norm_le_seminorm ℂ (scalarTestSchwartz φ) (q.1 + q.2))
  apply h.congr
  exact ae_of_all _ fun q => by
    have he := remainder_current_pairing_integrand_cutoff k p φ S hS (q.1 + q.2) q.2
    simp only [add_sub_cancel_right] at he
    exact he.symm

theorem remainder_current_correlation_inner (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (z : Position) :
    (∫ y : Position, (φ (z + y) : ℂ) • dyadicRemainder k z (p.current y)) =
      dyadicRemainder k z (currentTestCorrelationVector p φ z) := by
  calc
    _ = ∫ y : Position, dyadicRemainder k z ((φ (z + y) : ℂ) • p.current y) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => ((dyadicRemainder k z).map_smul _ _).symm
    _ = _ := (dyadicRemainder k z).integral_comp_comm
      (currentTestCorrelationVector_integrable p φ z)

theorem remainder_current_correlation_pairing_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    Integrable (fun z : Position => dyadicRemainder k z (currentTestCorrelationVector p φ z)) volume := by
  apply (remainder_current_correlation_joint_integrable k p φ).integral_prod_left.congr
  exact ae_of_all _ fun z => remainder_current_correlation_inner k p φ z

theorem remainderPotential_test_integrable (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    Integrable (fun x : Position => (φ x : ℂ) • remainderPotential k p x) volume := by
  apply (remainder_current_test_joint_integrable k p φ).integral_prod_left.congr
  exact ae_of_all _ fun x => by
    change (∫ y : Position, (φ x : ℂ) • dyadicRemainder k (x - y) (p.current y)) =
      (φ x : ℂ) • (∫ y : Position, dyadicRemainder k (x - y) (p.current y))
    exact integral_smul _ _

theorem remainderPotential_test_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    (∫ x : Position, (φ x : ℂ) • remainderPotential k p x) =
      ∫ z : Position, dyadicRemainder k z (currentTestCorrelationVector p φ z) := by
  calc
    _ = ∫ x : Position, ∫ y : Position,
        (φ x : ℂ) • dyadicRemainder k (x - y) (p.current y) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change (φ x : ℂ) • (∫ y : Position, dyadicRemainder k (x - y) (p.current y)) = _
        exact (integral_smul _ _).symm
    _ = ∫ y : Position, ∫ x : Position,
        (φ x : ℂ) • dyadicRemainder k (x - y) (p.current y) :=
      integral_integral_swap (remainder_current_test_joint_integrable k p φ)
    _ = ∫ y : Position, ∫ z : Position,
        (φ (z + y) : ℂ) • dyadicRemainder k z (p.current y) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x : Position, (φ x : ℂ) • dyadicRemainder k (x - y) (p.current y)) =
          ∫ z : Position, (φ (z + y) : ℂ) • dyadicRemainder k z (p.current y)
        have h := integral_add_right_eq_self (μ := (volume : Measure Position))
          (fun x : Position => (φ x : ℂ) • dyadicRemainder k (x - y) (p.current y)) y
        simpa only [add_sub_cancel_right] using h.symm
    _ = ∫ z : Position, ∫ y : Position,
        (φ (z + y) : ℂ) • dyadicRemainder k z (p.current y) :=
      (integral_integral_swap (remainder_current_correlation_joint_integrable k p φ)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun z => remainder_current_correlation_inner k p φ z)

theorem remainderPotential_locallyIntegrable (k : ℝ) (p : CompactPolarization) :
    LocallyIntegrable (remainderPotential k p) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨S, _, hKS⟩ := hK.isBounded.exists_pos_norm_lt
  apply Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (remainderPotential_aestronglyMeasurable k p) (M := (remainderPotentialBound k p S).toReal)
  apply ae_restrict_of_forall_mem hK.measurableSet
  intro x hx
  exact ENNReal.toReal_mono (remainderPotentialBound_lt_top k p S).ne
    (remainderPotential_enorm_le k p S x (hKS x hx).le)

def remainderPotentialDistribution (k : ℝ) (p : CompactPolarization) : VectorDistribution :=
  Distribution.ofFun ⊤ (remainderPotential k p) volume ⊤

theorem remainderPotentialDistribution_apply (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    remainderPotentialDistribution k p φ = ∫ x : Position, φ x • remainderPotential k p x := by
  exact Distribution.ofFun_apply ((remainderPotential_locallyIntegrable k p).locallyIntegrableOn _)

theorem remainderPotentialDistribution_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) :
    remainderPotentialDistribution k p φ =
      ∫ z : Position, dyadicRemainder k z (currentTestCorrelationVector p φ z) := by
  rw [remainderPotentialDistribution_apply, ← remainderPotential_test_pairing]
  apply integral_congr_ae
  exact ae_of_all _ fun x => (IsScalarTower.algebraMap_smul ℂ (φ x) (remainderPotential k p x)).symm

def remainderPotentialComponentDistribution (k : ℝ) (p : CompactPolarization)
    (i : Fin 3) : ScalarDistribution :=
  Distribution.mapCLM (vectorCoordinate i) (remainderPotentialDistribution k p)

theorem remainderPotentialComponentDistribution_pairing (k : ℝ) (p : CompactPolarization)
    (φ : ScalarTest) (i : Fin 3) :
    remainderPotentialComponentDistribution k p i φ =
      (∫ z : Position, dyadicRemainder k z (currentTestCorrelationVector p φ z)) i := by
  rw [remainderPotentialComponentDistribution, Distribution.mapCLM_apply,
    remainderPotentialDistribution_pairing]
  rfl

end OQ7Prescribed
