import PrescribedExtinction.CompactOutgoingOperator
import PrescribedExtinction.OutgoingVolumeIdentification

/-! The bounded compact-domain operator is the restriction of the actual
distributional outgoing Maxwell volume potential, on every original smooth
test supported in the compact domain. The full-space distributional identity,
including its Newtonian contact term, is proved in the imported bridge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter

theorem compactOutgoingOperator_test_pairing (k R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) (φ : ScalarTest)
    (hφ : Function.support (φ : Position → ℝ) ⊆ Metric.closedBall 0 R) :
    (∫ x : Position, φ x • (compactOutgoingOperator k R hR f : VectorL2) x) =
      (∫ x : Position, φ x • (staticFourierOperator (f : VectorL2)) x) +
        ∫ x : Position, φ x • remainderPotential k (supportedPolarization R hR f) x := by
  have hs := φ.integrable_smul
    ((vectorL2_locallyIntegrable (staticFourierOperator (f : VectorL2))).locallyIntegrableOn _)
  have hr := φ.integrable_smul
    ((remainderPotential_locallyIntegrable k (supportedPolarization R hR f)).locallyIntegrableOn _)
  calc
    _ = ∫ x : Position,
        φ x • (staticFourierOperator (f : VectorL2)) x +
          φ x • remainderPotential k (supportedPolarization R hR f) x := by
      apply integral_congr_ae
      filter_upwards [compactOutgoingOperator_coe k R hR f] with x hx
      rw [hx]
      by_cases hxs : x ∈ Metric.closedBall 0 R
      · simp only [indicator_of_mem hxs, smul_add]
      · have hφ0 : φ x = 0 := by
          by_contra hxφ
          exact hxs (hφ hxφ)
        simp only [indicator_of_notMem hxs, hφ0, zero_smul, add_zero]
    _ = _ := integral_add hs hr

/-- Equality with the actual outgoing volume distribution on all original
compact-domain tests; no scattering equation is assumed of the current. -/
theorem compactOutgoingOperator_physical_distribution (k R : ℝ) (hR : 0 ≤ R)
    (f : SupportedVectorL2 R) (i : Fin 3) (φ : ScalarTest)
    (hφ : Function.support (φ : Position → ℝ) ⊆ Metric.closedBall 0 R) :
    vectorL2ComponentDistribution (compactOutgoingOperator k R hR f : VectorL2) i φ =
      outgoingVolumeDistribution k (supportedPolarization R hR f) i φ := by
  rw [outgoingVolumeDistribution_eq_staticFourier_add_remainder,
    supportedPolarization_toLp, add_apply, vectorL2ComponentDistribution_apply,
    vectorL2ComponentDistribution_apply, remainderPotentialComponentDistribution,
    Distribution.mapCLM_apply, remainderPotentialDistribution_apply]
  have h := congrArg (fun v : Vector => v i)
    (compactOutgoingOperator_test_pairing k R hR f φ hφ)
  exact h

/-- An actual bounded L² realization of the physical outgoing volume
distribution on the compact domain, for every supported vector L² current. -/
theorem outgoingVolumeDistribution_on_ball_bounded_L2_realization
    (k R : ℝ) (hR : 0 ≤ R) (f : SupportedVectorL2 R) :
    ∃ u : SupportedVectorL2 R,
      (∀ (i : Fin 3) (φ : ScalarTest),
        Function.support (φ : Position → ℝ) ⊆ Metric.closedBall 0 R →
          vectorL2ComponentDistribution (u : VectorL2) i φ =
            outgoingVolumeDistribution k (supportedPolarization R hR f) i φ) ∧
      ‖u‖ ≤ (1 + compactRemainderConstant k R) * ‖f‖ := by
  refine ⟨compactOutgoingOperator k R hR f, ?_,
    compactOutgoingOperator_apply_norm_le k R hR f⟩
  exact compactOutgoingOperator_physical_distribution k R hR f

end OQ7Prescribed
