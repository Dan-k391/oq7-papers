import PrescribedExtinction.InverseStability
import PrescribedExtinction.RotationResponse

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

/-- The actual physical normalized response error is controlled by its volume-equation residual,
with the same aperture- and rotation-independent constant as the genuine inverse. -/
theorem normalizedActiveResponse_residual_bound (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) (q : ScalarBodyCurrentL2 B) :
    ‖normalizedActiveResponse k hk B σ θ α β hα hβ - q‖ ≤
      (1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β)) *
        ‖-normalizedIncidentDrive k B σ - activeMaterialOperator k B (basisR 0) (rotatedAxis θ) α β q‖ := by
  let e := activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  apply (continuousLinearEquiv_solution_residual_bound e (-normalizedIncidentDrive k B σ) q).trans
  exact mul_le_mul_of_nonneg_right (activeMaterialEquiv_inverse_norm_le k hk B (basisR 0) (rotatedAxis θ)
    α β hα hβ) (norm_nonneg _)

theorem normalizedActiveResponse_angle_difference_bound (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ φ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    ‖normalizedActiveResponse k hk B σ θ α β hα hβ - normalizedActiveResponse k hk B σ φ α β hα hβ‖ ≤
      (1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β)) *
        (‖activeMaterialOperator k B (basisR 0) (rotatedAxis θ) α β -
          activeMaterialOperator k B (basisR 0) (rotatedAxis φ) α β‖ *
            ‖normalizedActiveResponse k hk B σ φ α β hα hβ‖) := by
  let e := activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  let f := activeMaterialEquiv k hk B (basisR 0) (rotatedAxis φ) α β hα hβ
  have hb := continuousLinearEquiv_response_difference_bound e f
    (-normalizedIncidentDrive k B σ) (-normalizedIncidentDrive k B σ)
  simp only [sub_self, norm_zero, zero_add] at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (activeMaterialEquiv_inverse_norm_le k hk B (basisR 0) (rotatedAxis θ)
    α β hα hβ) (by positivity)

end OQ7Prescribed
