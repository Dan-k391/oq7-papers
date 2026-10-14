import PrescribedExtinction.BodyMaterialLift
import PrescribedExtinction.InverseTrialEstimate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem physicalBody_uniform_planar_response_estimate (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hH : 0 ≤ h + d) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      ∀ (_hR : 1 ≤ B.aperture) (σ : Direction) (θ : ℝ) (α β : ℂ)
        (hα : 0 < α.im) (hβ : 0 < β.im),
        ‖normalizedActiveResponse k hk B σ θ α β hα hβ -
          bodyScaledScalarLift B w hw hwc hs
            (planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ)‖ ≤
          (1 / activeMaterialCoercivity α β) *
            (‖normalizedIncidentDrive k B σ - bodyScaledScalarLift B w hw hwc hs
              (planarNormalizedDrive k σ _ B.absorberThickness)‖ +
                K * (1 / activeMaterialCoercivity α β) * ‖planarNormalizedDrive k σ
                  (B.absorberThickness + B.plateThickness) B.absorberThickness‖) := by
  obtain ⟨K, hK, he⟩ := physicalBody_uniform_planar_operator_residual k hk h d hH w hw hwc hs
  refine ⟨K, hK, ?_⟩
  intro B hh hd hR σ θ α β hα hβ
  let q := planarNormalizedResponse k hk σ (B.absorberThickness + B.plateThickness)
    (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  let e := activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  have hres := he B hh hd hR θ q
  rw [← bodyScaledScalarLift_material_residual_identity k hk B w hw hwc hs θ α β q] at hres
  have hM : 0 ≤ 1 / activeMaterialCoercivity α β :=
    (one_div_pos.mpr (activeMaterialCoercivity_pos α β hα hβ)).le
  have hb := inverse_trial_residual_estimate e
    (planarActiveMaterialOperator k hk _ (bodyHeight_pos B).le B.absorberThickness θ α β)
    (bodyScaledScalarLift B w hw hwc hs) (normalizedIncidentDrive k B σ)
    (planarNormalizedDrive k σ _ B.absorberThickness) q
    (planarNormalizedResponse_equation k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ)
    (1 / activeMaterialCoercivity α β) K hM
    (activeMaterialEquiv_inverse_norm_le k hk B (basisR 0) (rotatedAxis θ) α β hα hβ) hres
  have hq := planarNormalizedResponse_norm_le k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hM
  have hkn := mul_le_mul_of_nonneg_left hq hK.le
  exact add_le_add le_rfl (by simpa only [mul_assoc, q, activeMaterialCoercivity, activeScalarLoss] using hkn)

end OQ7Prescribed

