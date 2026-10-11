import PrescribedExtinction.BodyCompressedError

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem physicalBody_uniform_planar_operator_residual (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hH : 0 ≤ h + d) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      ∀ (hR : 1 ≤ B.aperture) (θ : ℝ) (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)),
        ‖activeProjection B (basisR 0) (rotatedAxis θ) (bodyOutgoingOperator k B
          (activeInjection B (basisR 0) (rotatedAxis θ) (bodyScaledScalarLift B w hw hwc hs q))) -
            bodyScaledScalarLift B w hw hwc hs
              (planarActiveOutgoing k hk _ (bodyHeight_pos B).le B.absorberThickness θ q)‖ ≤ K * ‖q‖ := by
  obtain ⟨K, hK, he⟩ := bodySlabError_uniform_bound k hk h d hH w hw hwc hs
  refine ⟨4 * K, by positivity, ?_⟩
  intro B hh hd hR θ q
  obtain ⟨hc, hs'⟩ := planarActiveAxisMaps_norm_le _ B.absorberThickness θ q
  have hu : ‖(1 : ℂ)‖ ≤ 1 := by norm_num
  have hv : ‖Complex.I‖ ≤ 1 := by simp
  have h00 := he B hh hd hR 1 1 hu hu (planarLayerAxisMap _ B.absorberThickness 1 (Real.cos θ) q)
  have h10 := he B hh hd hR Complex.I 1 hv hu (planarLayerAxisMap _ B.absorberThickness 0 (Real.sin θ) q)
  have h01 := he B hh hd hR 1 Complex.I hu hv (planarLayerAxisMap _ B.absorberThickness 1 (Real.cos θ) q)
  have h11 := he B hh hd hR Complex.I Complex.I hv hv (planarLayerAxisMap _ B.absorberThickness 0 (Real.sin θ) q)
  rw [bodyCompressed_aperture_error_identity k hk B hR w hw hwc hs θ q]
  apply (bodyCompressFourErrors_norm_le _ _ _ _ _ _).trans
  have hc' := mul_le_mul_of_nonneg_left hc hK.le
  have hs'' := mul_le_mul_of_nonneg_left hs' hK.le
  linarith

end OQ7Prescribed

