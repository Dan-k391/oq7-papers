import work.BodySharpLift
import work.PlanarDriveNorm

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem physicalBody_uniform_sharp_response_estimate (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hH : 0 ≤ h + d) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      ∀ (_hR : 1 ≤ B.aperture) (σ : Direction) (θ : ℝ) (α β : ℂ)
        (hα : 0 < α.im) (hβ : 0 < β.im),
        ‖normalizedActiveResponse k hk B σ θ α β hα hβ - bodySharpScalarLift B
          (planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ)‖ ≤
          (2 * B.aperture * ‖((squareApertureWindow_memLp 1).sub
            (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp (squareApertureWindow 1 - w)‖ /
              activeMaterialCoercivity α β + K / (activeMaterialCoercivity α β) ^ 2) * Real.sqrt d := by
  obtain ⟨K, hK, he⟩ := physicalBody_uniform_planar_response_estimate k hk h d hH w hw hwc hs
  refine ⟨K, hK, ?_⟩
  intro B hh hd hR σ θ α β hα hβ
  let q := planarNormalizedResponse k hk σ (B.absorberThickness + B.plateThickness)
    (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  let r := normalizedActiveResponse k hk B σ θ α β hα hβ
  let J := bodySharpScalarLift B
  let F := bodyScaledScalarLift B w hw hwc hs
  let e := ‖((squareApertureWindow_memLp 1).sub
    (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp (squareApertureWindow 1 - w)‖
  let c := activeMaterialCoercivity α β
  have hc : 0 < c := activeMaterialCoercivity_pos α β hα hβ
  have hg : ‖planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness‖ = Real.sqrt d := by
    rw [planarNormalizedDrive_norm _ _ _ _ B.absorberThickness_pos.le (by linarith [B.plateThickness_pos])]
    rw [hh, hd]
    congr 1
    ring
  have hb := he B hh hd hR σ θ α β hα hβ
  rw [normalizedIncidentDrive_window_mismatch_norm, hg] at hb
  change ‖r - F q‖ ≤ (1 / c) * (B.aperture * e * Real.sqrt d + K * (1 / c) * Real.sqrt d) at hb
  have hq := planarNormalizedResponse_norm_le k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  rw [hg] at hq
  change ‖q‖ ≤ (1 / c) * Real.sqrt d at hq
  have hdif : ‖F q - J q‖ ≤ B.aperture * e * ((1 / c) * Real.sqrt d) := by
    rw [norm_sub_rev, bodySharpScalarLift_window_difference_norm]
    exact mul_le_mul_of_nonneg_left hq (mul_nonneg B.aperture_pos.le (norm_nonneg _))
  have htriangle : ‖r - J q‖ ≤ ‖r - F q‖ + ‖F q - J q‖ := by
    calc
      _ = ‖(r - F q) + (F q - J q)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  apply htriangle.trans ((add_le_add hb hdif).trans_eq _)
  change (1 / c) * (B.aperture * e * Real.sqrt d + K * (1 / c) * Real.sqrt d) +
    B.aperture * e * ((1 / c) * Real.sqrt d) = (2 * B.aperture * e / c + K / c ^ 2) * Real.sqrt d
  ring

end OQ7Prescribed
