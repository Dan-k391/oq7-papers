import PrescribedExtinction.SharpResponseEstimate
import PrescribedExtinction.ApertureErrorAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem physicalBody_normalized_response_uniform_aperture_localization (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      R0 ≤ B.aperture → ∀ (σ : Direction) (θ : ℝ),
        ‖normalizedActiveResponse k hk B σ θ α β hα hβ - bodySharpScalarLift B
          (planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ)‖ ≤ ε * B.aperture := by
  let c := activeMaterialCoercivity α β
  let G := Real.sqrt d
  have hc : 0 < c := activeMaterialCoercivity_pos α β hα hβ
  have hG : 0 < G := Real.sqrt_pos.mpr hd
  let δ := ε * c / (4 * G)
  have hδ : 0 < δ := div_pos (mul_pos hε hc) (mul_pos (by norm_num) hG)
  obtain ⟨w, hw, hwc, hs, he⟩ := squareApertureWindow_smooth_L2_approximation δ hδ
  obtain ⟨K, hK, hb⟩ := physicalBody_uniform_sharp_response_estimate k hk h d (by linarith) w hw hwc hs
  refine ⟨max 1 (2 * K * G / (ε * c ^ 2)), le_max_left _ _, ?_⟩
  intro B hBh hBd hBR σ θ
  have hR : 1 ≤ B.aperture := (le_max_left _ _).trans hBR
  have hr : 2 * K * G / (ε * c ^ 2) ≤ B.aperture := (le_max_right _ _).trans hBR
  have hbound := hb B hBh hBd hR σ θ α β hα hβ
  apply hbound.trans
  exact aperture_error_le_of_window_and_radius ε c G K _ B.aperture
    hε hc hG B.aperture_pos.le he.le hr

end OQ7Prescribed

