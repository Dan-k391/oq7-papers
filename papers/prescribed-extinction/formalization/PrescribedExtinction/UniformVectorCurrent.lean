import PrescribedExtinction.UniformPhysicalPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem physicalBody_normalized_vector_current_uniform_aperture_localization (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      R0 ≤ B.aperture → ∀ (σ : Direction) (θ : ℝ),
        ‖activeInjection B (basisR 0) (rotatedAxis θ) (normalizedActiveResponse k hk B σ θ α β hα hβ) -
          activeInjection B (basisR 0) (rotatedAxis θ) (bodySharpScalarLift B
            (planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ))‖ ≤ ε * B.aperture := by
  obtain ⟨R0, hR0, he⟩ := physicalBody_normalized_response_uniform_aperture_localization k hk h d hh hd α β hα hβ ε hε
  refine ⟨R0, hR0, ?_⟩
  intro B hBh hBd hBR σ θ
  rw [← map_sub, activeInjection_norm]
  · exact he B hBh hBd hBR σ θ
  · simp [basisR, EuclideanSpace.norm_sq_eq]
  · exact rotatedAxis_unit θ

end OQ7Prescribed
