import work.BodyAbsorptionLocalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem physicalBody_normalized_powers_uniform_aperture_localization (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      R0 ≤ B.aperture → ∀ (σ : Direction) (θ : ℝ),
        |normalizedExtinction k hk B σ θ α β hα hβ - B.aperture ^ 2 *
          planarNormalizedExtinction k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ| +
        |normalizedAbsorption k hk B σ θ α β hα hβ - B.aperture ^ 2 *
          planarNormalizedAbsorption k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ| ≤ ε * B.aperture ^ 2 := by
  let c := activeMaterialCoercivity α β
  let C := activeMaterialNormBound α β
  let G := Real.sqrt d
  let L := (k + 2 * k * C / c) * G
  have hc : 0 < c := activeMaterialCoercivity_pos α β hα hβ
  have hC : 0 ≤ C := (norm_nonneg _).trans (le_max_left _ _)
  have hG : 0 < G := Real.sqrt_pos.mpr hd
  have hL : 0 < L := mul_pos (by
    have hp : 0 ≤ 2 * k * C / c := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk.le) hC) hc.le
    linarith) hG
  let δ := ε / L
  have hδ : 0 < δ := div_pos hε hL
  obtain ⟨R0, hR0, he⟩ := physicalBody_normalized_response_uniform_aperture_localization k hk h d hh hd α β hα hβ δ hδ
  refine ⟨R0, hR0, ?_⟩
  intro B hBh hBd hBR σ θ
  have hresponse := he B hBh hBd hBR σ θ
  have hx := normalizedExtinction_planar_lift_error_bound k hk B σ θ α β hα hβ
  have ha := normalizedAbsorption_planar_lift_error_bound k hk B σ θ α β hα hβ
  have hsqrt : Real.sqrt B.plateThickness = G := congrArg Real.sqrt hBd
  rw [hsqrt] at hx ha
  have hx' := hx.trans (mul_le_mul_of_nonneg_left hresponse
    (mul_nonneg (mul_nonneg hk.le B.aperture_pos.le) hG.le))
  have ha' := ha.trans (mul_le_mul_of_nonneg_left hresponse (by
    change 0 ≤ (2 * k * C / c) * B.aperture * G
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk.le) hC) hc.le) B.aperture_pos.le) hG.le))
  apply (add_le_add hx' ha').trans_eq
  change k * B.aperture * G * (δ * B.aperture) + (2 * k * C / c) * B.aperture * G * (δ * B.aperture) = ε * B.aperture ^ 2
  calc
    _ = L * δ * B.aperture ^ 2 := by dsimp only [L]; ring
    _ = _ := by rw [show L * δ = ε from by dsimp only [δ]; field_simp]

end OQ7Prescribed
