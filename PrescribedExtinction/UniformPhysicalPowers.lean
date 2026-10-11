import PrescribedExtinction.UniformBodyPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def rankOnePhysicalElectric (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : Field :=
  volumeTotalElectric k σ (bodyCurrentPolarization B (activeInjection B (basisR 0) (rotatedAxis θ)
    (activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ)))

theorem power_difference_triangle (x a X A t : ℝ) :
    |(x - a) - t * (X - A)| ≤ |x - t * X| + |a - t * A| := by
  have he : (x - a) - t * (X - A) = (x - t * X) - (a - t * A) := by ring
  rw [he]
  exact abs_sub _ _

theorem physicalRankOne_original_powers_uniform_aperture_localization (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ (B : TwoLayerBody), B.absorberThickness = h → B.plateThickness = d →
      R0 ≤ B.aperture → ∀ (σ : Direction) (θ : ℝ),
        |extinction k (rankOneBody B (basisR 0) (rotatedAxis θ) α β) σ
            (rankOnePhysicalElectric k hk B σ θ α β hα hβ) - B.aperture ^ 2 * (Real.sin θ) ^ 2 *
          planarNormalizedExtinction k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ| +
        |absorption k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
            (rankOnePhysicalElectric k hk B σ θ α β hα hβ) - B.aperture ^ 2 * (Real.sin θ) ^ 2 *
          planarNormalizedAbsorption k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ| +
        |scattering k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
            (rankOnePhysicalElectric k hk B σ θ α β hα hβ) - B.aperture ^ 2 * (Real.sin θ) ^ 2 *
          (planarNormalizedExtinction k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ -
           planarNormalizedAbsorption k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
            B.absorberThickness θ α β hα hβ)| ≤ ε * B.aperture ^ 2 * (Real.sin θ) ^ 2 := by
  obtain ⟨R0, hR0, he⟩ := physicalBody_normalized_powers_uniform_aperture_localization k hk h d hh hd α β hα hβ
    (ε / 2) (by positivity)
  refine ⟨R0, hR0, ?_⟩
  intro B hBh hBd hBR σ θ
  have hp := he B hBh hBd hBR σ θ
  let x := normalizedExtinction k hk B σ θ α β hα hβ
  let a := normalizedAbsorption k hk B σ θ α β hα hβ
  let X := planarNormalizedExtinction k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  let A := planarNormalizedAbsorption k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  let t := B.aperture ^ 2
  let s := (Real.sin θ) ^ 2
  change |x - t * X| + |a - t * A| ≤ ε / 2 * t at hp
  unfold rankOnePhysicalElectric
  rw [physicalExtinction_sine_squared_factorization, physicalAbsorption_sine_squared_factorization,
    physicalScattering_sine_squared_factorization]
  change |s * x - t * s * X| + |s * a - t * s * A| +
    |s * (x - a) - t * s * (X - A)| ≤ ε * t * s
  have hf (u v : ℝ) : s * u - t * s * v = s * (u - t * v) := by ring
  rw [hf, hf, hf, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hb := power_difference_triangle x a X A t
  have hsum : |x - t * X| + |a - t * A| + |(x - a) - t * (X - A)| ≤ ε * t := by linarith
  have hm := mul_le_mul_of_nonneg_left hsum (sq_nonneg (Real.sin θ))
  nlinarith

end OQ7Prescribed
