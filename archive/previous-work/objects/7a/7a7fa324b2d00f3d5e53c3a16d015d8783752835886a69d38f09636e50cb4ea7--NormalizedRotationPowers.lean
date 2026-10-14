import work.NormalizedWork
import work.NormalizedReciprocity

noncomputable section
namespace OQ7Prescribed
open Set

def normalizedRotationAsymmetry (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  |normalizedAbsorption k hk B .plus θ α β hα hβ -
    normalizedAbsorption k hk B .minus θ α β hα hβ| /
    normalizedExtinction k hk B .plus θ α β hα hβ

theorem normalizedExtinction_compact_lower_bound (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (s : Set ℝ) (hs : IsCompact s) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ s, c ≤ normalizedExtinction k hk B σ θ α β hα hβ :=
  hs.exists_forall_le' (normalizedExtinction_continuous k hk B σ α β hα hβ).continuousOn
    (fun θ _ => normalizedExtinction_pos k hk B σ θ α β hα hβ)

theorem normalizedRotationAsymmetry_continuous (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ : ℝ => normalizedRotationAsymmetry k hk B θ α β hα hβ) :=
  ((normalizedAbsorption_continuous k hk B .plus α β hα hβ).sub
    (normalizedAbsorption_continuous k hk B .minus α β hα hβ)).abs.div
    (normalizedExtinction_continuous k hk B .plus α β hα hβ)
    (fun θ => ne_of_gt (normalizedExtinction_pos k hk B .plus θ α β hα hβ))

theorem normalizedRotationAsymmetry_lt_one (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedRotationAsymmetry k hk B θ α β hα hβ < 1 := by
  apply (div_lt_one (normalizedExtinction_pos k hk B .plus θ α β hα hβ)).mpr
  apply abs_lt.mpr
  have hp := normalizedAbsorption_pos k hk B .plus θ α β hα hβ
  have hm := normalizedAbsorption_pos k hk B .minus θ α β hα hβ
  have hpl := normalizedAbsorption_le_extinction k hk B .plus θ α β hα hβ
  have hml := normalizedAbsorption_le_extinction k hk B .minus θ α β hα hβ
  have he := normalizedExtinction_reciprocity k hk B θ α β hα hβ
  constructor <;> linarith

theorem physicalAsymmetry_normalized_factorization (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (θ : ℝ) (hθ : Real.sin θ ≠ 0) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedAsymmetry k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
      (volumeTotalElectric k .plus (bodyCurrentPolarization B
        (activeInjection B (basisR 0) (rotatedAxis θ)
          (activePhysicalSolution k hk B .plus (basisR 0) (rotatedAxis θ) α β hα hβ))))
      (volumeTotalElectric k .minus (bodyCurrentPolarization B
        (activeInjection B (basisR 0) (rotatedAxis θ)
          (activePhysicalSolution k hk B .minus (basisR 0) (rotatedAxis θ) α β hα hβ)))) =
      normalizedRotationAsymmetry k hk B θ α β hα hβ := by
  unfold normalizedAsymmetry
  rw [physicalAbsorption_sine_squared_factorization, physicalAbsorption_sine_squared_factorization,
    physicalExtinction_sine_squared_factorization, ← mul_sub, abs_mul,
    abs_of_nonneg (sq_nonneg (Real.sin θ))]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hθ)

end OQ7Prescribed
