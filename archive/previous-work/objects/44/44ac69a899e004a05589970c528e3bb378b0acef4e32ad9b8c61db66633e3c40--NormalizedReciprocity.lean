import work.RotationContinuity
import PrescribedExtinction.ExtinctionReciprocity
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem rankOnePhysical_extinction_reciprocity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    extinction k (rankOneBody B u v α β) .plus
      (volumeTotalElectric k .plus (bodyCurrentPolarization B
        (activeInjection B u v (activePhysicalSolution k hk B .plus u v α β hα hβ)))) =
      extinction k (rankOneBody B u v α β) .minus
        (volumeTotalElectric k .minus (bodyCurrentPolarization B
          (activeInjection B u v (activePhysicalSolution k hk B .minus u v α β hα hβ)))) := by
  apply physicalVolume_extinction_reciprocity k hk
  · simp [rankOneBody, Matrix.transpose_add, Matrix.transpose_smul, rankOne_transpose]
  · simp [rankOneBody, Matrix.transpose_add, Matrix.transpose_smul, rankOne_transpose]
  · exact activePhysicalSolution_physicalVolumeEquation k hk B .plus u v α β hα hβ
  · exact activePhysicalSolution_physicalVolumeEquation k hk B .minus u v α β hα hβ

theorem normalizedExtinction_reciprocity_of_sine_ne_zero (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (θ : ℝ) (hθ : Real.sin θ ≠ 0) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedExtinction k hk B .plus θ α β hα hβ = normalizedExtinction k hk B .minus θ α β hα hβ := by
  have he := rankOnePhysical_extinction_reciprocity k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  rw [physicalExtinction_sine_squared_factorization, physicalExtinction_sine_squared_factorization] at he
  exact mul_left_cancel₀ (pow_ne_zero 2 hθ) he

theorem sine_ne_zero_dense : Dense {θ : ℝ | Real.sin θ ≠ 0} := by
  have hd := (countable_range (fun n : ℤ => (n : ℝ) * Real.pi)).dense_compl ℝ
  convert hd using 1
  ext θ
  simp [Real.sin_eq_zero_iff]

/-- The normalized physical extinction is common to both directions at every
angle, including zero. The proof uses continuous response, never sine division. -/
theorem normalizedExtinction_reciprocity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    normalizedExtinction k hk B .plus θ α β hα hβ = normalizedExtinction k hk B .minus θ α β hα hβ := by
  have he : EqOn (fun φ : ℝ => normalizedExtinction k hk B .plus φ α β hα hβ)
      (fun φ => normalizedExtinction k hk B .minus φ α β hα hβ) {φ | Real.sin φ ≠ 0} :=
    fun φ hφ => normalizedExtinction_reciprocity_of_sine_ne_zero k hk B φ hφ α β hα hβ
  exact he.closure (normalizedExtinction_continuous k hk B .plus α β hα hβ)
    (normalizedExtinction_continuous k hk B .minus α β hα hβ) (sine_ne_zero_dense θ)

end OQ7Prescribed
