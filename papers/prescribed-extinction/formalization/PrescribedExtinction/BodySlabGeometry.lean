import PrescribedExtinction.BodyApertureWindow
import PrescribedExtinction.SlabObservationRegion

noncomputable section
namespace OQ7Prescribed
open Set

theorem horizontalSquareAperture_norm_le (R : ℝ) (hR : 0 < R) (z : ℂ)
    (hz : z ∈ horizontalSquareAperture R) : ‖z‖ ≤ R := by
  change -R / 2 < z.re ∧ z.re < R / 2 ∧ -R / 2 < z.im ∧ z.im < R / 2 at hz
  have hr : z.re ^ 2 ≤ (R / 2) ^ 2 := by nlinarith [hz.1, hz.2.1]
  have hi : z.im ^ 2 ≤ (R / 2) ^ 2 := by nlinarith [hz.2.2.1, hz.2.2.2]
  nlinarith [Complex.sq_norm z, Complex.normSq_apply z, norm_nonneg z]

theorem bodyDomain_subset_slabObservation (B : TwoLayerBody) :
    B.domain ⊆ slabObservationRegion B.aperture (B.absorberThickness + B.plateThickness + 2) := by
  intro x hx
  change x ∈ squareAperture B.aperture ∧ 0 < x 2 ∧ x 2 < B.absorberThickness + B.plateThickness at hx
  apply (slabObservationRegion_mem_iff _ _ _).mpr
  exact ⟨horizontalSquareAperture_norm_le B.aperture B.aperture_pos _
    ((horizontalSquareAperture_physical _ _).mpr hx.1), hx.2.1.le, by linarith [hx.2.2]⟩

theorem slabPosition_one : slabPosition (1 : ℂ) 0 = basisR 0 := by
  ext i
  fin_cases i <;> simp [slabPosition, basisR]

theorem slabPosition_I : slabPosition Complex.I 0 = basisR 1 := by
  ext i
  fin_cases i <;> simp [slabPosition, basisR]

theorem axisCoupling_add (u : Position) (v w : Vector) :
    axisCoupling u (v + w) = axisCoupling u v + axisCoupling u w := by
  simp [axisCoupling, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

theorem axisCoupling_rotatedAxis (θ : ℝ) (v : Vector) :
    axisCoupling (rotatedAxis θ) v =
      (Real.cos θ : ℂ) * axisCoupling (slabPosition 1 0) v +
        (Real.sin θ : ℂ) * axisCoupling (slabPosition Complex.I 0) v := by
  simp [axisCoupling, rotatedAxis, slabPosition, Fin.sum_univ_succ]

end OQ7Prescribed

