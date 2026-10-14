import PrescribedExtinction.UniformBodyResponse
import work.ScaledInnerMap
import PrescribedExtinction.NormalizedRotationPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem bodySharpScalarLift_inner (B : TwoLayerBody)
    (q r : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    inner ℂ (bodySharpScalarLift B q) (bodySharpScalarLift B r) =
      (B.aperture ^ 2 : ℝ) • inner ℂ q r :=
  continuousLinearMap_inner_of_norm_mul (bodySharpScalarLift B) B.aperture (bodySharpScalarLift_norm B) q r

theorem bodySharpScalarLift_inverse_material (B : TwoLayerBody) (α β : ℂ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    activeInverseMaterial B α β (bodySharpScalarLift B q) =
      bodySharpScalarLift B (planarInverseMaterial _ B.absorberThickness α β q) := by
  let J := bodySharpScalarLift B
  let M := planarInverseMaterial (B.absorberThickness + B.plateThickness) B.absorberThickness α β q
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [activeInverseMaterial_coe B α β (J q), bodySharpScalarLift_coe B q, bodySharpScalarLift_coe B M,
    slabHeight_quasiMeasurePreserving.ae (planarInverseMaterial_coe _ B.absorberThickness α β q)] with x hm hq hM hp
  change (activeInverseMaterial B α β (J q) : ScalarVolumeL2) x = (J M : ScalarVolumeL2) x
  change (J q : ScalarVolumeL2) x = _ at hq
  change (J M : ScalarVolumeL2) x = _ at hM
  change (M : HeightL2) (x 2) = _ at hp
  rw [hm, hq, hM]
  change (if x 2 < B.absorberThickness then α⁻¹ * (squareApertureWindow B.aperture (slabHorizontalCoordinate x) * (q : HeightL2) (x 2))
    else β⁻¹ * (squareApertureWindow B.aperture (slabHorizontalCoordinate x) * (q : HeightL2) (x 2))) =
      squareApertureWindow B.aperture (slabHorizontalCoordinate x) * (M : HeightL2) (x 2)
  rw [hp]
  by_cases hx : x 2 < B.absorberThickness <;> simp only [hx, ite_true, ite_false] <;> ring

def activeMaterialNormBound (α β : ℂ) : ℝ := max ‖α⁻¹‖ ‖β⁻¹‖

theorem activeInverseMaterial_norm_le (B : TwoLayerBody) (α β : ℂ) :
    ‖activeInverseMaterial B α β‖ ≤ activeMaterialNormBound α β := by
  have hc : 0 ≤ activeMaterialNormBound α β := (norm_nonneg _).trans (le_max_left _ _)
  apply (activeInverseMaterial B α β).opNorm_le_bound hc
  intro q
  change ‖(activeInverseMaterial B α β q : ScalarVolumeL2)‖ ≤ activeMaterialNormBound α β * ‖(q : ScalarVolumeL2)‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [activeInverseMaterial_coe B α β q] with x hx
  rw [hx]
  split_ifs <;> rw [norm_mul]
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem normalizedIncidentDrive_norm (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    ‖normalizedIncidentDrive k B σ‖ = B.aperture * Real.sqrt B.plateThickness := by
  rw [normalizedIncidentDrive_eq_sharpLift, bodySharpScalarLift_norm,
    planarNormalizedDrive_norm _ _ _ _ B.absorberThickness_pos.le (by linarith [B.plateThickness_pos])]
  congr 1
  ring

theorem normalizedExtinction_planar_lift_error_bound (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    |normalizedExtinction k hk B σ θ α β hα hβ - B.aperture ^ 2 *
      planarNormalizedExtinction k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
        B.absorberThickness θ α β hα hβ| ≤ k * B.aperture * Real.sqrt B.plateThickness *
          ‖normalizedActiveResponse k hk B σ θ α β hα hβ - bodySharpScalarLift B
            (planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ)‖ := by
  let g := planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness
  let q := planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  let r := normalizedActiveResponse k hk B σ θ α β hα hβ
  let J := bodySharpScalarLift B
  have hid : normalizedExtinction k hk B σ θ α β hα hβ - B.aperture ^ 2 *
      planarNormalizedExtinction k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ =
        k * (inner ℂ (normalizedIncidentDrive k B σ) (r - J q)).im := by
    unfold normalizedExtinction planarNormalizedExtinction
    rw [inner_sub_right (𝕜 := ℂ), normalizedIncidentDrive_eq_sharpLift,
      bodySharpScalarLift_inner]
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.sub_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    ring
  rw [hid, abs_mul, abs_of_pos hk]
  have hinner := (Complex.abs_im_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ)
    (normalizedIncidentDrive k B σ) (r - J q))
  rw [normalizedIncidentDrive_norm] at hinner
  exact (mul_le_mul_of_nonneg_left hinner hk.le).trans_eq (by ring)

end OQ7Prescribed
