import work.BodySharpWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem normalizedAbsorption_planar_lift_error_bound (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    |normalizedAbsorption k hk B σ θ α β hα hβ - B.aperture ^ 2 *
      planarNormalizedAbsorption k hk σ (B.absorberThickness + B.plateThickness) (bodyHeight_pos B).le
        B.absorberThickness θ α β hα hβ| ≤
          (2 * k * activeMaterialNormBound α β / activeMaterialCoercivity α β) *
            B.aperture * Real.sqrt B.plateThickness *
              ‖normalizedActiveResponse k hk B σ θ α β hα hβ - bodySharpScalarLift B
                (planarNormalizedResponse k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ)‖ := by
  let r := normalizedActiveResponse k hk B σ θ α β hα hβ
  let q := planarNormalizedResponse k hk σ (B.absorberThickness + B.plateThickness)
    (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  let J := bodySharpScalarLift B
  let M := activeInverseMaterial B α β
  let c := activeMaterialCoercivity α β
  let C := activeMaterialNormBound α β
  have hc : 0 < c := activeMaterialCoercivity_pos α β hα hβ
  have hC : 0 ≤ C := (norm_nonneg _).trans (le_max_left _ _)
  have hsq : inner ℂ (J q) (M (J q)) = (B.aperture ^ 2 : ℝ) •
      inner ℂ q (planarInverseMaterial _ B.absorberThickness α β q) := by
    rw [bodySharpScalarLift_inverse_material, bodySharpScalarLift_inner]
  have hid : normalizedAbsorption k hk B σ θ α β hα hβ - B.aperture ^ 2 *
      planarNormalizedAbsorption k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ =
        -k * (inner ℂ r (M r) - inner ℂ (J q) (M (J q))).im := by
    rw [hsq]
    unfold normalizedAbsorption planarNormalizedAbsorption
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.sub_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    ring
  have hr := normalizedActiveResponse_norm_le k hk B σ θ α β hα hβ
  rw [normalizedIncidentDrive_norm] at hr
  change ‖r‖ ≤ (1 / c) * (B.aperture * Real.sqrt B.plateThickness) at hr
  have hq := planarNormalizedResponse_norm_le k hk σ _ (bodyHeight_pos B).le B.absorberThickness θ α β hα hβ
  rw [planarNormalizedDrive_norm _ _ _ _ B.absorberThickness_pos.le (by linarith [B.plateThickness_pos])] at hq
  have hh : B.absorberThickness + B.plateThickness - B.absorberThickness = B.plateThickness := by ring
  rw [hh] at hq
  change ‖q‖ ≤ (1 / c) * Real.sqrt B.plateThickness at hq
  have hj : ‖J q‖ ≤ (1 / c) * (B.aperture * Real.sqrt B.plateThickness) := by
    rw [bodySharpScalarLift_norm]
    exact (mul_le_mul_of_nonneg_left hq B.aperture_pos.le).trans_eq (by ring)
  have hs : ‖r‖ + ‖J q‖ ≤ 2 * (1 / c) * (B.aperture * Real.sqrt B.plateThickness) := by linarith
  have hnorm := (inner_quadratic_difference_norm_bound M r (J q)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul (activeInverseMaterial_norm_le B α β) hs (by positivity) hC) (norm_nonneg _))
  rw [hid, abs_mul, abs_neg, abs_of_pos hk]
  have him := (Complex.abs_im_le_norm _).trans hnorm
  exact (mul_le_mul_of_nonneg_left him hk.le).trans_eq (by dsimp only [C, c]; ring)

end OQ7Prescribed
