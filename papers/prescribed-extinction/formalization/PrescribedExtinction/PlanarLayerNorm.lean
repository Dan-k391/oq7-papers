import PrescribedExtinction.PlanarLayerCompression

noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem planarLayerAxisMap_norm_le (L h a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (q : PlanarCurrentL2 L) : ‖planarLayerAxisMap L h a b q‖ ≤ ‖q‖ := by
  change ‖(planarLayerAxisMap L h a b q : HeightL2)‖ ≤ ‖(q : HeightL2)‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [planarLayerAxisMap_coe L h a b q] with z hz
  rw [hz]
  split_ifs <;> rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  · exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_eq (one_mul _)
  · exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

theorem planarActiveAxisMaps_norm_le (L h θ : ℝ) (q : PlanarCurrentL2 L) :
    ‖planarLayerAxisMap L h 1 (Real.cos θ) q‖ ≤ ‖q‖ ∧
      ‖planarLayerAxisMap L h 0 (Real.sin θ) q‖ ≤ ‖q‖ :=
  ⟨planarLayerAxisMap_norm_le L h 1 (Real.cos θ) (by norm_num) (Real.abs_cos_le_one θ) q,
    planarLayerAxisMap_norm_le L h 0 (Real.sin θ) (by norm_num) (Real.abs_sin_le_one θ) q⟩

end OQ7Prescribed
