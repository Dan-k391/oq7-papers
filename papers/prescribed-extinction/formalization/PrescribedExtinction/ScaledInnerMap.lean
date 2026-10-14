import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

noncomputable section
namespace OQ7Prescribed
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem continuousLinearMap_inner_of_norm_mul (J : E →L[ℂ] F) (R : ℝ)
    (hJ : ∀ q : E, ‖J q‖ = R * ‖q‖) (q r : E) :
    inner ℂ (J q) (J r) = (R ^ 2 : ℝ) • inner ℂ q r := by
  have h1 : J q + J r = J (q + r) := (map_add J q r).symm
  have h2 : J q - J r = J (q - r) := (map_sub J q r).symm
  have h3 : J q - (RCLike.I : ℂ) • J r = J (q - (RCLike.I : ℂ) • r) := by rw [map_sub, map_smul]
  have h4 : J q + (RCLike.I : ℂ) • J r = J (q + (RCLike.I : ℂ) • r) := by rw [map_add, map_smul]
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four,
    h1, h2, h3, h4, hJ, hJ, hJ, hJ]
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, Complex.real_smul, Complex.ofReal_pow]
  ring

theorem inner_quadratic_difference_norm_bound [CompleteSpace E] (M : E →L[ℂ] E) (r s : E) :
    ‖inner ℂ r (M r) - inner ℂ s (M s)‖ ≤ ‖M‖ * (‖r‖ + ‖s‖) * ‖r - s‖ := by
  have he : inner ℂ r (M r) - inner ℂ s (M s) =
      inner ℂ (r - s) (M r) + inner ℂ s (M (r - s)) := by
    rw [inner_sub_left (𝕜 := ℂ), map_sub, inner_sub_right (𝕜 := ℂ)]
    abel
  rw [he]
  have h1 := (norm_inner_le_norm (𝕜 := ℂ) (r - s) (M r)).trans
    (mul_le_mul_of_nonneg_left (M.le_opNorm r) (norm_nonneg (r - s)))
  have h2 := (norm_inner_le_norm (𝕜 := ℂ) s (M (r - s))).trans
    (mul_le_mul_of_nonneg_left (M.le_opNorm (r - s)) (norm_nonneg s))
  apply (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq _)
  ring

end OQ7Prescribed
