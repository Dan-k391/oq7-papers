import QuarticMaxwell.SphereResponse

/-! Exact scalar response identities for the homogeneous finite-ball family. -/
noncomputable section
namespace QuarticMaxwell.HomogeneousScalars
open OQ7Prescribed SphereResponse

def contrast (μ : ℝ) : ℂ := Complex.I * (μ : ℂ)

theorem contrast_im (μ : ℝ) : (contrast μ).im = μ := by simp [contrast]
theorem contrast_norm {μ : ℝ} (hμ : 0 ≤ μ) : ‖contrast μ‖ = μ := by simp [contrast, Complex.norm_real, abs_of_nonneg hμ]

theorem beta_formula (μ : ℝ) :
    beta (contrast μ) = ⟨3 * μ ^ 2 / (9 + μ ^ 2), 9 * μ / (9 + μ ^ 2)⟩ := by
  have hd : (9 + μ ^ 2 : ℝ) ≠ 0 := by positivity
  have hc : (3 + contrast μ : ℂ) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [contrast] at he
  apply (div_eq_iff hc).mpr
  apply Complex.ext <;> simp [contrast, Complex.mul_re, Complex.mul_im]
  all_goals field_simp; ring

theorem beta_im (μ : ℝ) : (beta (contrast μ)).im = 9 * μ / (9 + μ ^ 2) := by rw [beta_formula]

theorem beta_im_pos {μ : ℝ} (hμ : 0 < μ) : 0 < (beta (contrast μ)).im := by
  rw [beta_im]
  positivity

theorem beta_norm_sq (μ : ℝ) : ‖beta (contrast μ)‖ ^ 2 = 9 * μ ^ 2 / (9 + μ ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply, beta_formula]
  have hd : (9 + μ ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem beta_norm_le_mu {μ : ℝ} (hμ : 0 ≤ μ) : ‖beta (contrast μ)‖ ≤ μ := by
  apply (sq_le_sq₀ (norm_nonneg _) hμ).mp
  rw [beta_norm_sq]
  apply (div_le_iff₀ (by positivity : 0 < 9 + μ ^ 2)).mpr
  nlinarith [sq_nonneg (μ ^ 2)]

theorem beta_norm_le_three (μ : ℝ) : ‖beta (contrast μ)‖ ≤ 3 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [beta_norm_sq]
  apply (div_le_iff₀ (by positivity : 0 < 9 + μ ^ 2)).mpr
  nlinarith

def leading (μ : ℝ) : ℝ := 2688 * Real.pi ^ 2 * μ ^ 3 / (9 + μ ^ 2) ^ 2

theorem leading_pos {μ : ℝ} (hμ : 0 < μ) : 0 < leading μ := by unfold leading; positivity

theorem beta_leading_factor (μ : ℝ) :
    ‖beta (contrast μ)‖ ^ 2 * (beta (contrast μ)).im = 81 * μ ^ 3 / (9 + μ ^ 2) ^ 2 := by
  rw [beta_norm_sq, beta_im]
  have hd : (9 + μ ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end QuarticMaxwell.HomogeneousScalars
