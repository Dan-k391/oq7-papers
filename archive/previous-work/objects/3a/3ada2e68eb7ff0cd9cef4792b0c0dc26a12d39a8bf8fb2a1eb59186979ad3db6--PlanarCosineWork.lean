import work.PlanarQuadraticKernel

noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped ComplexConjugate

theorem kernelQuadratic_real_rankOne (c : ℝ → ℝ) (q : ℝ → ℂ) :
    kernelQuadratic (fun p => (c p.1 * c p.2 : ℝ)) q =
      (Complex.normSq (∫ z : ℝ, (c z : ℂ) * q z) : ℂ) := by
  unfold kernelQuadratic
  rw [Complex.normSq_eq_conj_mul_self, ← integral_conj, Measure.volume_eq_prod, ← integral_prod_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring

theorem kernelQuadratic_cosine (k : ℝ) (q : ℝ → ℂ) (hq : Integrable q volume) :
    kernelQuadratic (fun p => (Real.cos (k * (p.1 - p.2)) : ℂ)) q =
      ((Complex.normSq (∫ z : ℝ, (Real.cos (k * z) : ℂ) * q z) +
        Complex.normSq (∫ z : ℝ, (Real.sin (k * z) : ℂ) * q z) : ℝ) : ℂ) := by
  have hcos : Integrable (fun p : ℝ × ℝ =>
      (Real.cos (k * p.1) * Real.cos (k * p.2) : ℝ) * conj (q p.1) * q p.2) volume :=
    kernelQuadratic_integrable _ q hq (by fun_prop) 1 (ae_of_all _ fun p => by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num))
  have hsin : Integrable (fun p : ℝ × ℝ =>
      (Real.sin (k * p.1) * Real.sin (k * p.2) : ℝ) * conj (q p.1) * q p.2) volume :=
    kernelQuadratic_integrable _ q hq (by fun_prop) 1 (ae_of_all _ fun p => by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num))
  have hsplit : kernelQuadratic (fun p => (Real.cos (k * (p.1 - p.2)) : ℂ)) q =
      kernelQuadratic (fun p => (Real.cos (k * p.1) * Real.cos (k * p.2) : ℝ)) q +
        kernelQuadratic (fun p => (Real.sin (k * p.1) * Real.sin (k * p.2) : ℝ)) q := by
    unfold kernelQuadratic
    rw [← integral_add hcos hsin]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by
      change (Real.cos (k * (p.1 - p.2)) : ℂ) * conj (q p.1) * q p.2 =
        (Real.cos (k * p.1) * Real.cos (k * p.2) : ℝ) * conj (q p.1) * q p.2 +
          (Real.sin (k * p.1) * Real.sin (k * p.2) : ℝ) * conj (q p.1) * q p.2
      rw [mul_sub, Real.cos_sub, Complex.ofReal_add]
      ring
  rw [hsplit, kernelQuadratic_real_rankOne (fun z => Real.cos (k * z)) q,
    kernelQuadratic_real_rankOne (fun z => Real.sin (k * z)) q, Complex.ofReal_add]

end OQ7Prescribed
