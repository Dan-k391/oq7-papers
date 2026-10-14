import PrescribedExtinction.PlanarKernelSplit
import PrescribedExtinction.PlanarCosineWork

noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped ComplexConjugate

theorem kernelQuadratic_planar_im (k : ℝ) (hk : 0 < k) (q : ℝ → ℂ) (hq : Integrable q volume) :
    (kernelQuadratic (fun p => (k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) q).im =
      (k / 2) * (Complex.normSq (∫ z : ℝ, (Real.cos (k * z) : ℂ) * q z) +
        Complex.normSq (∫ z : ℝ, (Real.sin (k * z) : ℂ) * q z)) := by
  have hr : Integrable (fun p : ℝ × ℝ => (planarRealKernel k (p.1 - p.2) : ℂ) * conj (q p.1) * q p.2) volume :=
    kernelQuadratic_integrable _ q hq (by unfold planarRealKernel; fun_prop) (|k / 2|)
      (ae_of_all _ fun p => by
        simp only [Complex.norm_real, Real.norm_eq_abs, planarRealKernel, abs_mul, abs_neg]
        exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq (mul_one _))
  have hc : Integrable (fun p : ℝ × ℝ => (Real.cos (k * (p.1 - p.2)) : ℂ) * conj (q p.1) * q p.2) volume :=
    kernelQuadratic_integrable _ q hq (by fun_prop) 1
      (ae_of_all _ fun p => by simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (k * (p.1 - p.2)))
  have hsplit : kernelQuadratic (fun p => (k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) q =
      kernelQuadratic (fun p => (planarRealKernel k (p.1 - p.2) : ℂ)) q +
        (Complex.I * (k / 2 : ℝ)) * kernelQuadratic (fun p => (Real.cos (k * (p.1 - p.2)) : ℂ)) q := by
    unfold kernelQuadratic
    rw [← integral_const_mul, ← integral_add hr (hc.const_mul _)]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by
      change ((k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) * conj (q p.1) * q p.2 =
        (planarRealKernel k (p.1 - p.2) : ℂ) * conj (q p.1) * q p.2 +
          (Complex.I * (k / 2 : ℝ)) * ((Real.cos (k * (p.1 - p.2)) : ℂ) * conj (q p.1) * q p.2)
      rw [planarScalarGreen_physical_split k _ hk.ne']
      simp only [Complex.ofReal_mul]
      ring
  have hreal := kernelQuadratic_real_symmetric (fun p : ℝ × ℝ => planarRealKernel k (p.1 - p.2)) q
    (fun p => by change planarRealKernel k (p.2 - p.1) = _; rw [← neg_sub, planarRealKernel_even])
  rw [hsplit, Complex.add_im, hreal, kernelQuadratic_cosine k q hq]
  simp [Complex.mul_im, Complex.mul_re]

theorem kernelQuadratic_planar_im_nonneg (k : ℝ) (hk : 0 < k) (q : ℝ → ℂ) (hq : Integrable q volume) :
    0 ≤ (kernelQuadratic (fun p => (k ^ 2 : ℝ) • planarScalarGreen k (p.1 - p.2)) q).im := by
  rw [kernelQuadratic_planar_im k hk q hq]
  exact mul_nonneg (by positivity) (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

end OQ7Prescribed
