import PrescribedExtinction.NewtonHeat
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! The Fourier transform of the actual three-dimensional positive-time heat
kernel, with Mathlib's `exp(-2πi⟪x,ξ⟫)` normalization. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory
open scoped FourierTransform

theorem newtonHeatKernel_complex_gaussian (t : ℝ) (x : Position) :
    (newtonHeatKernel t x : ℂ) =
      ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) : ℝ) *
        Complex.exp (-(((4 * t)⁻¹ : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  simp only [newtonHeatKernel, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 1
  congr 1
  push_cast
  ring

theorem newtonHeatKernel_space_integrable_complex (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : Position => (newtonHeatKernel t x : ℂ)) volume := by
  have hb : 0 < ((((4 * t)⁻¹ : ℝ) : ℂ)).re := by simp; positivity
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Position) hb (0 : ℂ) (0 : Position)
  simp only [zero_mul, add_zero] at h
  have hc := h.const_mul (((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
  exact hc.congr (ae_of_all _ fun x => (newtonHeatKernel_complex_gaussian t x).symm)

theorem newtonHeatKernel_space_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (newtonHeatKernel t) volume := by
  have h := (newtonHeatKernel_space_integrable_complex t ht).re
  change Integrable (fun x : Position => Complex.re (newtonHeatKernel t x : ℂ)) volume at h
  simpa only [Complex.ofReal_re] using h

theorem newtonHeatKernel_fourier (t : ℝ) (ht : 0 < t) (ξ : Position) :
    𝓕 (fun x : Position => (newtonHeatKernel t x : ℂ)) ξ =
      Complex.exp ((-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  let c : ℂ := ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) : ℝ)
  let b : ℂ := ((4 * t)⁻¹ : ℝ)
  have hb : 0 < b.re := by simp [b]; positivity
  have he : (fun x : Position => (newtonHeatKernel t x : ℂ)) =
      c • (fun x : Position => Complex.exp (-b * (‖x‖ : ℂ) ^ 2)) := by
    funext x
    exact newtonHeatKernel_complex_gaussian t x
  rw [he]
  change VectorFourier.fourierIntegral _ _ _ (c • _) ξ = _
  rw [VectorFourier.fourierIntegral_const_smul]
  change c * (𝓕 (fun x : Position => Complex.exp (-b * (‖x‖ : ℂ) ^ 2)) ξ) = _
  rw [fourier_gaussian_innerProductSpace hb]
  have hd : Module.finrank ℝ Position = 3 := by simp [Position]
  rw [hd]
  norm_num only [Nat.cast_ofNat]
  have hπ : (Real.pi : ℂ) / b = ((4 * Real.pi * t : ℝ) : ℂ) := by
    dsimp [b]
    push_cast
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [hπ]
  have hp : ((4 * Real.pi * t : ℝ) : ℂ) ^ (3 / 2 : ℂ) =
      (((4 * Real.pi * t) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (by positivity : 0 ≤ 4 * Real.pi * t) (3 / 2 : ℝ)).symm
  rw [hp, ← mul_assoc]
  have hc : c * (((4 * Real.pi * t) ^ (3 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    dsimp [c]
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity : 0 < 4 * Real.pi * t)]
    norm_num
  rw [hc, one_mul]
  congr 1
  dsimp [b]
  push_cast
  simp only [div_eq_mul_inv, inv_inv]
  ring

theorem newtonHeatKernel_integral_one (t : ℝ) (ht : 0 < t) :
    (∫ x : Position, newtonHeatKernel t x) = 1 := by
  have h := newtonHeatKernel_fourier t ht (0 : Position)
  have hc : ((∫ x : Position, newtonHeatKernel t x : ℝ) : ℂ) = 1 := by
    simpa [Real.fourier_eq, integral_complex_ofReal] using h
  exact_mod_cast hc

end OQ7Prescribed
