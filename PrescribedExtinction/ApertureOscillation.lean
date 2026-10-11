import PrescribedExtinction.GreenKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.CircleAverage

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def apertureOscillation (k t : ℝ) : ℂ := Complex.exp (Complex.I * (k * t : ℝ))

theorem apertureOscillation_norm (k t : ℝ) : ‖apertureOscillation k t‖ = 1 := by
  simp [apertureOscillation, Complex.norm_exp, Complex.mul_re]

theorem apertureOscillation_hasDerivAt (k t : ℝ) :
    HasDerivAt (apertureOscillation k) ((Complex.I * (k : ℂ)) * apertureOscillation k t) t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (k : ℂ)).const_mul Complex.I
  convert h.cexp using 1 <;> simp [apertureOscillation, Complex.ofReal_mul, mul_comm, mul_left_comm]
  funext x
  simp [apertureOscillation, Complex.ofReal_mul, mul_comm]

theorem apertureOscillation_continuous (k : ℝ) : Continuous (apertureOscillation k) := by
  unfold apertureOscillation
  fun_prop

theorem apertureOscillation_ibp (k a b : ℝ) (u du : ℝ → ℂ)
    (hu : ContinuousOn u (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt u (du t) t)
    (hdi : IntervalIntegrable du volume a b) :
    (Complex.I * (k : ℂ)) * (∫ t in a..b, u t * apertureOscillation k t) =
      u b * apertureOscillation k b - u a * apertureOscillation k a -
        ∫ t in a..b, du t * apertureOscillation k t := by
  have hc := apertureOscillation_continuous k
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hc.continuousOn
    hd (fun t _ => apertureOscillation_hasDerivAt k t) hdi
    ((continuous_const.mul hc).intervalIntegrable a b)
  rw [← he, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

private theorem apertureOscillation_algebra (c s a : ℂ) (hc : c ≠ 0) :
    c ^ 2 * (s + c⁻¹ * a) = c * (c * s + a) := by field_simp

theorem apertureOscillation_two_ibp (k a b : ℝ) (hk : k ≠ 0) (u du ddu : ℝ → ℂ)
    (hu : ContinuousOn u (uIcc a b)) (hdu : ContinuousOn du (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt u (du t) t)
    (hdd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt du (ddu t) t)
    (hddi : IntervalIntegrable ddu volume a b) (hb : u b = 0) (hdb : du b = 0) :
    (Complex.I * (k : ℂ)) ^ 2 *
      ((∫ t in a..b, u t * apertureOscillation k t) +
        (Complex.I * (k : ℂ))⁻¹ * u a * apertureOscillation k a) =
      du a * apertureOscillation k a + ∫ t in a..b, ddu t * apertureOscillation k t := by
  have hdi : IntervalIntegrable du volume a b := hdu.intervalIntegrable
  have h1 := apertureOscillation_ibp k a b u du hu hd hdi
  have h2 := apertureOscillation_ibp k a b du ddu hdu hdd hddi
  rw [hb, zero_mul, zero_sub] at h1
  rw [hdb, zero_mul, zero_sub] at h2
  have hn : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  calc
    _ = (Complex.I * (k : ℂ)) *
      ((Complex.I * (k : ℂ)) * (∫ t in a..b, u t * apertureOscillation k t) +
        u a * apertureOscillation k a) := by
          simpa only [mul_assoc] using apertureOscillation_algebra (Complex.I * (k : ℂ))
            (∫ t in a..b, u t * apertureOscillation k t) (u a * apertureOscillation k a) hn
    _ = -(Complex.I * (k : ℂ)) * (∫ t in a..b, du t * apertureOscillation k t) := by rw [h1]; ring
    _ = _ := by rw [neg_mul, h2]; ring

theorem apertureOscillation_error_bound (k a b : ℝ) (hk : 0 < k) (hab : a ≤ b)
    (u du ddu : ℝ → ℂ) (hu : ContinuousOn u (uIcc a b)) (hdu : ContinuousOn du (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt u (du t) t)
    (hdd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt du (ddu t) t)
    (hddi : IntervalIntegrable ddu volume a b) (hb : u b = 0) (hdb : du b = 0)
    (M : ℝ) (hM : ∀ t ∈ Ioc a b, ‖ddu t‖ ≤ M) :
    ‖(∫ t in a..b, u t * apertureOscillation k t) +
      (Complex.I * (k : ℂ))⁻¹ * u a * apertureOscillation k a‖ ≤
      (‖du a‖ + M * (b - a)) / k ^ 2 := by
  have he := congrArg norm (apertureOscillation_two_ibp k a b hk.ne' u du ddu hu hdu hd hdd hddi hb hdb)
  simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hk, one_mul] at he
  have hi : ‖∫ t in a..b, ddu t * apertureOscillation k t‖ ≤ M * (b - a) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => ddu t * apertureOscillation k t) (C := M) (fun t ht => by
        rw [norm_mul, apertureOscillation_norm, mul_one]
        exact hM t (by simpa only [uIoc_of_le hab] using ht))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hbound
  apply (le_div_iff₀ (sq_pos_of_pos hk)).mpr
  rw [mul_comm, he]
  exact (norm_add_le _ _).trans (by
    rw [norm_mul, apertureOscillation_norm, mul_one]
    exact add_le_add le_rfl hi)

end OQ7Prescribed
