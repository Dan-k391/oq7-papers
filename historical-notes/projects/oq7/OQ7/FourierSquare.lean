import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OQ7.TwoPort

noncomputable section
namespace OQ7
open MeasureTheory Set

theorem sineSquare_difference_fourier (K x y : ℝ) :
    Real.sin (K * (y - x)) ^ 2 =
      (1 - Real.cos (2 * K * x) * Real.cos (2 * K * y) -
        Real.sin (2 * K * x) * Real.sin (2 * K * y)) / 2 := by
  have hd : 2 * (K * (y - x)) = 2 * K * y - 2 * K * x := by ring
  have hcos := Real.cos_two_mul (K * (y - x))
  rw [hd, Real.cos_sub] at hcos
  nlinarith [Real.sin_sq_add_cos_sq (K * (y - x))]

theorem sineSquare_squareIntegral {q : ℝ → ℝ} {a b K : ℝ}
    (hq : IntervalIntegrable q volume a b) :
    (∫ x in a..b, ∫ y in a..b, q x * q y * Real.sin (K * (y - x)) ^ 2) =
      ((∫ x in a..b, q x) ^ 2 -
        (∫ x in a..b, q x * Real.cos (2 * K * x)) ^ 2 -
        (∫ x in a..b, q x * Real.sin (2 * K * x)) ^ 2) / 2 := by
  let m : ℝ := ∫ x in a..b, q x
  let c : ℝ := ∫ x in a..b, q x * Real.cos (2 * K * x)
  let s : ℝ := ∫ x in a..b, q x * Real.sin (2 * K * x)
  have hc : Continuous (fun x : ℝ => Real.cos (2 * K * x)) := by fun_prop
  have hs : Continuous (fun x : ℝ => Real.sin (2 * K * x)) := by fun_prop
  have hqc := hq.mul_continuousOn hc.continuousOn
  have hqs := hq.mul_continuousOn hs.continuousOn
  have hinner : ∀ x : ℝ,
      (∫ y in a..b, q x * q y * Real.sin (K * (y - x)) ^ 2) =
        (q x * m - (q x * Real.cos (2 * K * x)) * c -
          (q x * Real.sin (2 * K * x)) * s) / 2 := by
    intro x
    calc
      _ = ∫ y in a..b,
          (q x * q y - (q x * Real.cos (2 * K * x)) *
            (q y * Real.cos (2 * K * y)) -
            (q x * Real.sin (2 * K * x)) * (q y * Real.sin (2 * K * y))) / 2 := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only
        rw [sineSquare_difference_fourier]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_sub
            ((hq.const_mul (q x)).sub (hqc.const_mul (q x * Real.cos (2 * K * x))))
            (hqs.const_mul (q x * Real.sin (2 * K * x))),
          intervalIntegral.integral_sub (hq.const_mul (q x))
            (hqc.const_mul (q x * Real.cos (2 * K * x))),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  calc
    _ = ∫ x in a..b, (q x * m - (q x * Real.cos (2 * K * x)) * c -
        (q x * Real.sin (2 * K * x)) * s) / 2 := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hinner x
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub ((hq.mul_const m).sub (hqc.mul_const c)) (hqs.mul_const s),
        intervalIntegral.integral_sub (hq.mul_const m) (hqc.mul_const c),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const]
      dsimp [m, c, s]
      ring

theorem fourierMoment_normSq_coordinates {q : ℝ → ℝ} {a b K : ℝ}
    (hq : IntervalIntegrable q volume a b) :
    Complex.normSq (∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)) =
      (∫ z in a..b, q z * Real.cos (2 * K * z)) ^ 2 +
      (∫ z in a..b, q z * Real.sin (2 * K * z)) ^ 2 := by
  have hqc : IntervalIntegrable (fun z => (q z : ℂ)) volume a b := ⟨hq.1.ofReal, hq.2.ofReal⟩
  have he : Continuous (fun z : ℝ => Complex.exp ((2 * K * z : ℝ) * Complex.I)) := by fun_prop
  have hMc := hqc.mul_continuousOn he.continuousOn
  have hre := intervalIntegral.intervalIntegral_re hMc
  have him := intervalIntegral.intervalIntegral_im hMc
  simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero] at hre
  simp only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero] at him
  rw [Complex.normSq_apply, ← hre, ← him]
  ring

theorem sineSquare_squareIntegral_fourier {q : ℝ → ℝ} {a b K : ℝ}
    (hq : IntervalIntegrable q volume a b) :
    (∫ x in a..b, ∫ y in a..b, q x * q y * Real.sin (K * (y - x)) ^ 2) =
      ((∫ x in a..b, q x) ^ 2 -
        Complex.normSq (∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I))) / 2 := by
  rw [sineSquare_squareIntegral hq, fourierMoment_normSq_coordinates hq]
  ring

#print axioms sineSquare_difference_fourier
#print axioms sineSquare_squareIntegral
#print axioms fourierMoment_normSq_coordinates
#print axioms sineSquare_squareIntegral_fourier
end OQ7
