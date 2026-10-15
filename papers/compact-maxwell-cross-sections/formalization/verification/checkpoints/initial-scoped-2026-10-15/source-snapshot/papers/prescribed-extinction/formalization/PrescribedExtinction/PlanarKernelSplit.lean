import PrescribedExtinction.PlanarHeightGreen
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace OQ7Prescribed
open MeasureTheory

def planarRealKernel (k s : ℝ) : ℝ := -(k / 2) * Real.sin (k * |s|)

theorem planarRealKernel_even (k s : ℝ) : planarRealKernel k (-s) = planarRealKernel k s := by
  simp [planarRealKernel]

theorem cos_mul_abs (k s : ℝ) : Real.cos (k * |s|) = Real.cos (k * s) := by
  by_cases h : 0 ≤ s
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), mul_neg, Real.cos_neg]

theorem planarScalarGreen_physical_split (k s : ℝ) (hk : k ≠ 0) :
    (k ^ 2 : ℝ) • planarScalarGreen k s =
      (planarRealKernel k s : ℂ) + Complex.I * (k / 2 * Real.cos (k * s) : ℝ) := by
  unfold planarScalarGreen apertureOscillation
  rw [mul_comm Complex.I _, Complex.exp_ofReal_mul_I, cos_mul_abs]
  simp only [Complex.real_smul,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, planarRealKernel, Complex.ofReal_neg]
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  field_simp
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

end OQ7Prescribed
