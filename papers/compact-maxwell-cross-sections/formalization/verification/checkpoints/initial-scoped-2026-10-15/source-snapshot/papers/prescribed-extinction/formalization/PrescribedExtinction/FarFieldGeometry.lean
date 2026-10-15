import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace OQ7Prescribed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Uniform second-order distance error in every direction; no angular exclusion. -/
theorem displaced_distance_phase_error (x y : H) (hx : 0 < ‖x‖) (hy : 2 * ‖y‖ ≤ ‖x‖) :
    0 ≤ ‖x - y‖ - ‖x‖ + inner ℝ (‖x‖⁻¹ • x) y ∧
      ‖x - y‖ - ‖x‖ + inner ℝ (‖x‖⁻¹ • x) y ≤ ‖y‖ ^ 2 / ‖x‖ := by
  let t := inner ℝ (‖x‖⁻¹ • x) y
  have hn : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, hx.ne', abs_inv, abs_of_pos hx]
  have ht : |t| ≤ ‖y‖ := by simpa only [t, hn, one_mul] using abs_real_inner_le_norm (‖x‖⁻¹ • x) y
  have htlo := (abs_le.mp ht).1
  have hthi := (abs_le.mp ht).2
  have htip : inner ℝ x y = ‖x‖ * t := by
    dsimp [t]
    rw [real_inner_smul_left]
    field_simp
  have hsq : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ‖x‖ * t + ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, htip]
    ring
  have hs := norm_sub_norm_le x y
  have hsum : ‖x‖ ≤ ‖x - y‖ + ‖x‖ - t := by linarith
  have ht2 : t ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hprod : (‖x - y‖ - ‖x‖ + t) * (‖x - y‖ + ‖x‖ - t) = ‖y‖ ^ 2 - t ^ 2 := by nlinarith
  have hpos : 0 < ‖x - y‖ + ‖x‖ - t := hx.trans_le hsum
  have herror : 0 ≤ ‖x - y‖ - ‖x‖ + t := by nlinarith
  refine ⟨herror, ?_⟩
  apply (le_div_iff₀ hx).mpr
  nlinarith [mul_nonneg herror (sub_nonneg.mpr hsum)]

theorem displaced_inverse_amplitude_error (x y : H) (hx : 0 < ‖x‖) (hy : 2 * ‖y‖ ≤ ‖x‖) :
    |‖x‖ / ‖x - y‖ - 1| ≤ 2 * ‖y‖ / ‖x‖ := by
  have hs := norm_sub_norm_le x y
  have hp : 0 < ‖x - y‖ := by linarith
  have hab : |‖x‖ - ‖x - y‖| ≤ ‖y‖ := by simpa using abs_norm_sub_norm_le x (x - y)
  have he : ‖x‖ / ‖x - y‖ - 1 = (‖x‖ - ‖x - y‖) / ‖x - y‖ := by field_simp
  rw [he, abs_div, abs_of_pos hp]
  calc
    _ ≤ ‖y‖ / ‖x - y‖ := div_le_div_of_nonneg_right hab hp.le
    _ ≤ _ := by
      apply (div_le_div_iff₀ hp hx).mpr
      nlinarith [mul_nonneg (norm_nonneg y) (show 0 ≤ 2 * ‖x - y‖ - ‖x‖ by linarith)]

theorem purePhase_norm_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have he : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    have hh : Complex.I * (b : ℂ) + Complex.I * ((a - b : ℝ) : ℂ) = Complex.I * (a : ℂ) := by
      push_cast
      ring
    rw [hh, mul_one]
  rw [he, norm_mul, show ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 by simp [Complex.norm_exp], one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

end OQ7Prescribed
