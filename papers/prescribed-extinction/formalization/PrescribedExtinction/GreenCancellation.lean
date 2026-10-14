import PrescribedExtinction.OutgoingRadial
import Mathlib.Analysis.Complex.Exponential

/-! Exact second-order cancellations in the dynamic-minus-static Green kernel.
The estimates are global complex Taylor estimates; no radiation or Maxwell
identity is used. -/
noncomputable section
namespace OQ7Prescribed

theorem exp_remainder_two_norm (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  simpa [Finset.sum_range_succ, sub_sub] using
    Complex.norm_exp_sub_sum_le_norm_mul_exp z 2

theorem green_first_cancel_norm (z : ℂ) :
    ‖Complex.exp z * (z - 1) + 1‖ ≤
      ‖z‖ ^ 2 * (1 + (‖z‖ + 1) * Real.exp ‖z‖) := by
  have he : Complex.exp z * (z - 1) + 1 =
      z ^ 2 + (Complex.exp z - 1 - z) * (z - 1) := by ring
  rw [he]
  calc
    _ ≤ ‖z ^ 2‖ + ‖(Complex.exp z - 1 - z) * (z - 1)‖ := norm_add_le _ _
    _ = ‖z‖ ^ 2 + ‖Complex.exp z - 1 - z‖ * ‖z - 1‖ := by rw [norm_pow, norm_mul]
    _ ≤ ‖z‖ ^ 2 + (‖z‖ ^ 2 * Real.exp ‖z‖) * (‖z‖ + 1) := by
      gcongr
      · exact exp_remainder_two_norm z
      · simpa using norm_sub_le z 1
    _ = _ := by ring

theorem green_second_poly_norm (z : ℂ) :
    ‖z ^ 2 - 3 * z + 3‖ ≤ ‖z‖ ^ 2 + 3 * ‖z‖ + 3 := by
  calc
    _ ≤ ‖z ^ 2 - 3 * z‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
    _ ≤ (‖z ^ 2‖ + ‖3 * z‖) + ‖(3 : ℂ)‖ := by gcongr; exact norm_sub_le _ _
    _ = _ := by simp [norm_pow]

theorem green_second_cancel_norm (z : ℂ) :
    ‖Complex.exp z * (z ^ 2 - 3 * z + 3) - 3‖ ≤
      ‖z‖ ^ 2 * (‖z‖ + 2 + (‖z‖ ^ 2 + 3 * ‖z‖ + 3) * Real.exp ‖z‖) := by
  have he : Complex.exp z * (z ^ 2 - 3 * z + 3) - 3 =
      z ^ 2 * (z - 2) + (Complex.exp z - 1 - z) * (z ^ 2 - 3 * z + 3) := by ring
  rw [he]
  calc
    _ ≤ ‖z ^ 2 * (z - 2)‖ + ‖(Complex.exp z - 1 - z) * (z ^ 2 - 3 * z + 3)‖ := norm_add_le _ _
    _ = ‖z‖ ^ 2 * ‖z - 2‖ + ‖Complex.exp z - 1 - z‖ * ‖z ^ 2 - 3 * z + 3‖ := by
      rw [norm_mul, norm_pow, norm_mul]
    _ ≤ ‖z‖ ^ 2 * (‖z‖ + 2) + (‖z‖ ^ 2 * Real.exp ‖z‖) *
        (‖z‖ ^ 2 + 3 * ‖z‖ + 3) := by
      gcongr
      · simpa using norm_sub_le z 2
      · exact exp_remainder_two_norm z
      · exact green_second_poly_norm z
    _ = _ := by ring

end OQ7Prescribed
