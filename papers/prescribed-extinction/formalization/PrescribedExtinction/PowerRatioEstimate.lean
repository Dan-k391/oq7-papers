import PrescribedExtinction.UniformBodyPowers

noncomputable section
namespace OQ7Prescribed

theorem normalizedPowerRatio_error_bound (n N y X c e : ℝ) (hc : 0 < c) (he : 0 ≤ e)
    (hy : c / 2 ≤ y) (hX : c ≤ X) (hN : 0 ≤ N) (hNX : N ≤ X)
    (hn : |n - N| ≤ 2 * e) (hden : |y - X| ≤ e) :
    |n / y - N / X| ≤ 6 * e / c := by
  have hyp : 0 < y := lt_of_lt_of_le (by linarith) hy
  have hXp : 0 < X := hc.trans_le hX
  have hnum : |n * X - N * y| ≤ 3 * e * X := by
    calc
      _ = |(n - N) * X + N * (X - y)| := by congr 1; ring
      _ ≤ |(n - N) * X| + |N * (X - y)| := abs_add_le _ _
      _ = |n - N| * X + N * |y - X| := by
        rw [abs_mul, abs_mul, abs_of_pos hXp, abs_of_nonneg hN, abs_sub_comm X y]
      _ ≤ (2 * e) * X + N * e := add_le_add (mul_le_mul_of_nonneg_right hn hXp.le)
        (mul_le_mul_of_nonneg_left hden hN)
      _ ≤ (2 * e) * X + X * e := add_le_add le_rfl (mul_le_mul_of_nonneg_right hNX he)
      _ = _ := by ring
  calc
    _ = |n * X - N * y| / (y * X) := by
      rw [div_sub_div _ _ hyp.ne' hXp.ne', abs_div, abs_of_pos (mul_pos hyp hXp)]
      rw [mul_comm y N]
    _ ≤ (3 * e * X) / (y * X) := div_le_div_of_nonneg_right hnum (mul_nonneg hyp.le hXp.le)
    _ = 3 * e / y := by field_simp
    _ ≤ 3 * e / (c / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hy
    _ = _ := by ring

theorem scaledPower_error_bound (x X t e : ℝ) (ht : 0 < t) (he : |x - t * X| ≤ e * t) :
    |x / t - X| ≤ e := by
  have hi : x / t - X = (x - t * X) / t := by field_simp
  rw [hi, abs_div, abs_of_pos ht]
  exact (div_le_iff₀ ht).mpr he

end OQ7Prescribed
