import QuarticMaxwell.Asymptotics

/-! Sixth-order quotient error using actual common lower bounds on both
denominators. The input cubic/quadratic errors are separate obligations. -/
namespace QuarticMaxwell
theorem quartic_quotient_error_of_lower_bound {t s d N D B E L : ℝ}
    (ht : 0 ≤ t) (hL : 0 < L) (hd : L ≤ d) (hD : L ≤ D)
    (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hs : |s - N * t| ≤ B * t ^ 3) (he : |d - D| ≤ E * t ^ 2) :
    |t ^ 3 * |s| / d - (|N| / D) * t ^ 4| ≤
      (B / L + |N| * E / L ^ 2) * t ^ 6 := by
  have hd0 : 0 < d := lt_of_lt_of_le hL hd
  have hD0 : 0 < D := lt_of_lt_of_le hL hD
  have hab : abs (abs s - abs N * t) ≤ B * t ^ 3 := by
    have heq : |N * t| = |N| * t := by rw [abs_mul, abs_of_nonneg ht]
    rw [← heq]
    exact (abs_abs_sub_abs_le_abs_sub s (N * t)).trans hs
  have he' : |D - d| ≤ E * t ^ 2 := by simpa only [abs_sub_comm] using he
  have hden : L ^ 2 ≤ d * D := by
    simpa only [pow_two] using mul_le_mul hd hD hL.le hd0.le
  have hinv := one_div_le_one_div_of_le hL hd
  have hinv2 := one_div_le_one_div_of_le (sq_pos_of_pos hL) hden
  have hsplit : t ^ 3 * |s| / d - (|N| / D) * t ^ 4 =
      (t ^ 3 / d) * (|s| - |N| * t) + (|N| * t ^ 4 / (d * D)) * (D - d) := by
    field_simp
    ring
  rw [hsplit]
  calc
    _ ≤ |(t ^ 3 / d) * (|s| - |N| * t)| +
        |(|N| * t ^ 4 / (d * D)) * (D - d)| := abs_add_le _ _
    _ = (t ^ 3 / d) * abs (abs s - abs N * t) + (|N| * t ^ 4 / (d * D)) * |D - d| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ t ^ 3 / d),
        abs_of_nonneg (by positivity : 0 ≤ |N| * t ^ 4 / (d * D))]
    _ ≤ (t ^ 3 / d) * (B * t ^ 3) + (|N| * t ^ 4 / (d * D)) * (E * t ^ 2) := by gcongr
    _ = (B * t ^ 6) * (1 / d) + (|N| * E * t ^ 6) * (1 / (d * D)) := by ring
    _ ≤ (B * t ^ 6) * (1 / L) + (|N| * E * t ^ 6) * (1 / L ^ 2) := by gcongr
    _ = _ := by ring
end QuarticMaxwell
