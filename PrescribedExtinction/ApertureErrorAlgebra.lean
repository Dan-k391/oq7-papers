import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OQ7Prescribed

theorem aperture_error_le_of_window_and_radius (ε c G K e R : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hG : 0 < G) (hR : 0 ≤ R)
    (he : e ≤ ε * c / (4 * G)) (hr : 2 * K * G / (ε * c ^ 2) ≤ R) :
    (2 * R * e / c + K / c ^ 2) * G ≤ ε * R := by
  have he' : e * (4 * G) ≤ ε * c := (le_div_iff₀ (by positivity)).mp he
  have hr' : 2 * K * G ≤ R * (ε * c ^ 2) := (div_le_iff₀ (by positivity)).mp hr
  have hfirst : (2 * R * e / c) * G ≤ ε * R / 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hc).mpr
    have hm := mul_le_mul_of_nonneg_left he' hR
    nlinarith
  have hsecond : (K / c ^ 2) * G ≤ ε * R / 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith
  rw [add_mul]
  linarith

end OQ7Prescribed

