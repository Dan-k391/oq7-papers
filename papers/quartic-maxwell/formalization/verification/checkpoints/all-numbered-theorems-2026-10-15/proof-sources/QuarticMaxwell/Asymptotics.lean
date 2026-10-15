import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Quantitative coefficient and sharpness consequences

These lemmas prove the nontrivial division, absolute-value, and sharpness steps
from explicit error estimates. They do not assume the desired quartic error.
To prove manuscript Theorem 4.1 for Maxwell fields one still has to prove its
operator/moment expansions and identify the quantities used here.
-/

noncomputable section
namespace QuarticMaxwell

/-- Dividing a third-order signed-scattering remainder by a second-order
extinction remainder produces the sixth-order normalized remainder. The
absolute value also permits a vanishing leading coefficient. -/
theorem quartic_quotient_error {t s d N D B E : ℝ}
    (ht : 0 ≤ t) (hD : 0 < D) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hd : D / 2 ≤ d)
    (hs : |s - N * t| ≤ B * t ^ 3)
    (he : |d - D| ≤ E * t ^ 2) :
    |t ^ 3 * |s| / d - (|N| / D) * t ^ 4| ≤
      (2 * B / D + 2 * |N| * E / D ^ 2) * t ^ 6 := by
  have hd0 : 0 < d := by linarith
  have hnt : |N * t| = |N| * t := by rw [abs_mul, abs_of_nonneg ht]
  have hab : abs (abs s - abs N * t) ≤ B * t ^ 3 := by
    rw [← hnt]
    exact (abs_abs_sub_abs_le_abs_sub s (N * t)).trans hs
  have he' : |D - d| ≤ E * t ^ 2 := by simpa only [abs_sub_comm] using he
  have hden : d * D ≥ D ^ 2 / 2 := by nlinarith
  have hinv : 1 / d ≤ 2 / D := by
    rw [div_le_div_iff₀ hd0 hD]
    linarith
  have hinv2 : 1 / (d * D) ≤ 2 / D ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos hd0 hD) (sq_pos_of_pos hD)]
    nlinarith
  have hsplit : t ^ 3 * |s| / d - (|N| / D) * t ^ 4 =
      (t ^ 3 / d) * (|s| - |N| * t) +
        (|N| * t ^ 4 / (d * D)) * (D - d) := by
    field_simp
    ring
  rw [hsplit]
  calc
    _ ≤ |(t ^ 3 / d) * (|s| - |N| * t)| +
        |(|N| * t ^ 4 / (d * D)) * (D - d)| := abs_add_le _ _
    _ = (t ^ 3 / d) * abs (abs s - abs N * t) +
        (|N| * t ^ 4 / (d * D)) * |D - d| := by
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg (by positivity : 0 ≤ t ^ 3 / d),
        abs_of_nonneg (by positivity : 0 ≤ |N| * t ^ 4 / (d * D))]
    _ ≤ (t ^ 3 / d) * (B * t ^ 3) +
        (|N| * t ^ 4 / (d * D)) * (E * t ^ 2) := by gcongr
    _ = (B * t ^ 6) * (1 / d) + (|N| * E * t ^ 6) * (1 / (d * D)) := by ring
    _ ≤ (B * t ^ 6) * (2 / D) + (|N| * E * t ^ 6) * (2 / D ^ 2) := by gcongr
    _ = _ := by ring

/-- Positive coefficient plus a full remainder certificate gives an actual
quartic lower bound on the stated interval. -/
theorem positive_coefficient_lower_bound {Γ C c B t : ℝ}
    (_ht : 0 ≤ t) (hC : c ≤ C) (_hB : 0 ≤ B)
    (hrem : |Γ - C * t ^ 4| ≤ B * t ^ 6)
    (hsmall : B * t ^ 2 ≤ c / 2) : c / 2 * t ^ 4 ≤ Γ := by
  have herr := (abs_le.mp hrem).1
  have hscale : B * t ^ 6 ≤ c / 2 * t ^ 4 := by
    calc
      _ = (B * t ^ 2) * t ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)
  have hlead : c * t ^ 4 ≤ C * t ^ 4 :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  linarith

/-- The coefficient moment is invariant under a real change of origin. -/
theorem coefficient_translation_invariant {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (p₀ p₁ : H) (r : ℝ) :
    (inner ℂ p₀ (p₁ + (r : ℂ) • p₀)).im = (inner ℂ p₀ p₁).im := by
  rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [pow_two, Complex.mul_im]

end QuarticMaxwell
