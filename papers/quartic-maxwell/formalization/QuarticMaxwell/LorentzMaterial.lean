import QuarticMaxwell.SphereResponse

/-! The literal Lorentz rational law in the original finite-sphere example:
all denominator zeros lie strictly below the real axis, the real positive
frequency loss is positive, and the operating-frequency value is exactly ij.
No time-domain causality theorem is inferred beyond these explicit claims. -/
noncomputable section
namespace QuarticMaxwell.LorentzMaterial

def denominator (ω0 γ : ℝ) (z : ℂ) : ℂ := (ω0 ^ 2 : ℝ) - z ^ 2 - Complex.I * (γ : ℂ) * z

def susceptibility (j ω0 γ : ℝ) (z : ℂ) : ℂ := ((j * γ * ω0 : ℝ) : ℂ) / denominator ω0 γ z

theorem pole_strictly_lower {ω0 γ : ℝ} (hω0 : 0 < ω0) (hγ : 0 < γ)
    (z : ℂ) (hz : denominator ω0 γ z = 0) : z.im < 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [denominator, Complex.mul_re, Complex.mul_im, pow_two] at hr hi
  by_contra hn
  have hy : 0 ≤ z.im := le_of_not_gt hn
  have hfac : 0 < 2 * z.im + γ := by linarith
  have hx : z.re = 0 := by
    have heq : z.re * (2 * z.im + γ) = 0 := by nlinarith only [hi]
    exact (mul_eq_zero.mp heq).resolve_right hfac.ne'
  rw [hx] at hr
  nlinarith [mul_nonneg hγ.le hy, sq_pos_of_pos hω0]

theorem denominator_ne_zero_real {ω0 γ : ℝ} (hω0 : 0 < ω0) (hγ : 0 < γ) (ω : ℝ) :
    denominator ω0 γ (ω : ℂ) ≠ 0 := by
  intro hz
  have h := pole_strictly_lower hω0 hγ (ω : ℂ) hz
  simp at h

theorem positive_frequency_imaginary (j ω0 γ ω : ℝ) :
    (susceptibility j ω0 γ (ω : ℂ)).im =
      j * γ ^ 2 * ω0 * ω / ((ω0 ^ 2 - ω ^ 2) ^ 2 + (γ * ω) ^ 2) := by
  simp [susceptibility, denominator, Complex.div_im, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem positive_frequency_loss {j ω0 γ ω : ℝ}
    (hj : 0 < j) (hω0 : 0 < ω0) (hγ : 0 < γ) (hω : 0 < ω) :
    0 < (susceptibility j ω0 γ (ω : ℂ)).im := by
  rw [positive_frequency_imaginary]
  have hgω : 0 < γ * ω := mul_pos hγ hω
  have hden : 0 < (ω0 ^ 2 - ω ^ 2) ^ 2 + (γ * ω) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hgω)
  exact div_pos (by positivity) hden

theorem operating_value (j : ℝ) {ω0 γ : ℝ} (hω0 : 0 < ω0) (hγ : 0 < γ) :
    susceptibility j ω0 γ (ω0 : ℂ) = (j : ℂ) * Complex.I := by
  unfold susceptibility
  apply (div_eq_iff (denominator_ne_zero_real hω0 hγ ω0)).mpr
  simp [denominator]
  ring_nf
  norm_num

end QuarticMaxwell.LorentzMaterial
