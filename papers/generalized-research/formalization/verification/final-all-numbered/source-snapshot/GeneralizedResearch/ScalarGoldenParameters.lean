import GeneralizedResearch.ScalarContrast

/-! Equality in the scalar golden-ratio polynomial certificate. -/
noncomputable section
namespace GeneralizedResearch.ScalarGoldenParameters
open ScalarContrast

theorem equality_parameters {w d q σ : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d)
    (hq : 0 ≤ q) (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hbound : w + q ≤ 1)
    (hsq : d ^ 2 + σ ^ 2 = q ^ 2)
    (heq : 4 * w * d = 2 * gamma * (1 - σ)) :
    q = goldenQ ∧ w = 1 - goldenQ ∧ σ = goldenQ ^ 2 ∧ d = goldenD := by
  have hp := golden_properties
  have hg : 0 < gamma := hp.2.2.2.1
  have hright : 0 < 2 * gamma * (1 - σ) := by positivity
  have hdpos : 0 < d := by
    by_contra h
    have hz : d = 0 := le_antisymm (le_of_not_gt h) hd
    rw [hz, mul_zero] at heq
    linarith
  have hwpos : 0 < w := by
    by_contra h
    have hz : w = 0 := le_antisymm (le_of_not_gt h) hw
    rw [hz, mul_zero, zero_mul] at heq
    linarith
  have hq1 : q < 1 := by linarith
  have hub := golden_parameter_upper (by linarith : 0 ≤ 1 - q) hd hq hσ
    (by linarith : (1 - q) + q ≤ 1) hsq
  have hwq : w = 1 - q := by nlinarith
  have heq' : 2 * (1 - q) * d = gamma * (1 - σ) := by rw [hwq] at heq; linarith
  have hgap : gamma ^ 2 * (1 - σ) ^ 2 - 4 * (1 - q) ^ 2 * d ^ 2 = 0 := by
    nlinarith only [sq_nonneg (2 * (1 - q) * d - gamma * (1 - σ)),
      congrArg (fun x : ℝ => x ^ 2) heq']
  have hpoly := golden_polynomial_maximum hq
  have hfirst : 0 ≤ (gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q)) * (1 - σ) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hpoly) (sq_nonneg _)
  have hsecond : 0 ≤ 4 * (1 - q) * (σ - q ^ 2) ^ 2 := by positivity
  have hid : (1 + q) * (gamma ^ 2 * (1 - σ) ^ 2 - 4 * (1 - q) ^ 2 * d ^ 2) =
      (gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q)) * (1 - σ) ^ 2 +
        4 * (1 - q) * (σ - q ^ 2) ^ 2 := by
    linear_combination -(4 * (1 - q) ^ 2 * (1 + q)) * hsq
  have hzfirst : (gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q)) * (1 - σ) ^ 2 = 0 := by
    rw [hgap, mul_zero] at hid
    linarith
  have hzpoly : gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q) = 0 := by
    exact (mul_eq_zero.mp hzfirst).resolve_right (pow_ne_zero _ (by linarith))
  have hfactor : gamma ^ 2 * (1 + q) - 4 * q ^ 2 * (1 - q) =
      4 * (q - goldenQ) ^ 2 * (q + 2 * goldenQ - 1) := by
    rw [hp.2.2.2.2]
    linear_combination (4 * (3 + 3 * q - 2 * goldenQ)) * hp.2.2.1
  have hqeq : q = goldenQ := by
    rw [hfactor] at hzpoly
    have hpos : 0 < q + 2 * goldenQ - 1 := by linarith [hp.1]
    have hz : 4 * (q - goldenQ) ^ 2 = 0 :=
      (mul_eq_zero.mp hzpoly).resolve_right hpos.ne'
    nlinarith only [hz]
  have hzsecond : 4 * (1 - q) * (σ - q ^ 2) ^ 2 = 0 := by
    rw [hgap, mul_zero, hzfirst] at hid
    linarith
  have hσeq : σ = q ^ 2 := by
    have hz : (σ - q ^ 2) ^ 2 = 0 :=
      (mul_eq_zero.mp hzsecond).resolve_left
        (mul_pos (by norm_num : (0 : ℝ) < 4) (sub_pos.mpr hq1)).ne'
    nlinarith only [hz]
  have hge : goldenD ^ 2 = goldenQ ^ 2 * (1 - goldenQ ^ 2) := by
    unfold goldenD
    rw [mul_pow, Real.sq_sqrt (by nlinarith [hp.1, hp.2.1])]
  have hgd : 0 ≤ goldenD :=
    mul_nonneg (by linarith [hp.1]) (Real.sqrt_nonneg _)
  have hdeq : d = goldenD := by
    rw [hσeq, hqeq] at hsq
    nlinarith only [hsq, hge, hd, hgd]
  exact ⟨hqeq, by simpa only [hqeq] using hwq, by simpa only [hqeq] using hσeq, hdeq⟩

end GeneralizedResearch.ScalarGoldenParameters
