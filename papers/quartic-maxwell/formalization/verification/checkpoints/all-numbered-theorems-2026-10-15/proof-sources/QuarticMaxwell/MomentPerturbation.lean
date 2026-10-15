import QuarticMaxwell.FixedPatternWork

/-! Generic inner-product perturbation and positive-small-parameter algebra.
The input norm/error estimates are explicit obligations; this module alone
makes no assertion about a Maxwell medium or a finite-sphere response. -/
noncomputable section
namespace QuarticMaxwell.MomentPerturbation

theorem imaginary_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p0 p1 a0 a1 : H) (L E0 E1 N0 N1 : ℝ)
    (hL : (inner ℂ a0 a1).im = L)
    (h0 : ‖p0 - a0‖ ≤ E0) (h1 : ‖p1 - a1‖ ≤ E1)
    (hN0 : ‖a0‖ ≤ N0) (hN1 : ‖p1‖ ≤ N1) :
    |(inner ℂ p0 p1).im - L| ≤ E0 * N1 + N0 * E1 := by
  have hE0 : 0 ≤ E0 := (norm_nonneg _).trans h0
  have hE1 : 0 ≤ E1 := (norm_nonneg _).trans h1
  have hN0' : 0 ≤ N0 := (norm_nonneg _).trans hN0
  rw [← hL]
  apply (FixedPatternWork.inner_im_error p0 p1 a0 a1).trans
  exact add_le_add (mul_le_mul h0 hN1 (norm_nonneg _) hE0)
    (mul_le_mul hN0 h1 (norm_nonneg _) hN0')

theorem imaginary_error_split {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p0 p1 a0 a1 : H) (L E0 Eaff E1 N0 N1 : ℝ)
    (hL : (inner ℂ a0 a1).im = L)
    (h0 : ‖p0 - a0‖ ≤ E0) (h1 : ‖p1 - a1‖ ≤ Eaff + E1)
    (hN0 : ‖a0‖ ≤ N0) (hN1 : ‖p1‖ ≤ N1) :
    |(inner ℂ p0 p1).im - L| ≤ E0 * N1 + N0 * (Eaff + E1) :=
  imaginary_error p0 p1 a0 a1 L E0 (Eaff + E1) N0 N1 hL h0 h1 hN0 hN1

theorem exists_small_square {A L K : ℝ} (hA : 0 < A) (hL : 0 < L) (hK : 0 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ a ≤ A ∧ K * a ^ 2 ≤ L / 2 := by
  let δ := Real.sqrt (L / (2 * (K + 1)))
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδ2 : δ ^ 2 = L / (2 * (K + 1)) := Real.sq_sqrt (by positivity)
  let a := min A δ
  have ha : 0 < a := lt_min hA hδ
  have haδ : a ≤ δ := min_le_right _ _
  have ha2 : a ^ 2 ≤ δ ^ 2 := (sq_le_sq₀ ha.le hδ.le).mpr haδ
  have heq : 2 * (K + 1) * δ ^ 2 = L := by rw [hδ2]; field_simp
  have hbound := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ 2 * (K + 1) by positivity)
  rw [heq] at hbound
  refine ⟨a, ha, min_le_left _ _, ?_⟩
  nlinarith only [hbound, sq_nonneg a]

theorem eleventh_order_enclosure {I L K a : ℝ}
    (ha : 0 < a) (hsmall : K * a ^ 2 ≤ L / 2)
    (herr : |I - L * a ^ 9| ≤ K * a ^ 11) :
    (L / 2) * a ^ 9 ≤ I ∧ I ≤ (3 * L / 2) * a ^ 9 := by
  have hbound : K * a ^ 11 ≤ (L / 2) * a ^ 9 := by
    convert mul_le_mul_of_nonneg_right hsmall (show 0 ≤ a ^ 9 by positivity) using 1
    ring
  have h := abs_le.mp (herr.trans hbound)
  constructor <;> linarith

theorem positive_from_eleventh_order_error {I L K a : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hsmall : K * a ^ 2 ≤ L / 2)
    (herr : |I - L * a ^ 9| ≤ K * a ^ 11) : 0 < I := by
  have h := (eleventh_order_enclosure ha hsmall herr).1
  exact lt_of_lt_of_le (by positivity) h

theorem exists_positive_from_uniform_error (I : ℝ → ℝ) {A L K : ℝ}
    (hA : 0 < A) (hL : 0 < L) (hK : 0 ≤ K)
    (herr : ∀ a : ℝ, 0 < a → a ≤ A → |I a - L * a ^ 9| ≤ K * a ^ 11) :
    ∃ a : ℝ, 0 < a ∧ a ≤ A ∧ 0 < I a := by
  obtain ⟨a, ha, hAa, hKa⟩ := exists_small_square hA hL hK
  exact ⟨a, ha, hAa, positive_from_eleventh_order_error ha hL hKa (herr a ha hAa)⟩

theorem higher_power_collapse {a E c11 c12 c14 c15 : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h12 : 0 ≤ c12) (h14 : 0 ≤ c14) (h15 : 0 ≤ c15)
    (herr : E ≤ c11 * a ^ 11 + c12 * a ^ 12 + c14 * a ^ 14 + c15 * a ^ 15) :
    E ≤ (c11 + c12 + c14 + c15) * a ^ 11 := by
  have hpow12 : a ^ 12 ≤ a ^ 11 := pow_le_pow_of_le_one ha ha1 (by decide)
  have hpow14 : a ^ 14 ≤ a ^ 11 := pow_le_pow_of_le_one ha ha1 (by decide)
  have hpow15 : a ^ 15 ≤ a ^ 11 := pow_le_pow_of_le_one ha ha1 (by decide)
  have hbound12 := mul_le_mul_of_nonneg_left hpow12 h12
  have hbound14 := mul_le_mul_of_nonneg_left hpow14 h14
  have hbound15 := mul_le_mul_of_nonneg_left hpow15 h15
  linarith

end QuarticMaxwell.MomentPerturbation
