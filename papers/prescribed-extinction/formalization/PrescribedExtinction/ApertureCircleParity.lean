import PrescribedExtinction.ApertureCircleJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem apertureCircleJet_neg (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r : ℝ) :
    apertureCircleJet n w x (-r) = (-1 : ℂ) ^ n * apertureCircleJet n w x r := by
  induction n generalizing r with
  | zero => simp [apertureCircleJet_zero]
  | succ n ih =>
    have hl := (apertureCircleJet_hasDerivAt n w hw hc x (-r)).scomp r ((hasDerivAt_id r).neg)
    have hr := (apertureCircleJet_hasDerivAt n w hw hc x r).const_mul ((-1 : ℂ) ^ n)
    have hf : (apertureCircleJet n w x) ∘ (fun t : ℝ => -t) =
        fun t => (-1 : ℂ) ^ n * apertureCircleJet n w x t := by funext t; exact ih t
    rw [hf] at hl
    have he := hl.unique hr
    simp only [neg_smul, one_smul] at he
    have hn := congrArg Neg.neg he
    simp only [neg_neg] at hn
    rw [hn, pow_succ]
    ring

theorem apertureCircleJet_first_zero (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) :
    apertureCircleJet 1 w x 0 = 0 := by
  have he := apertureCircleJet_neg 1 w hw hc x 0
  exact CharZero.eq_neg_self_iff.mp (by simpa using he)

theorem apertureCircleJet_third_zero (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) :
    apertureCircleJet 3 w x 0 = 0 := by
  have he := apertureCircleJet_neg 3 w hw hc x 0
  norm_num at he
  exact CharZero.eq_neg_self_iff.mp he

theorem apertureCircleJet_third_norm_le (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r C : ℝ)
    (hr : 0 ≤ r) (hC : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C) :
    ‖apertureCircleJet 3 w x r‖ ≤ C * r := by
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := r) (f := apertureCircleJet 3 w x) (f' := apertureCircleJet 4 w x)
    (fun t _ => (apertureCircleJet_hasDerivAt 3 w hw hc x t).hasDerivWithinAt)
    (fun t _ => apertureCircleJet_norm_le 4 w x t C hC) r ⟨hr, le_rfl⟩
  simpa only [apertureCircleJet_third_zero w hw hc x, sub_zero] using he

theorem apertureCircleJet_first_norm_le (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r C : ℝ)
    (hr : 0 ≤ r) (hC : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C) :
    ‖apertureCircleJet 1 w x r‖ ≤ C * r := by
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := r) (f := apertureCircleJet 1 w x) (f' := apertureCircleJet 2 w x)
    (fun t _ => (apertureCircleJet_hasDerivAt 1 w hw hc x t).hasDerivWithinAt)
    (fun t _ => apertureCircleJet_norm_le 2 w x t C hC) r ⟨hr, le_rfl⟩
  simpa only [apertureCircleJet_first_zero w hw hc x, sub_zero] using he

end OQ7Prescribed
