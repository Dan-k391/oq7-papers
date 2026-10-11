import PrescribedExtinction.ApertureMeanSlope
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

def apertureRadialLift (w : ℂ → ℂ) (x : ℂ) (s t : ℝ) : ℂ :=
  apertureCircleJet 0 w x (Real.sqrt (t ^ 2 - s ^ 2))

def apertureRadialLiftDeriv (w : ℂ → ℂ) (x : ℂ) (s t : ℝ) : ℂ :=
  t • apertureMeanSlope w x (Real.sqrt (t ^ 2 - s ^ 2))

def apertureRadialLiftSecond (w : ℂ → ℂ) (x : ℂ) (s t : ℝ) : ℂ :=
  apertureMeanSlope w x (Real.sqrt (t ^ 2 - s ^ 2)) +
    (t ^ 2 / Real.sqrt (t ^ 2 - s ^ 2)) • apertureMeanSlopeDeriv w x (Real.sqrt (t ^ 2 - s ^ 2))

theorem apertureRadialRoot_pos (s t : ℝ) (ht : |s| < t) : 0 < Real.sqrt (t ^ 2 - s ^ 2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [abs_nonneg s, sq_abs s]

theorem apertureRadialRoot_hasDerivAt (s t : ℝ) (ht : |s| < t) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - s ^ 2))
      (t / Real.sqrt (t ^ 2 - s ^ 2)) t := by
  have hn : t ^ 2 - s ^ 2 ≠ 0 := by
    have hp := apertureRadialRoot_pos s t ht
    exact ne_of_gt (Real.sqrt_pos.mp hp)
  have he := (((hasDerivAt_id t).pow 2).sub_const (s ^ 2)).sqrt hn
  convert he using 1 <;> simp
  field_simp

theorem apertureRadialLift_continuous (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) (s : ℝ) : Continuous (apertureRadialLift w x s) := by
  have hj := apertureCircleJet_continuous 0 w hw x
  exact hj.comp ((continuous_id.pow 2).sub continuous_const).sqrt

theorem apertureRadialLiftDeriv_continuous (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) (s : ℝ) : Continuous (apertureRadialLiftDeriv w x s) :=
  continuous_id.smul ((apertureMeanSlope_continuous w hw x).comp
    ((continuous_id.pow 2).sub continuous_const).sqrt)

theorem apertureRadialLift_hasDerivAt (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (s t : ℝ) (ht : |s| < t) :
    HasDerivAt (apertureRadialLift w x s) (apertureRadialLiftDeriv w x s t) t := by
  have he := (apertureCircleJet_hasDerivAt 0 w hw hc x (Real.sqrt (t ^ 2 - s ^ 2))).scomp t
    (apertureRadialRoot_hasDerivAt s t ht)
  have hs := apertureMeanSlope_first_jet w hw hc x (Real.sqrt (t ^ 2 - s ^ 2))
  rw [← hs, smul_smul, div_mul_cancel₀ _ (apertureRadialRoot_pos s t ht).ne'] at he
  exact he

theorem apertureRadialLiftDeriv_hasDerivAt (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (s t : ℝ) (ht : |s| < t) :
    HasDerivAt (apertureRadialLiftDeriv w x s) (apertureRadialLiftSecond w x s t) t := by
  have he := (apertureMeanSlope_hasDerivAt w hw hc x (Real.sqrt (t ^ 2 - s ^ 2))).scomp t
    (apertureRadialRoot_hasDerivAt s t ht)
  have hh := (hasDerivAt_id t).smul he
  convert hh using 1
  · rfl
  · simp only [one_smul, smul_smul, apertureRadialLiftSecond, Function.comp_def, id_eq]
    rw [add_comm]
    congr 1
    congr 1
    ring

theorem apertureRadialLiftSecond_norm_le (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (s t C₂ C₄ : ℝ)
    (ht : |s| < t) (h₂ : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C₂)
    (h₄ : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C₄) :
    ‖apertureRadialLiftSecond w x s t‖ ≤ C₂ + t ^ 2 * C₄ / 3 := by
  have hr := apertureRadialRoot_pos s t ht
  unfold apertureRadialLiftSecond
  apply (norm_add_le _ _).trans
  apply add_le_add (apertureMeanSlope_norm_le w x _ C₂ h₂)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t ^ 2 / Real.sqrt (t ^ 2 - s ^ 2))]
  calc
    _ ≤ (t ^ 2 / Real.sqrt (t ^ 2 - s ^ 2)) * (C₄ * Real.sqrt (t ^ 2 - s ^ 2) / 3) :=
      mul_le_mul_of_nonneg_left (apertureMeanSlopeDeriv_norm_le w hw hc x _ C₄ hr.le h₄) (by positivity)
    _ = _ := by field_simp

theorem apertureRadialLift_at_lower (w : ℂ → ℂ) (x : ℂ) (s : ℝ) :
    apertureRadialLift w x s |s| = w x := by
  simp [apertureRadialLift, apertureCircleJet_zero]

theorem apertureRadialLiftDeriv_lower_norm_le (w : ℂ → ℂ) (x : ℂ) (s C : ℝ)
    (hC : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C) :
    ‖apertureRadialLiftDeriv w x s |s|‖ ≤ |s| * C := by
  rw [apertureRadialLiftDeriv, norm_smul, Real.norm_eq_abs, abs_abs]
  exact mul_le_mul_of_nonneg_left (apertureMeanSlope_norm_le w x _ C hC) (abs_nonneg _)

end OQ7Prescribed
