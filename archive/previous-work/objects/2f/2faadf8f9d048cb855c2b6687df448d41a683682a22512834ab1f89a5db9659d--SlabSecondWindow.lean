import work.SlabDerivatives
import PrescribedExtinction.SlabScaledEstimate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def apertureWindowSecond (w : ℂ → ℂ) (u v : ℂ) : ℂ → ℂ :=
  apertureWindowPartial (apertureWindowPartial w u) v

theorem apertureWindowSecond_contDiff (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (u v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (apertureWindowSecond w u v) :=
  apertureWindowPartial_contDiff _ (apertureWindowPartial_contDiff w hw u) v

theorem apertureWindowSecond_hasCompactSupport (w : ℂ → ℂ) (hc : HasCompactSupport w) (u v : ℂ) :
    HasCompactSupport (apertureWindowSecond w u v) :=
  apertureWindowPartial_hasCompactSupport _ (apertureWindowPartial_hasCompactSupport w hc u) v

theorem apertureWindowSecond_support (w : ℂ → ℂ) (u v : ℂ) :
    tsupport (apertureWindowSecond w u v) ⊆ tsupport w :=
  (apertureWindowPartial_support _ v).trans (apertureWindowPartial_support w u)

theorem apertureWindowSecond_jet_norm_le (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (apertureWindowSecond w u v) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 2) w x‖ := by
  apply (apertureWindowPartial_jet_norm_le n _ (apertureWindowPartial_contDiff w hw u) x v).trans
  calc
    _ ≤ ‖v‖ * (‖u‖ * ‖iteratedFDeriv ℝ (n + 1 + 1) w x‖) := by
      gcongr
      exact apertureWindowPartial_jet_norm_le (n + 1) w hw x u
    _ ≤ 1 * (1 * ‖iteratedFDeriv ℝ (n + 2) w x‖) := by
      gcongr
    _ = _ := by ring

theorem scaledApertureWindow_second_jetBound (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (R C : ℝ) (hR : 0 < R)
    (hC : ∀ y, ‖iteratedFDeriv ℝ (n + 2) w y‖ ≤ C)
    (u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ∀ x, ‖iteratedFDeriv ℝ n (apertureWindowSecond (scaledApertureWindow w R) u v) x‖ ≤
      C / R ^ (n + 2) := by
  intro x
  exact (apertureWindowSecond_jet_norm_le n _ (scaledApertureWindow_contDiff w hw R) x u v hu hv).trans
    (scaledApertureWindow_jetBound (n + 2) w hw R C hR hC x)

end OQ7Prescribed
