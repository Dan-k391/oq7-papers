import PrescribedExtinction.SlabConvolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Convolution

def apertureWindowPartial (w : ℂ → ℂ) (v : ℂ) : ℂ → ℂ := fun x => fderiv ℝ w x v

theorem apertureWindowPartial_contDiff (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (apertureWindowPartial w v) :=
  (hw.fderiv_right (by simp)).clm_apply contDiff_const

theorem apertureWindowPartial_support (w : ℂ → ℂ) (v : ℂ) :
    tsupport (apertureWindowPartial w v) ⊆ tsupport w :=
  (tsupport_comp_subset (g := fun D : ℂ →L[ℝ] ℂ => D v) rfl _).trans (tsupport_fderiv_subset ℝ)

theorem apertureWindowPartial_hasCompactSupport (w : ℂ → ℂ) (hc : HasCompactSupport w) (v : ℂ) :
    HasCompactSupport (apertureWindowPartial w v) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (apertureWindowPartial_support w v)

theorem horizontalSlabPotential_contDiff (k s : ℝ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞) (horizontalSlabPotential k s w) := by
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (slabGreen_locallyIntegrable k s) hw

theorem horizontalSlabPotential_partial (k s : ℝ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x v : ℂ) :
    fderiv ℝ (horizontalSlabPotential k s w) x v =
      horizontalSlabPotential k s (apertureWindowPartial w v) x := by
  have he := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (slabGreen_locallyIntegrable k s) (hw.of_le (by simp)) x
  change (fderiv ℝ (slabGreen k s ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] w) x) v = _
  rw [he.fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    (slabGreen_locallyIntegrable k s) (hc.fderiv ℝ)
    (hw.continuous_fderiv (by simp)) x v

theorem apertureWindowPartial_jet_norm_le (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x v : ℂ) :
    ‖iteratedFDeriv ℝ n (apertureWindowPartial w v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) w x‖ := by
  let ev : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ w) := hw.fderiv_right (by simp)
  have he := ev.iteratedFDeriv_comp_left (hD.contDiffAt (x := x)) (i := n) (by simp)
  change ‖iteratedFDeriv ℝ n (ev ∘ fderiv ℝ w) x‖ ≤ _
  rw [he]
  have hn : ‖ev‖ ≤ ‖v‖ := by
    apply ev.opNorm_le_bound (norm_nonneg v)
    intro D
    change ‖D v‖ ≤ ‖v‖ * ‖D‖
    simpa only [mul_comm] using D.le_opNorm v
  apply (ev.norm_compContinuousMultilinearMap_le _).trans
  rw [norm_iteratedFDeriv_fderiv]
  gcongr

theorem horizontalSlabPotential_second_partial (k s : ℝ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x u v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (horizontalSlabPotential k s w) y u) x v =
      horizontalSlabPotential k s (apertureWindowPartial (apertureWindowPartial w u) v) x := by
  have he : (fun y => fderiv ℝ (horizontalSlabPotential k s w) y u) =
      horizontalSlabPotential k s (apertureWindowPartial w u) := by
    funext y
    exact horizontalSlabPotential_partial k s w hw hc y u
  rw [he]
  exact horizontalSlabPotential_partial k s _ (apertureWindowPartial_contDiff w hw u)
    (apertureWindowPartial_hasCompactSupport w hc u) x v

end OQ7Prescribed
