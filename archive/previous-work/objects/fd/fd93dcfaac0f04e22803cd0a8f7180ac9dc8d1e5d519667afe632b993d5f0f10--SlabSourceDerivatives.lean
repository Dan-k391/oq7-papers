import work.SlabSourceGeometry
import work.SlabDerivatives
import work.SlabSecondWindow
import work.ScalarCompactConvolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabHorizontalCLM : Position →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)) +
    Complex.I • (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1))

def slabHeightCLM : Position →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2

theorem slabHorizontalCLM_apply (x : Position) : slabHorizontalCLM x = slabHorizontalCoordinate x := by
  simp [slabHorizontalCLM, slabHorizontalCoordinate, mul_comm]

theorem slabHorizontalCLM_at_slab (v : ℂ) : slabHorizontalCLM (slabPosition v 0) = v := by
  simp [slabHorizontalCLM_apply, slabHorizontalCoordinate, slabPosition]

theorem slabHeightCLM_at_slab (v : ℂ) : slabHeightCLM (slabPosition v 0) = 0 := by
  simp [slabHeightCLM, slabPosition]

theorem slabSeparatedFunction_horizontal_partial (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (x : Position) (v : ℂ) :
    fderiv ℝ (slabSeparatedFunction w q) x (slabPosition v 0) =
      slabSeparatedFunction (apertureWindowPartial w v) q x := by
  have hW := (hw.differentiable (by simp) (slabHorizontalCLM x)).hasFDerivAt.comp x
    (slabHorizontalCLM.hasFDerivAt (x := x))
  have hQ := (hq.differentiable (by simp) (x 2)).hasFDerivAt.comp x
    (slabHeightCLM.hasFDerivAt (x := x))
  have h := hW.mul hQ
  have hfunc : (fun y => w (slabHorizontalCLM y) * q (slabHeightCLM y)) = slabSeparatedFunction w q := by
    funext y
    simp only [slabHorizontalCLM_apply, slabHeightCLM, PiLp.proj_apply]
    rfl
  change HasFDerivAt (fun y => w (slabHorizontalCLM y) * q (slabHeightCLM y)) _ x at h
  rw [hfunc] at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, slabHorizontalCLM_at_slab, slabHeightCLM_at_slab,
    slabSeparatedFunction, apertureWindowPartial, slabHeightCLM, slabHorizontalCLM_apply, mul_comm]
  simp [slabPosition, slabHorizontalCoordinate]

theorem scalarOutgoingPotential_slab_horizontal_partial (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x : Position) (v : ℂ) :
    fderiv ℝ (scalarOutgoingPotential k (slabSeparatedFunction w q)) x (slabPosition v 0) =
      scalarOutgoingPotential k (slabSeparatedFunction (apertureWindowPartial w v) q) x := by
  rw [scalarOutgoingPotential_partial k _ (slabSeparatedFunction_contDiff w q hw hq)
    (slabSeparatedFunction_hasCompactSupport w q hwc hqc)]
  congr 1
  funext y
  exact slabSeparatedFunction_horizontal_partial w q hw hq y v

theorem scalarOutgoingPotential_slab_second_horizontal_partial (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x : Position) (u v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (scalarOutgoingPotential k (slabSeparatedFunction w q)) y
      (slabPosition u 0)) x (slabPosition v 0) =
      scalarOutgoingPotential k (slabSeparatedFunction (apertureWindowSecond w u v) q) x := by
  have he : (fun y => fderiv ℝ (scalarOutgoingPotential k (slabSeparatedFunction w q)) y
      (slabPosition u 0)) = scalarOutgoingPotential k (slabSeparatedFunction (apertureWindowPartial w u) q) := by
    funext y
    exact scalarOutgoingPotential_slab_horizontal_partial k w q hw hq hwc hqc y u
  rw [he]
  exact scalarOutgoingPotential_slab_horizontal_partial k _ q (apertureWindowPartial_contDiff w hw u)
    hq (apertureWindowPartial_hasCompactSupport w hwc u) hqc x v

end OQ7Prescribed
