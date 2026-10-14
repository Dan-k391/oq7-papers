import PrescribedExtinction.SlabPotentialSeparation
import PrescribedExtinction.SlabSourceDerivatives
import PrescribedExtinction.SlabTransverseKernel

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped InnerProductSpace

def scalarOutgoingSlabTransverse (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ) (x : ℂ) (z : ℝ) (u v : ℂ) : ℂ :=
  (k ^ 2 * inner ℝ u v : ℝ) • scalarOutgoingPotential k (slabSeparatedFunction w q) (slabPosition x z) +
    fderiv ℝ (fun y => fderiv ℝ (scalarOutgoingPotential k (slabSeparatedFunction w q)) y
      (slabPosition u 0)) (slabPosition x z) (slabPosition v 0)

theorem scalarOutgoingSlabTransverse_separation (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x u v : ℂ) (z : ℝ) :
    scalarOutgoingSlabTransverse k w q x z u v =
      ∫ t : ℝ, horizontalSlabTransverseKernel k (z - t) w x u v * q t := by
  have hW := apertureWindowSecond_contDiff w hw u v
  have hWc := apertureWindowSecond_hasCompactSupport w hwc u v
  have hi := horizontalSlabPotential_height_integrable k w q hw hq hwc hqc x z
  have hsi : Integrable (fun t : ℝ => (k ^ 2 * inner ℝ u v : ℝ) •
      (horizontalSlabPotential k (z - t) w x * q t)) volume := hi.smul (k ^ 2 * inner ℝ u v)
  have hdi := horizontalSlabPotential_height_integrable k _ q hW hq hWc hqc x z
  unfold scalarOutgoingSlabTransverse
  rw [scalarOutgoingPotential_slab_second_horizontal_partial k w q hw hq hwc hqc,
    scalarOutgoingPotential_slab_separation k w q hw hq hwc hqc,
    scalarOutgoingPotential_slab_separation k _ q hW hq hWc hqc]
  have hfun : (fun t : ℝ => horizontalSlabTransverseKernel k (z - t) w x u v * q t) =
      fun t => (k ^ 2 * inner ℝ u v : ℝ) • (horizontalSlabPotential k (z - t) w x * q t) +
        horizontalSlabPotential k (z - t) (apertureWindowSecond w u v) x * q t := by
    funext t
    rw [horizontalSlabTransverseKernel, horizontalSlabPotential_second_partial k (z - t) w hw hwc]
    simp only [add_mul, smul_mul_assoc]
    rfl
  rw [hfun, integral_add hsi hdi, integral_smul]

theorem scalarOutgoingSlabTransverse_height_integrable (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x u v : ℂ) (z : ℝ) :
    Integrable (fun t : ℝ => horizontalSlabTransverseKernel k (z - t) w x u v * q t) volume := by
  have hi := horizontalSlabPotential_height_integrable k w q hw hq hwc hqc x z
  have hd := horizontalSlabPotential_height_integrable k _ q (apertureWindowSecond_contDiff w hw u v)
    hq (apertureWindowSecond_hasCompactSupport w hwc u v) hqc x z
  have he : (fun t : ℝ => horizontalSlabTransverseKernel k (z - t) w x u v * q t) =
      fun t => (k ^ 2 * inner ℝ u v : ℝ) • (horizontalSlabPotential k (z - t) w x * q t) +
        horizontalSlabPotential k (z - t) (apertureWindowSecond w u v) x * q t := by
    funext t
    rw [horizontalSlabTransverseKernel, horizontalSlabPotential_second_partial k (z - t) w hw hwc]
    simp only [add_mul, smul_mul_assoc]
    rfl
  rw [he]
  have hsi : Integrable (fun t : ℝ => (k ^ 2 * inner ℝ u v : ℝ) •
      (horizontalSlabPotential k (z - t) w x * q t)) volume := hi.smul (k ^ 2 * inner ℝ u v)
  exact hsi.add hd

end OQ7Prescribed
