import work.SlabSourceGeometry
import work.ScalarCompactConvolution
import PrescribedExtinction.SlabConvolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem horizontalSlabPotential_source_form (k s : ℝ) (w : ℂ → ℂ) (x : ℂ) :
    (∫ y : ℂ, slabGreen k s (x - y) * w y) = horizontalSlabPotential k s w x := by
  have he := integral_sub_left_eq_self
    (fun y : ℂ => slabGreen k s y * w (x - y)) volume x
  unfold horizontalSlabPotential
  simpa only [sub_sub_self] using he

theorem scalarOutgoingPotential_slab_product_integrable (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x : ℂ) (z : ℝ) :
    Integrable (fun p : ℂ × ℝ => slabGreen k (z - p.2) (x - p.1) * w p.1 * q p.2) volume := by
  have hi := scalarOutgoingPotential_integrable k (slabSeparatedFunction w q)
    (slabSeparatedFunction_contDiff w q hw hq).continuous
    (slabSeparatedFunction_hasCompactSupport w q hwc hqc) (slabPosition x z)
  apply (slabCoordinateEquiv_measurePreserving.integrable_comp_of_integrable hi).congr
  exact ae_of_all _ (fun p => by
    change outgoingGreen k (slabPosition x z - slabCoordinateEquiv p) *
      slabSeparatedFunction w q (slabCoordinateEquiv p) = _
    rw [slabCoordinateEquiv_apply, slabPosition_sub, slabSeparatedFunction_at_slab]
    simp only [slabGreen]
    ring)

theorem scalarOutgoingPotential_slab_separation (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x : ℂ) (z : ℝ) :
    scalarOutgoingPotential k (slabSeparatedFunction w q) (slabPosition x z) =
      ∫ t : ℝ, horizontalSlabPotential k (z - t) w x * q t := by
  have hi := scalarOutgoingPotential_slab_product_integrable k w q hw hq hwc hqc x z
  unfold scalarOutgoingPotential
  rw [integral_slabCoordinates]
  have he : (∫ p : ℂ × ℝ, outgoingGreen k (slabPosition x z - slabPosition p.1 p.2) *
      slabSeparatedFunction w q (slabPosition p.1 p.2)) =
      ∫ p : ℂ × ℝ, slabGreen k (z - p.2) (x - p.1) * w p.1 * q p.2 := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by
      change outgoingGreen k (slabPosition x z - slabPosition p.1 p.2) *
        slabSeparatedFunction w q (slabPosition p.1 p.2) = _
      rw [slabPosition_sub, slabSeparatedFunction_at_slab]
      simp only [slabGreen]
      ring)
  rw [he]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change (∫ y : ℂ, slabGreen k (z - t) (x - y) * w y * q t) = _
    rw [integral_mul_const, horizontalSlabPotential_source_form])

theorem horizontalSlabPotential_height_integrable (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (x : ℂ) (z : ℝ) :
    Integrable (fun t : ℝ => horizontalSlabPotential k (z - t) w x * q t) volume := by
  have hi := scalarOutgoingPotential_slab_product_integrable k w q hw hq hwc hqc x z
  rw [Measure.volume_eq_prod] at hi
  apply hi.integral_prod_right.congr
  exact ae_of_all _ (fun t => by
    change (∫ y : ℂ, slabGreen k (z - t) (x - y) * w y * q t) = _
    rw [integral_mul_const, horizontalSlabPotential_source_form])

end OQ7Prescribed
