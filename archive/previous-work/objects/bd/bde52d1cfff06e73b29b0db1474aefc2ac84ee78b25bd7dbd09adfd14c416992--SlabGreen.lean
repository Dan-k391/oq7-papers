import work.ApertureOscillation
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def slabPosition (w : ℂ) (z : ℝ) : Position := WithLp.toLp 2 ![w.re, w.im, z]

theorem slabPosition_norm_sq (w : ℂ) (z : ℝ) :
    ‖slabPosition w z‖ ^ 2 = ‖w‖ ^ 2 + z ^ 2 := by
  simp [slabPosition, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem slabPosition_norm (w : ℂ) (z : ℝ) :
    ‖slabPosition w z‖ = Real.sqrt (‖w‖ ^ 2 + z ^ 2) := by
  rw [← slabPosition_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem slabPosition_norm_ge (w : ℂ) (z : ℝ) : ‖w‖ ≤ ‖slabPosition w z‖ := by
  nlinarith [slabPosition_norm_sq w z, norm_nonneg w, norm_nonneg (slabPosition w z), sq_nonneg z]

def slabGreen (k z : ℝ) (w : ℂ) : ℂ := outgoingGreen k (slabPosition w z)

theorem slabGreen_measurable (k z : ℝ) : Measurable (slabGreen k z) := by
  apply (outgoingGreen_measurable k).comp
  unfold slabPosition
  fun_prop

theorem slabGreen_norm (k z : ℝ) (w : ℂ) :
    ‖slabGreen k z w‖ = (4 * Real.pi * Real.sqrt (‖w‖ ^ 2 + z ^ 2))⁻¹ := by
  rw [slabGreen, outgoingGreen_norm, slabPosition_norm]

theorem slabGreen_norm_le (k z : ℝ) (w : ℂ) (hw : w ≠ 0) :
    ‖slabGreen k z w‖ ≤ (4 * Real.pi)⁻¹ * ‖w‖⁻¹ := by
  rw [slabGreen, outgoingGreen_norm, ← mul_inv_rev, mul_comm ‖w‖]
  simp only [← one_div]
  apply one_div_le_one_div_of_le
  · exact mul_pos (by positivity) (norm_pos_iff.mpr hw)
  · exact mul_le_mul_of_nonneg_left (slabPosition_norm_ge w z) (by positivity)

theorem slabGreen_locallyIntegrable (k z : ℝ) : LocallyIntegrable (slabGreen k z) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi)⁻¹) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_
    (slabGreen_measurable k z).aestronglyMeasurable
  have hzero : ∀ᵐ w : ℂ ∂volume, w ≠ 0 := by simp [ae_iff]
  filter_upwards [hzero] with w hw
  simpa [Real.rpow_neg_one] using slabGreen_norm_le k z w hw

theorem slabGreen_radial (k z r θ : ℝ) :
    slabGreen k z (circleMap 0 r θ) =
      apertureOscillation k (Real.sqrt (r ^ 2 + z ^ 2)) /
        ((4 * Real.pi * Real.sqrt (r ^ 2 + z ^ 2) : ℝ) : ℂ) := by
  unfold slabGreen outgoingGreen apertureOscillation
  rw [slabPosition_norm]
  simp

end OQ7Prescribed
