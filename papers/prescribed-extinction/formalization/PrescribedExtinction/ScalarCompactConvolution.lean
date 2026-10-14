import PrescribedExtinction.VolumePotential
import PrescribedExtinction.SmoothOutgoingFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Convolution

def scalarOutgoingPotential (k : ℝ) (f : Position → ℂ) (x : Position) : ℂ :=
  ∫ y : Position, outgoingGreen k (x - y) * f y

theorem scalarOutgoingPotential_convolution (k : ℝ) (f : Position → ℂ) :
    scalarOutgoingPotential k f = outgoingGreen k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f := by
  funext x
  have he := integral_sub_left_eq_self
    (fun y : Position => outgoingGreen k y * f (x - y)) volume x
  change (∫ y : Position, outgoingGreen k (x - y) * f y) =
    ∫ y : Position, outgoingGreen k y * f (x - y)
  simpa only [sub_sub_self] using he

theorem scalarOutgoingPotential_integrable (k : ℝ) (f : Position → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (x : Position) :
    Integrable (fun y : Position => outgoingGreen k (x - y) * f y) volume := by
  obtain ⟨R, hR, hball⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Position)
  have hfm : MemLp f 2 volume := hf.memLp_of_hasCompactSupport hc
  have hi := ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ)
    hfm (cutoffGreen_memLp k (‖x‖ + R)) x
  apply hi.congr
  exact ae_of_all _ (fun y => by
    by_cases hy : y ∈ tsupport f
    · have hn := hball hy
      simp only [Metric.mem_closedBall, dist_zero_right] at hn
      have hxy : x - y ∈ Metric.closedBall 0 (‖x‖ + R) := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact (norm_sub_le x y).trans (add_le_add le_rfl hn)
      simp [cutoffGreen, hxy, mul_comm]
    · simp [image_eq_zero_of_notMem_tsupport hy])

theorem scalarOutgoingPotential_contDiff (k : ℝ) (f : Position → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarOutgoingPotential k f) := by
  have he : scalarOutgoingPotential k f = f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] outgoingGreen k := by
    funext x
    apply integral_congr_ae
    exact ae_of_all _ fun y => mul_comm _ _
  rw [he]
  exact hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hf (outgoingGreen_locallyIntegrable k)

theorem scalarOutgoingPotential_partial (k : ℝ) (f : Position → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (x a : Position) :
    fderiv ℝ (scalarOutgoingPotential k f) x a =
      scalarOutgoingPotential k (fun y => fderiv ℝ f y a) x := by
  rw [scalarOutgoingPotential_convolution, scalarOutgoingPotential_convolution]
  have he := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (outgoingGreen_locallyIntegrable k) (hf.of_le (by simp)) x
  rw [he.fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    (outgoingGreen_locallyIntegrable k) (hc.fderiv ℝ)
    (hf.continuous_fderiv (by simp)) x a

end OQ7Prescribed
