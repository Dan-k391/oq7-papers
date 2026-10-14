import PrescribedExtinction.NewtonSchwartz

/-! Exact Mathlib Fourier normalization for the actual Newtonian tempered
kernel and Hessian. The scalar Newton Fourier transform is still to be proved;
the factor below is not a proof of the inverse-square Fourier kernel. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap

theorem newtonTempered_fourier_apply (φ : SchwartzMap Position ℂ) :
    𝓕 newtonTempered φ =
      ∫ x : Position, (𝓕 φ) x * outgoingGreen 0 x := by
  rw [TemperedDistribution.fourier_apply, newtonTempered_apply]

theorem newtonTemperedHessian_fourier : ∀ i j : Fin 3,
    𝓕 (newtonTemperedHessian i j) =
      (-(2 * Real.pi) ^ 2 : ℂ) •
        TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : Position => (ξ i : ℂ) * (ξ j : ℂ)) (𝓕 newtonTempered) := by
  intro i j
  have hei : (fun ξ : Position => (inner ℝ ξ (basisR i) : ℂ)) =
      (fun ξ : Position => (ξ i : ℂ)) := by
    funext ξ
    rw [real_inner_basis]
  have hej : (fun ξ : Position => (inner ℝ ξ (basisR j) : ℂ)) =
      (fun ξ : Position => (ξ j : ℂ)) := by
    funext ξ
    rw [real_inner_basis]
  have hi : (fun ξ : Position => (ξ i : ℂ)).HasTemperateGrowth := by
    rw [← hei]
    fun_prop
  have hj : (fun ξ : Position => (ξ j : ℂ)).HasTemperateGrowth := by
    rw [← hej]
    fun_prop
  rw [newtonTemperedHessian, TemperedDistribution.fourier_lineDerivOp_eq,
    TemperedDistribution.fourier_lineDerivOp_eq,
    hei, hej,
    map_smul, smul_smul,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hj hi]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I) =
      (-(2 * Real.pi) ^ 2 : ℂ) := by
    ring_nf
    simp
  rw [hc]
  have he : ((fun ξ : Position => (ξ j : ℂ)) * fun ξ => (ξ i : ℂ)) =
      (fun ξ : Position => (ξ i : ℂ) * (ξ j : ℂ)) := by
    funext ξ
    exact mul_comm _ _
  rw [he]

end OQ7Prescribed
