import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Abel

noncomputable section
namespace OQ7Prescribed
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem inverse_trial_residual_estimate (e : E ≃L[𝕜] E) (A : F →L[𝕜] F) (J : F →L[𝕜] E)
    (g : E) (f q : F) (hq : A q = -f) (M C : ℝ) (hM : 0 ≤ M)
    (he : ‖e.symm.toContinuousLinearMap‖ ≤ M)
    (hres : ‖e (J q) - J (A q)‖ ≤ C * ‖q‖) :
    ‖e.symm (-g) - J q‖ ≤ M * (‖g - J f‖ + C * ‖q‖) := by
  have hid : e.symm (-g) - J q = e.symm (-g - e (J q)) := by
    rw [map_sub, e.symm_apply_apply]
  have hsplit : -g - e (J q) = -(g - J f) - (e (J q) - J (A q)) := by
    rw [hq, map_neg]
    abel
  rw [hid]
  apply (e.symm.toContinuousLinearMap.le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
  apply mul_le_mul_of_nonneg_left _ hM
  rw [hsplit]
  exact (norm_sub_le _ _).trans (by simpa only [norm_neg] using add_le_add le_rfl hres)

end OQ7Prescribed
