import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel

noncomputable section
namespace OQ7Prescribed
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Quantitative stability of genuine bounded inverses; no physical invertibility hypothesis. -/
theorem continuousLinearEquiv_response_difference_bound (e f : H ≃L[ℂ] H) (s t : H) :
    ‖e.symm s - f.symm t‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      (‖s - t‖ + ‖e.toContinuousLinearMap - f.toContinuousLinearMap‖ * ‖f.symm t‖) := by
  have hid : e.symm s - f.symm t = e.symm
      (s - t + (f.toContinuousLinearMap - e.toContinuousLinearMap) (f.symm t)) := by
    apply e.injective
    simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearEquiv.coe_coe]
    abel
  rw [hid]
  apply (e.symm.toContinuousLinearMap.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg e.symm.toContinuousLinearMap)
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  simpa only [norm_sub_rev] using
    (f.toContinuousLinearMap - e.toContinuousLinearMap).le_opNorm (f.symm t)

theorem continuousLinearEquiv_solution_residual_bound (e : H ≃L[ℂ] H) (s v : H) :
    ‖e.symm s - v‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖s - e v‖ := by
  have hid : e.symm s - v = e.symm (s - e v) := by simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  rw [hid]
  exact e.symm.toContinuousLinearMap.le_opNorm _

theorem continuousLinearEquiv_response_continuousAt {X : Type*} [TopologicalSpace X]
    (e : X → H ≃L[ℂ] H) (s : X → H) (x : X) (M : ℝ)
    (hM : ∀ a : X, ‖(e a).symm.toContinuousLinearMap‖ ≤ M)
    (he : ContinuousAt (fun a => (e a).toContinuousLinearMap) x) (hs : ContinuousAt s x) :
    ContinuousAt (fun a => (e a).symm (s a)) x := by
  have hb (a : X) : ‖(e a).symm (s a) - (e x).symm (s x)‖ ≤
      M * (‖s a - s x‖ + ‖(e a).toContinuousLinearMap - (e x).toContinuousLinearMap‖ * ‖(e x).symm (s x)‖) := by
    apply (continuousLinearEquiv_response_difference_bound (e a) (e x) (s a) (s x)).trans
    exact mul_le_mul_of_nonneg_right (hM a) (by positivity)
  have ht : Tendsto (fun a => M * (‖s a - s x‖ +
      ‖(e a).toContinuousLinearMap - (e x).toContinuousLinearMap‖ * ‖(e x).symm (s x)‖)) (𝓝 x) (𝓝 0) := by
    convert ((hs.tendsto.sub tendsto_const_nhds).norm.add
      ((he.tendsto.sub tendsto_const_nhds).norm.mul_const ‖(e x).symm (s x)‖)).const_mul M using 1 <;> simp
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun a => norm_nonneg _) hb ht

end OQ7Prescribed
