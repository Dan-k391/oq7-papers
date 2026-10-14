import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace OQ7Prescribed
open Set

theorem norm_bound_of_close_approximants {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (D : E →L[ℂ] F) (K : ℝ) (x : E)
    (ha : ∀ ε > 0, ∃ y : E, ‖x - y‖ ≤ ε ∧ ‖D y‖ ≤ K * ‖y‖) :
    ‖D x‖ ≤ K * ‖x‖ := by
  let S : Set E := {y | ‖D y‖ ≤ K * ‖y‖}
  have hc : IsClosed S := isClosed_le D.continuous.norm (continuous_const.mul continuous_norm)
  have hm : x ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hb⟩ := ha (ε / 2) (half_pos hε)
    refine ⟨y, hb, ?_⟩
    rw [dist_eq_norm]
    exact hy.trans_lt (half_lt_self hε)
  rw [hc.closure_eq] at hm
  exact hm

end OQ7Prescribed
