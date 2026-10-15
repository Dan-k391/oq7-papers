import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Real

namespace OQ7Prescribed
open Set Filter
open scoped Topology

theorem exists_uniform_parameter_neighborhood_of_compact (s : Set ℝ) (hs : IsCompact s)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ∀ θ ∈ s, (0, θ) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ (ν : ℝ), |ν| < r → ∀ θ ∈ s, (ν, θ) ∈ U := by
  obtain ⟨u, v, hu, _, hsu, htv, huv⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hs hU (by
      rintro ⟨ν, θ⟩ ⟨hν, hθ⟩
      have hz : ν = 0 := mem_singleton_iff.mp hν
      subst ν
      exact h0 θ hθ)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hu 0 (hsu (mem_singleton 0))
  refine ⟨r, hr, fun ν hν θ hθ => huv ⟨?_, htv hθ⟩⟩
  apply hball
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hν

theorem isOpen_strict_region_of_continuousAt_on_open {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (f : X → ℝ) (hf : ∀ x ∈ U, ContinuousAt f x) (m : ℝ) :
    IsOpen {x | x ∈ U ∧ m < f x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem (hU.mem_nhds hx.1) ((hf x hx.1).eventually_const_lt hx.2)

end OQ7Prescribed
