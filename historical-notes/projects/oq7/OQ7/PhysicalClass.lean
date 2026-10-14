import OQ7.Layers
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OQ7

/-- Finite passive ordinary dielectric layers, without a specified upper material cap.
Local resource theorems can use independent caps on a selected interval. -/
def FinitePhysicalStack (layers : List HomogeneousLayer) : Prop :=
  ∀ layer ∈ layers, 1 ≤ layer.p ∧ 0 ≤ layer.q ∧ 0 ≤ layer.width

theorem finitePhysicalStack_of_admissible {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) : FinitePhysicalStack layers := by
  intro layer hm
  have hl := h layer hm
  exact ⟨hl.1, hl.2.2.1, hl.2.2.2.2⟩

theorem finitePhysicalStack_exists_caps {layers : List HomogeneousLayer}
    (h : FinitePhysicalStack layers) :
    ∃ P Q : ℝ, 1 ≤ P ∧ 0 ≤ Q ∧ StackAdmissible P Q layers := by
  let P := 1 + (layers.map HomogeneousLayer.p).sum
  let Q := (layers.map HomogeneousLayer.q).sum
  have hp : ∀ x ∈ layers.map HomogeneousLayer.p, (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨layer, hm, rfl⟩ := List.mem_map.mp hx
    exact le_trans (by norm_num) (h layer hm).1
  have hq : ∀ x ∈ layers.map HomogeneousLayer.q, (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨layer, hm, rfl⟩ := List.mem_map.mp hx
    exact (h layer hm).2.1
  have hpsum : 0 ≤ (layers.map HomogeneousLayer.p).sum := List.sum_nonneg hp
  have hqsum : 0 ≤ (layers.map HomogeneousLayer.q).sum := List.sum_nonneg hq
  refine ⟨P, Q, by dsimp [P]; linarith, hqsum, ?_⟩
  intro layer hm
  have hl := h layer hm
  have hpmem : layer.p ∈ layers.map HomogeneousLayer.p := List.mem_map.mpr ⟨layer, hm, rfl⟩
  have hqmem : layer.q ∈ layers.map HomogeneousLayer.q := List.mem_map.mpr ⟨layer, hm, rfl⟩
  have hple := List.single_le_sum hp _ hpmem
  have hqle := List.single_le_sum hq _ hqmem
  exact ⟨hl.1, by dsimp [P]; linarith, hl.2.1, hqle, hl.2.2⟩

theorem finitePhysicalStack_iff_exists_admissible (layers : List HomogeneousLayer) :
    FinitePhysicalStack layers ↔ ∃ P Q : ℝ, StackAdmissible P Q layers := by
  constructor
  · intro h
    obtain ⟨P, Q, _, _, hc⟩ := finitePhysicalStack_exists_caps h
    exact ⟨P, Q, hc⟩
  · rintro ⟨P, Q, hc⟩
    exact finitePhysicalStack_of_admissible hc

#print axioms finitePhysicalStack_of_admissible
#print axioms finitePhysicalStack_exists_caps
#print axioms finitePhysicalStack_iff_exists_admissible

end OQ7
