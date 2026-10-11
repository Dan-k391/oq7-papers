import OQ7.ResourceBounds
import OQ7.ResourceUniform
import OQ7.SelectedResource

noncomputable section

namespace OQ7

open Filter Set
open scoped Topology

/-- The unconditional half-cell floor for the original selected physical class. -/
theorem selectedResource_half_floor {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : SelectedResourceClass P Q M L layers) :
    ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) ≤
      stackResourceInvariant k layers := by
  obtain ⟨hphysical, a, ha, hpLocal, hqLocal, hMass⟩ := h
  exact physical_resource_half_lower_finitePhysical_Ioo hk hP hQ ha hL
    hphysical hpLocal hqLocal hMass

/-- The explicit lower estimate for the half-cell floor in equation (27). -/
theorem selectedResource_half_floor_explicit {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : SelectedResourceClass P Q M L layers) :
    4 * k ^ 4 * M ^ 4 / (3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2) ≤
      ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) := by
  obtain ⟨hphysical, a, _, _, hqLocal, hMass⟩ := h
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hglobal⟩ :=
    finitePhysicalStack_exists_caps hphysical
  have hbudget : M ≤ Q * L := by
    rw [← hMass]
    exact resourceMass_le_cap_Ioo hL.le
      (fun x y => stackLossProfile_intervalIntegrable x y hQglobal hglobal) hqLocal
  exact ResourceFloor.half_floor_explicit hk hP hQ hM hL hbudget

/-- Positive distributed loss forces a strict positive physical invariant. -/
theorem selectedResource_invariant_pos {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : SelectedResourceClass P Q M L layers) :
    0 < stackResourceInvariant k layers :=
  (ResourceFloor.explicit_floor_pos hk hP hQ hM hL).trans_le
    ((selectedResource_half_floor_explicit hk hP hQ hM hL h).trans
      (selectedResource_half_floor hk hP hQ hL h))
/-- The strong finite floor for the original selected-interval physical class. -/
theorem selectedResource_full_floor {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : SelectedResourceClass P Q M L layers)
    (hcase : ResourceFloor.U k P Q M ≤ Real.pi / 2 ∨
      ResourceFloor.U k P Q M / (ResourceFloor.fullCellCount k P L : ℝ) ≤ 1 / 3) :
    ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) ≤
      stackResourceInvariant k layers := by
  obtain ⟨hphysical, a, ha, hpLocal, hqLocal, hMass⟩ := h
  exact physical_resource_full_lower_finitePhysical_Ioo hk hP hQ hM ha hL
    hphysical hpLocal hqLocal hMass hcase

/-- The finite inequalities (27) and (28) of Theorem 4.5 for actual multilayers. -/
theorem theorem45_finite {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : SelectedResourceClass P Q M L layers) :
    ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) ≤
      stackResourceInvariant k layers ∧
    4 * k ^ 4 * M ^ 4 / (3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2) ≤
      ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) ∧
    0 < 4 * k ^ 4 * M ^ 4 / (3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2) ∧
    ((ResourceFloor.U k P Q M ≤ Real.pi / 2 ∨
      ResourceFloor.U k P Q M / (ResourceFloor.fullCellCount k P L : ℝ) ≤ 1 / 3) →
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) ≤
        stackResourceInvariant k layers) :=
  ⟨selectedResource_half_floor hk hP hQ hL h,
    selectedResource_half_floor_explicit hk hP hQ hM hL h,
    ResourceFloor.explicit_floor_pos hk hP hQ hM hL,
    selectedResource_full_floor hk hP hQ hM hL h⟩
/-- The same budget threshold works for every original physical stack, including
arbitrary additional finite passive layers outside the selected interval. -/
theorem selectedResource_full_floor_eventually {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    ∀ᶠ L : ℝ in atTop, ∀ layers : List HomogeneousLayer,
      SelectedResourceClass P Q M L layers →
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) ≤
        stackResourceInvariant k layers := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    ResourceFloor.full_mean_eventually_small hk hP hQ hM] with L hL hsmall
  intro layers h
  exact selectedResource_full_floor hk hP hQ hM hL h (Or.inr hsmall)

/-- The uniform asymptotic lower bound in Theorem 4.5, with the budget threshold
independent of the stack and of its selected interval. -/
theorem theorem45_uniform_asymptotic {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ layers : List HomogeneousLayer,
      SelectedResourceClass P Q M L layers →
      resourceAsymptoticCoefficient k P Q M - ε ≤
        (k * L) ^ 2 * stackResourceInvariant k layers :=
  resource_uniform_eventual_lower_of_floor hk hP hQ hM
    (SelectedResourceClass P Q M) (fun _ layers => stackResourceInvariant k layers)
    (selectedResource_full_floor_eventually hk hP hQ hM) hε

/-- Every varying admissible physical sequence with budgets tending to infinity
satisfies the precise eventual epsilon form of the lower bound. -/
theorem theorem45_sequence_eventual_lower {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    (L : ℕ → ℝ) (layers : ℕ → List HomogeneousLayer)
    (hL : Tendsto L atTop atTop)
    (hphysical : ∀ j, SelectedResourceClass P Q M (L j) (layers j))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, resourceAsymptoticCoefficient k P Q M - ε ≤
      (k * L j) ^ 2 * stackResourceInvariant k (layers j) := by
  have hfloor : ∀ᶠ j : ℕ in atTop,
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P (L j)) ≤
        stackResourceInvariant k (layers j) := by
    filter_upwards [hL.eventually (selectedResource_full_floor_eventually hk hP hQ hM)]
      with j hj
    exact hj (layers j) (hphysical j)
  exact resource_sequence_eventual_lower_of_floor hk hP hQ hM L
    (fun j => stackResourceInvariant k (layers j)) hL hfloor hε

/-- Equation (29), quantified over every sequence in the original physical class.
Extended-real liminf includes sequences whose scaled invariant diverges to infinity. -/
theorem theorem45_sequence_lowerlimit {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    (L : ℕ → ℝ) (layers : ℕ → List HomogeneousLayer)
    (hL : Tendsto L atTop atTop)
    (hphysical : ∀ j, SelectedResourceClass P Q M (L j) (layers j)) :
    (resourceAsymptoticCoefficient k P Q M : EReal) ≤
      liminf (fun j => ((k * L j) ^ 2 * stackResourceInvariant k (layers j) : EReal))
        atTop := by
  have hfloor : ∀ᶠ j : ℕ in atTop,
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P (L j)) ≤
        stackResourceInvariant k (layers j) := by
    filter_upwards [hL.eventually (selectedResource_full_floor_eventually hk hP hQ hM)]
      with j hj
    exact hj (layers j) (hphysical j)
  exact resource_sequence_liminf_lower_of_floor hk hP hQ hM L
    (fun j => stackResourceInvariant k (layers j)) hL hfloor

#print axioms selectedResource_half_floor
#print axioms selectedResource_half_floor_explicit
#print axioms selectedResource_invariant_pos
#print axioms theorem45_finite
#print axioms selectedResource_full_floor
#print axioms selectedResource_full_floor_eventually
#print axioms theorem45_uniform_asymptotic
#print axioms theorem45_sequence_eventual_lower
#print axioms theorem45_sequence_lowerlimit

end OQ7


