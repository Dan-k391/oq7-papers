import OQ7.ResourceTheorem45
import OQ7.PhysicalResourceDeficit

noncomputable section

namespace OQ7

open Filter Set
open scoped Topology

/-- The floor transferred through the exact-target envelope, before its sharp limit. -/
def fullResourceDeficitFloor (p : PhysicalParameters) (L : ℝ) : ℝ :=
  ScalarEnvelope.alpha p.T p.a *
    ResourceFloor.beta p.k p.P p.Q p.M (ResourceFloor.fullCellCount p.k p.P L)

theorem asymptoticCoefficient_eq_resource (p : PhysicalParameters) :
    asymptoticCoefficient p =
      ScalarEnvelope.alpha p.T p.a * resourceAsymptoticCoefficient p.k p.P p.Q p.M := by
  unfold asymptoticCoefficient resourceAsymptoticCoefficient
  ring

theorem fullResourceDeficitFloor_scaled_tendsto (p : PhysicalParameters) :
    Tendsto (fun L : ℝ => (p.k * L) ^ 2 * fullResourceDeficitFloor p L)
      atTop (𝓝 (asymptoticCoefficient p)) := by
  rw [asymptoticCoefficient_eq_resource]
  dsimp only [resourceAsymptoticCoefficient]
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  have ht := (ResourceFloor.full_floor_limit p.k_pos hP p.Q_pos p.M_pos).const_mul
    (ScalarEnvelope.alpha p.T p.a)
  convert ht using 1
  funext L
  unfold fullResourceDeficitFloor
  ring

/-- Pure order transfer for the scaled actual physical deficit; its floor premise
is supplied by the physical resource theorem in the public Section 5 bridge. -/
theorem physical_deficit_liminf_of_full_floor (p : PhysicalParameters)
    (deficit : ℝ → ℝ)
    (hfloor : ∀ᶠ L : ℝ in atTop, fullResourceDeficitFloor p L ≤ deficit L) :
    (asymptoticCoefficient p : EReal) ≤
      liminf (fun L : ℝ => ((p.k * L) ^ 2 * deficit L : EReal)) atTop := by
  have hte := EReal.tendsto_coe.mpr (fullResourceDeficitFloor_scaled_tendsto p)
  rw [← hte.liminf_eq]
  apply Filter.liminf_le_liminf
  filter_upwards [hfloor] with L hL
  exact_mod_cast mul_le_mul_of_nonneg_left hL (sq_nonneg (p.k * L))
  all_goals isBoundedDefault

/-- Uniform transfer to each exact-target physical stack from a proved resource floor. -/
theorem exactTarget_uniform_deficit_of_full_floor (p : PhysicalParameters)
    (hfloor : ∀ᶠ L : ℝ in atTop, ∀ layers ∈ exactTargetClass p L,
      ResourceFloor.beta p.k p.P p.Q p.M (ResourceFloor.fullCellCount p.k p.P L) ≤
        normalizedAbsorptionDet (stackReflectionLeft p.k layers)
          (stackReflectionRight p.k layers) (stackTransmission p.k layers))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ layers ∈ exactTargetClass p L,
      asymptoticCoefficient p - ε ≤ (p.k * L) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k layers) := by
  have hα : 0 < ScalarEnvelope.alpha p.T p.a :=
    (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have ht := (fullResourceDeficitFloor_scaled_tendsto p).eventually
    (eventually_gt_nhds (sub_lt_self (asymptoticCoefficient p) hε))
  filter_upwards [ht, hfloor] with L hL hF
  intro layers hm
  have hc := (mul_le_mul_of_nonneg_left (hF layers hm) hα.le).trans
    (exactTargetClass_normalizedDet_deficit hm)
  exact hL.le.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg (p.k * L)))

/-- The physical supremum receives the same full floor whenever its class is nonempty. -/
theorem exactTarget_optimal_full_floor_of_floor (p : PhysicalParameters)
    (hfloor : ∀ᶠ L : ℝ in atTop, ∀ layers ∈ exactTargetClass p L,
      ResourceFloor.beta p.k p.P p.Q p.M (ResourceFloor.fullCellCount p.k p.P L) ≤
        normalizedAbsorptionDet (stackReflectionLeft p.k layers)
          (stackReflectionRight p.k layers) (stackTransmission p.k layers)) :
    ∀ᶠ L : ℝ in atTop, (exactTargetClass p L).Nonempty →
      fullResourceDeficitFloor p L ≤ ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L := by
  filter_upwards [hfloor] with L hF
  intro hne
  exact exactTargetClass_optimal_deficit_of_normalizedDet_floor hne hF

#print axioms asymptoticCoefficient_eq_resource
#print axioms fullResourceDeficitFloor_scaled_tendsto
#print axioms physical_deficit_liminf_of_full_floor
#print axioms exactTarget_uniform_deficit_of_full_floor
#print axioms exactTarget_optimal_full_floor_of_floor

/-- Theorem 4.5 supplies the actual determinant floor uniformly on the exact target class. -/
theorem exactTarget_resource_full_floor_eventually (p : PhysicalParameters) :
    ∀ᶠ L : ℝ in atTop, ∀ layers ∈ exactTargetClass p L,
      ResourceFloor.beta p.k p.P p.Q p.M (ResourceFloor.fullCellCount p.k p.P L) ≤
        normalizedAbsorptionDet (stackReflectionLeft p.k layers)
          (stackReflectionRight p.k layers) (stackTransmission p.k layers) := by
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  filter_upwards [selectedResource_full_floor_eventually p.k_pos hP p.Q_pos p.M_pos]
    with L hF
  intro layers hm
  exact hF layers (selectedResourceClass_of_exactTarget hm)

/-- Section 5.1: the asymptotic deficit bound holds uniformly over the actual exact-target class. -/
theorem theorem51_uniform_lower (p : PhysicalParameters) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ layers ∈ exactTargetClass p L,
      asymptoticCoefficient p - ε ≤ (p.k * L) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k layers) :=
  exactTarget_uniform_deficit_of_full_floor p (exactTarget_resource_full_floor_eventually p) hε

/-- The uniform finite full-cell lower bound transfers to the physical supremum. -/
theorem theorem51_optimal_full_floor (p : PhysicalParameters) :
    ∀ᶠ L : ℝ in atTop, (exactTargetClass p L).Nonempty →
      fullResourceDeficitFloor p L ≤ ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L :=
  exactTarget_optimal_full_floor_of_floor p (exactTarget_resource_full_floor_eventually p)

/-- The sharp lower coefficient for the optimum, at every sufficiently large feasible budget. -/
theorem theorem51_optimal_uniform_lower (p : PhysicalParameters)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, (exactTargetClass p L).Nonempty →
      asymptoticCoefficient p - ε ≤ (p.k * L) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L) := by
  have ht := (fullResourceDeficitFloor_scaled_tendsto p).eventually
    (eventually_gt_nhds (sub_lt_self (asymptoticCoefficient p) hε))
  filter_upwards [ht, theorem51_optimal_full_floor p] with L hL hF
  intro hne
  exact hL.le.trans (mul_le_mul_of_nonneg_left (hF hne) (sq_nonneg (p.k * L)))

/-- The universal lower half of the optimal asymptotic limit; the matching construction
must separately establish eventual nonemptiness of the exact target class. -/
theorem theorem51_optimal_lowerlimit (p : PhysicalParameters)
    (hne : ∀ᶠ L : ℝ in atTop, (exactTargetClass p L).Nonempty) :
    (asymptoticCoefficient p : EReal) ≤
      liminf (fun L : ℝ => ((p.k * L) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - optimalAsymmetry p L) : EReal)) atTop := by
  apply physical_deficit_liminf_of_full_floor p
  filter_upwards [theorem51_optimal_full_floor p, hne] with L hF hN
  exact hF hN

/-- Every sequence of actual exact-target physical stacks obeys the same lower coefficient. -/
theorem theorem51_sequence_lowerlimit (p : PhysicalParameters)
    (L : ℕ → ℝ) (layers : ℕ → List HomogeneousLayer)
    (hL : Tendsto L atTop atTop)
    (hphysical : ∀ j, layers j ∈ exactTargetClass p (L j)) :
    (asymptoticCoefficient p : EReal) ≤
      liminf (fun j => ((p.k * L j) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k (layers j)) : EReal)) atTop := by
  have hα : 0 < ScalarEnvelope.alpha p.T p.a :=
    (ScalarEnvelope.active_target_properties p.active).2.2.2.2.2.2.2
  have hte := EReal.tendsto_coe.mpr ((fullResourceDeficitFloor_scaled_tendsto p).comp hL)
  rw [← hte.liminf_eq]
  apply Filter.liminf_le_liminf
  filter_upwards [hL.eventually (exactTarget_resource_full_floor_eventually p)] with j hF
  have hc := (mul_le_mul_of_nonneg_left (hF (layers j) (hphysical j)) hα.le).trans
    (exactTargetClass_normalizedDet_deficit (hphysical j))
  exact_mod_cast mul_le_mul_of_nonneg_left hc (sq_nonneg (p.k * L j))
  all_goals isBoundedDefault

#print axioms exactTarget_resource_full_floor_eventually
#print axioms theorem51_uniform_lower
#print axioms theorem51_optimal_full_floor
#print axioms theorem51_optimal_uniform_lower
#print axioms theorem51_optimal_lowerlimit
#print axioms theorem51_sequence_lowerlimit
end OQ7


