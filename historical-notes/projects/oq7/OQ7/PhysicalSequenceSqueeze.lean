import OQ7.ConstructionBudget
import OQ7.PhysicalLowerAsymptotics
import OQ7.StrictLoss
import OQ7.TargetBounds

noncomputable section
namespace OQ7
open Filter
open scoped Topology

/-- A genuinely physical construction sequence supplies every sufficiently large real budget.
All exact targets and the complete physical thickness remain explicit hypotheses. -/
theorem physical_sequence_budget_membership (p : PhysicalParameters)
    (layers : ℕ → List HomogeneousLayer) (C : ℝ)
    (hphysical : ∀ᶠ m : ℕ in atTop,
      StackAdmissible p.P p.Q (layers m) ∧ integratedLoss (layers m) = p.M ∧
      stackTransmissionPower p.k (layers m) = p.T ∧
      stackMeanAbsorptance p.k (layers m) = p.a ∧
      p.k * totalThickness (layers m) ≤ Real.pi * (m : ℝ) / Real.sqrt p.P + C) :
    ∀ᶠ L : ℝ in atTop,
      layers (constructionIndex p.k p.P C L) ∈ exactTargetClass p L := by
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  have hm := constructionIndex_atTop p.k_pos hP C
  have hs := constructionShift_atTop p.k_pos C
  filter_upwards [hm.eventually hphysical, hs.eventually (eventually_ge_atTop (0 : ℝ))]
    with L hphys hshift
  refine ⟨hphys.1, hphys.2.1, ?_, hphys.2.2.1, hphys.2.2.2.1⟩
  have hb := hphys.2.2.2.2.trans (constructionIndex_fits hP hshift)
  nlinarith [p.k_pos]

/-- The all-budget upper asymptotic derived from the integer physical sequence. -/
theorem physical_sequence_scaled_limit (p : PhysicalParameters)
    (layers : ℕ → List HomogeneousLayer) (C : ℝ)
    (hlimit : Tendsto
      (fun m : ℕ => (m : ℝ) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k (layers m))) atTop
      (𝓝 (ScalarEnvelope.alpha p.T p.a * (p.k * p.M) ^ 4 / (3 * p.Q ^ 2)))) :
    Tendsto (fun L : ℝ => (p.k * L) ^ 2 *
      (ScalarEnvelope.D0 p.T p.a -
        stackAsymmetry p.k (layers (constructionIndex p.k p.P C L)))) atTop
      (𝓝 (asymptoticCoefficient p)) := by
  have hP : 0 < p.P := lt_trans (by norm_num) p.P_gt_one
  have hs : Real.sqrt p.P ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  have hm := constructionIndex_atTop p.k_pos hP C
  have hr := (constructionIndex_ratio p.k_pos hP C).inv₀
    (show Real.sqrt p.P / Real.pi ≠ 0 by positivity)
  have hr' : Tendsto (fun L : ℝ => p.k * L / (constructionIndex p.k p.P C L : ℝ))
      atTop (𝓝 (Real.pi / Real.sqrt p.P)) := by
    simpa only [inv_div] using hr
  have ht := (hr'.pow 2).mul (hlimit.comp hm)
  have hc : (Real.pi / Real.sqrt p.P) ^ 2 *
      (ScalarEnvelope.alpha p.T p.a * (p.k * p.M) ^ 4 / (3 * p.Q ^ 2)) =
      asymptoticCoefficient p := by
    unfold asymptoticCoefficient
    rw [div_pow, Real.sq_sqrt hP.le]
    ring
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [hm.eventually (eventually_gt_atTop (0 : ℕ))] with L hmpos
  have hm0 : (constructionIndex p.k p.P C L : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  dsimp [Function.comp_def]
  field_simp

/-- Final reduction to a sequence of actual finite layers. The Section 5 construction
must still discharge both sequence hypotheses; this theorem does not claim it exists. -/
theorem theorem51_of_physical_constructed_sequence (p : PhysicalParameters)
    (layers : ℕ → List HomogeneousLayer) (C : ℝ)
    (hphysical : ∀ᶠ m : ℕ in atTop,
      StackAdmissible p.P p.Q (layers m) ∧ integratedLoss (layers m) = p.M ∧
      stackTransmissionPower p.k (layers m) = p.T ∧
      stackMeanAbsorptance p.k (layers m) = p.a ∧
      p.k * totalThickness (layers m) ≤ Real.pi * (m : ℝ) / Real.sqrt p.P + C)
    (hlimit : Tendsto
      (fun m : ℕ => (m : ℝ) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k (layers m))) atTop
      (𝓝 (ScalarEnvelope.alpha p.T p.a * (p.k * p.M) ^ 4 / (3 * p.Q ^ 2)))) :
    Theorem51Statement p := by
  have hmem := physical_sequence_budget_membership p layers C hphysical
  have hne : ∀ᶠ L : ℝ in atTop, (exactTargetClass p L).Nonempty := by
    filter_upwards [hmem] with L hL
    exact ⟨_, hL⟩
  refine ⟨hne, fun L layers h => exactTargetClass_strict_gap h, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (fullResourceDeficitFloor_scaled_tendsto p)
    (physical_sequence_scaled_limit p layers C hlimit)
  · filter_upwards [theorem51_optimal_full_floor p, hne] with L hF hN
    exact mul_le_mul_of_nonneg_left (hF hN) (sq_nonneg (p.k * L))
  · filter_upwards [hmem] with L hL
    exact mul_le_mul_of_nonneg_left (optimal_deficit_le_stack_deficit hL) (sq_nonneg (p.k * L))

#print axioms physical_sequence_budget_membership
#print axioms physical_sequence_scaled_limit
#print axioms theorem51_of_physical_constructed_sequence
end OQ7
