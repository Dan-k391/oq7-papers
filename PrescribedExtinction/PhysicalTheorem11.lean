import PrescribedExtinction.FullPhysicalOpticalTheorem
import PrescribedExtinction.UniversalPhysicalBounds

noncomputable section
namespace OQ7Prescribed
open MeasureTheory

/-- Complete manuscript Theorem 1.1: the exact preserved existence
statement, both prescribed-extinction suprema, universal strict
nonattainment, and the physical Maxwell/optical/reciprocity certificates
that make the original X, A, S and Gamma the manuscript's powers. -/
def PhysicalTheorem11Statement : Prop :=
  Theorem11Statement ∧
  ∀ k P Q target : ℝ, 0 < k → 1 < P → 0 < Q → 0 < target →
    sSup (prescribedExtinctionAsymmetryValues k P Q target) = 1 ∧
      sSup (prescribedExtinctionDifferenceValues k P Q target) = target ∧
      (∀ B : TwoLayerBody, B.admissible P Q → ∀ σ : Direction,
        (∃ s : ScatteringState k B σ, ∀ t : ScatteringState k B σ,
          s.electric =ᵐ[volume] t.electric ∧ s.magnetic =ᵐ[volume] t.magnetic) ∧
        (∀ s : ScatteringState k B σ, FullPhysicalOpticalStatement k B σ s)) ∧
      (∀ B : TwoLayerBody, B.admissible P Q → ∀ sp : ScatteringState k B .plus,
        ∀ sm : ScatteringState k B .minus,
        extinction k B .plus sp.electric = extinction k B .minus sm.electric ∧
        0 ≤ normalizedAsymmetry k B sp.electric sm.electric ∧
        normalizedAsymmetry k B sp.electric sm.electric ≤ 1 ∧
        (0 < extinction k B .plus sp.electric → normalizedAsymmetry k B sp.electric sm.electric < 1) ∧
        normalizedAsymmetry k B sp.electric sm.electric =
          |scattering k B sp.electric - scattering k B sm.electric| / extinction k B .plus sp.electric) ∧
      (∀ s : PrescribedExtinctionPair k P Q target, s.asymmetry < 1 ∧ s.absorptionDifference < target)

theorem theorem11_complete : PhysicalTheorem11Statement := by
  refine ⟨theorem11, ?_⟩
  intro k P Q target hk hP hQ htarget
  refine ⟨prescribedExtinctionAsymmetryValues_sSup k P Q target hk hP hQ htarget,
    prescribedExtinctionDifferenceValues_sSup k P Q target hk hP hQ htarget, ?_, ?_, ?_⟩
  · intro B hB σ
    exact ⟨physicalScatteringState_wellposed_ae k hk P Q B hB σ,
      fun s => scatteringState_full_optical_theorem k hk B σ s⟩
  · intro B hB sp sm
    exact ⟨admissibleScatteringState_extinction_reciprocity k hk P Q B hB sp sm,
      universal_physical_asymmetry_nonneg k hk P Q B hB sp sm,
      universal_physical_asymmetry_le_one k hk P Q B hB sp sm,
      fun hX => universal_physical_asymmetry_lt_one k hk P Q B hB sp sm hX,
      universal_physical_asymmetry_eq_scattering_difference k hk P Q B hB sp sm⟩
  · intro s
    exact ⟨s.asymmetry_lt_one hk htarget, s.absorptionDifference_lt_target hk htarget⟩

end OQ7Prescribed
