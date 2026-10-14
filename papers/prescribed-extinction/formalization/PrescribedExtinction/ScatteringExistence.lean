import PrescribedExtinction.MaterialBodyInverse
import PrescribedExtinction.VolumeScatteringBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical

theorem bodyIncident_memLp (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    MemLp (B.domain.indicator (incidentElectric k σ)) 2 volume := by
  rw [memLp_indicator_iff_restrict (bodyDomain_isOpen B).measurableSet]
  exact (incidentElectric_locallySquareIntegrable k σ (closure B.domain) (domain_compact_closure B)).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)

def bodyIncidentCurrent (k : ℝ) (B : TwoLayerBody) (σ : Direction) : BodyCurrentL2 B :=
  ⟨(bodyIncident_memLp k B σ).toLp (B.domain.indicator (incidentElectric k σ)), by
    change ∀ᵐ x ∂volume, x ∉ B.domain →
      ((bodyIncident_memLp k B σ).toLp (B.domain.indicator (incidentElectric k σ))) x = 0
    filter_upwards [(bodyIncident_memLp k B σ).coeFn_toLp] with x hx
    intro hxd
    rw [hx, indicator_of_notMem hxd]⟩

theorem bodyIncidentCurrent_coe (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    (bodyIncidentCurrent k B σ : VectorL2) =ᵐ[volume] B.domain.indicator (incidentElectric k σ) :=
  (bodyIncident_memLp k B σ).coeFn_toLp

def materialBodySolution (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) : BodyCurrentL2 B :=
  (materialBodyEquiv k hk B a b).symm (-bodyIncidentCurrent k B σ)

theorem materialBodySolution_equation (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) :
    materialBodyOperator k B a b (materialBodySolution k hk B σ a b) = -bodyIncidentCurrent k B σ := by
  rw [← materialBodyEquiv_apply k hk B a b]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

theorem materialBodySolution_physicalVolumeEquation (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) :
    MaterialVolumeEquation k B σ (bodyCurrentPolarization B (materialBodySolution k hk B σ a b)) := by
  let f := materialBodySolution k hk B σ a b
  let p := bodyCurrentPolarization B f
  have heq : (bodyOutgoingOperator k B f : VectorL2) - (bodyInverseSusceptibility B a b f : VectorL2) =
      -(bodyIncidentCurrent k B σ : VectorL2) :=
    congrArg (fun g : BodyCurrentL2 B => (g : VectorL2)) (materialBodySolution_equation k hk B σ a b)
  have ht := bodyOutgoingOperator_coe k B f
  have hj := bodyInverseSusceptibility_coe B a b f
  have hi := bodyIncidentCurrent_coe k B σ
  change p.current =ᵐ[volume] polarization B (volumeTotalElectric k σ p)
  filter_upwards [ht, hj, hi,
    Lp.coeFn_sub (bodyOutgoingOperator k B f : VectorL2) (bodyInverseSusceptibility B a b f : VectorL2),
    Lp.coeFn_neg (bodyIncidentCurrent k B σ : VectorL2), outgoingElectricField_eq_ae k p] with x hxT hxJ hxI hsub hneg hout
  have hx := congrArg (fun g : VectorL2 => g x) heq
  rw [hsub, hneg] at hx
  change (bodyOutgoingOperator k B f : VectorL2) x - (bodyInverseSusceptibility B a b f : VectorL2) x =
    -(bodyIncidentCurrent k B σ : VectorL2) x at hx
  rw [hxT, hxJ, hxI] at hx
  rw [physicalPolarization_indicator]
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd] at hx
    change B.domain.indicator (fun y => (f : VectorL2) y) x = _
    rw [indicator_of_mem hxd, indicator_of_mem hxd]
    change (f : VectorL2) x = if x 2 < B.absorberThickness then
      tensorMap (B.absorberPermittivity - 1) (incidentElectric k σ x + outgoingElectricField k p x)
      else tensorMap (B.platePermittivity - 1) (incidentElectric k σ x + outgoingElectricField k p x)
    rw [hout]
    by_cases hxa : x 2 < B.absorberThickness
    · simp only [hxa, ite_true] at hx ⊢
      have hjEq : a.inverse.symm ((f : VectorL2) x) = incidentElectric k σ x + electricVolumeField k p x := by
        have hh := (sub_eq_iff_eq_add).mp hx
        have hh' := congrArg (fun v : Vector => incidentElectric k σ x + v) hh
        simpa only [add_neg_cancel_left, add_comm] using hh'.symm
      have hh := congrArg a.inverse hjEq
      rw [ContinuousLinearEquiv.apply_symm_apply, a.forward_eq] at hh
      exact hh
    · simp only [hxa, ite_false] at hx ⊢
      have hjEq : b.inverse.symm ((f : VectorL2) x) = incidentElectric k σ x + electricVolumeField k p x := by
        have hh := (sub_eq_iff_eq_add).mp hx
        have hh' := congrArg (fun v : Vector => incidentElectric k σ x + v) hh
        simpa only [add_neg_cancel_left, add_comm] using hh'.symm
      have hh := congrArg b.inverse hjEq
      rw [ContinuousLinearEquiv.apply_symm_apply, b.forward_eq] at hh
      exact hh
  · change B.domain.indicator (fun y => (f : VectorL2) y) x = _
    rw [indicator_of_notMem hxd, indicator_of_notMem hxd]

theorem materialVolumeEquation_exists (k : ℝ) (hk : 0 < k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (σ : Direction) :
    ∃ p : CompactPolarization, MaterialVolumeEquation k B σ p := by
  let a := admissibleSusceptibilityInverseData P Q B.absorberPermittivity hB.1
  let b := admissibleSusceptibilityInverseData P Q B.platePermittivity hB.2
  exact ⟨bodyCurrentPolarization B (materialBodySolution k hk B σ a b),
    materialBodySolution_physicalVolumeEquation k hk B σ a b⟩

/-- Existence for the original physical fields and full uniform radiation condition. -/
theorem physicalScatteringState_exists (k : ℝ) (hk : 0 < k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (σ : Direction) : Nonempty (ScatteringState k B σ) := by
  obtain ⟨p, hp⟩ := materialVolumeEquation_exists k hk P Q B hB σ
  exact ⟨scatteringStateOfVolumeEquation k B σ p hp⟩

end OQ7Prescribed
