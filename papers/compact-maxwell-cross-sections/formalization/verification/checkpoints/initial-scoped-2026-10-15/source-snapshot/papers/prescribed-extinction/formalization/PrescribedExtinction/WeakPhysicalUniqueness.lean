import PrescribedExtinction.WeakPhysicalRepresentation
import PrescribedExtinction.MaterialVolumeUniqueness

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem outgoingElectricField_congr_current_ae (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : outgoingElectricField k p =ᵐ[volume] outgoingElectricField k q := by
  have he := electricVolumeField_congr_current k p q h
  have hmid : electricVolumeField k p =ᵐ[volume] electricVolumeField k q := ae_of_all _ fun x => congrFun he x
  exact (outgoingElectricField_eq_ae k p).trans (hmid.trans (outgoingElectricField_eq_ae k q).symm)

theorem gradientPotential_congr_current (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) (j : Fin 3) : gradientPotential k p j = gradientPotential k q j := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem outgoingMagneticField_congr_current (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : outgoingMagneticField k p = outgoingMagneticField k q := by
  funext x
  simp only [outgoingMagneticField, magneticVolumeField, potentialCurlField,
    gradientPotential_congr_current k p q h]

theorem volumeTotalElectric_congr_current_ae (k : ℝ) (σ : Direction) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : volumeTotalElectric k σ p =ᵐ[volume] volumeTotalElectric k σ q := by
  filter_upwards [outgoingElectricField_congr_current_ae k p q h] with x hx
  simp only [volumeTotalElectric, hx]

theorem volumeTotalMagnetic_congr_current (k : ℝ) (σ : Direction) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : volumeTotalMagnetic k σ p = volumeTotalMagnetic k σ q := by
  funext x
  simp only [volumeTotalMagnetic, outgoingMagneticField_congr_current k p q h]

/-- All original admissible outgoing weak Maxwell scattering states are
unique up to equality almost everywhere, for both actual fields. -/
theorem physicalScatteringState_unique_ae (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q) (σ : Direction)
    (s t : ScatteringState k B σ) :
    s.electric =ᵐ[volume] t.electric ∧ s.magnetic =ᵐ[volume] t.magnetic := by
  let p := physicalCompactPolarization B s.electric s.maxwell.1
  let q := physicalCompactPolarization B t.electric t.maxwell.1
  have hp := scatteringState_converse_material_volume_equation k hk B σ s
  have hq := scatteringState_converse_material_volume_equation k hk B σ t
  have hc := materialVolumeEquation_unique_current k hk P Q B hB σ p q hp hq
  have hs := scatteringState_outgoing_volume_representation k hk B σ s
  have ht := scatteringState_outgoing_volume_representation k hk B σ t
  constructor
  · exact hs.1.trans ((volumeTotalElectric_congr_current_ae k σ p q hc).trans ht.1.symm)
  · have hmid : volumeTotalMagnetic k σ p =ᵐ[volume] volumeTotalMagnetic k σ q :=
      ae_of_all _ fun x => congrFun (volumeTotalMagnetic_congr_current k σ p q hc) x
    exact hs.2.trans (hmid.trans ht.2.symm)

theorem physicalScatteringState_wellposed_ae (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q) (σ : Direction) :
    ∃ s : ScatteringState k B σ, ∀ t : ScatteringState k B σ,
      s.electric =ᵐ[volume] t.electric ∧ s.magnetic =ᵐ[volume] t.magnetic := by
  obtain ⟨s⟩ := physicalScatteringState_exists k hk P Q B hB σ
  exact ⟨s, fun t => physicalScatteringState_unique_ae k hk P Q B hB σ s t⟩

end OQ7Prescribed
