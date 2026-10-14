import work.PhysicalPowersAE
import PrescribedExtinction.WeakPhysicalUniqueness
import PrescribedExtinction.PhysicalOpticalBalance
import PrescribedExtinction.ExtinctionReciprocity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem materialVolumeEquation_congr_current (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p q : CompactPolarization) (hp : MaterialVolumeEquation k B σ p)
    (h : p.current =ᵐ[volume] q.current) : MaterialVolumeEquation k B σ q := by
  filter_upwards [hp, h, volumeTotalElectric_congr_current_ae k σ p q h] with x hx hc he
  change q.current x = polarization B (volumeTotalElectric k σ q) x
  rw [← hc, hx]
  unfold polarization
  rw [he]

theorem scatteringState_body_volume_representation (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (σ : Direction) (s : ScatteringState k B σ) :
    ∃ f : BodyCurrentL2 B, MaterialVolumeEquation k B σ (bodyCurrentPolarization B f) ∧
      s.electric =ᵐ[volume] volumeTotalElectric k σ (bodyCurrentPolarization B f) ∧
      s.magnetic =ᵐ[volume] volumeTotalMagnetic k σ (bodyCurrentPolarization B f) := by
  let p := physicalCompactPolarization B s.electric s.maxwell.1
  have hp := scatteringState_converse_material_volume_equation k hk B σ s
  let f := materialVolumeCurrent k B σ p hp
  let q := bodyCurrentPolarization B f
  have hq : q.current =ᵐ[volume] p.current :=
    (bodyCurrentPolarization_current_ae B f).trans (materialVolumeCurrent_coe k B σ p hp)
  have hs := scatteringState_outgoing_volume_representation k hk B σ s
  refine ⟨f, materialVolumeEquation_congr_current k B σ p q hp hq.symm,
    hs.1.trans (volumeTotalElectric_congr_current_ae k σ p q hq.symm), ?_⟩
  have hmag : volumeTotalMagnetic k σ p =ᵐ[volume] volumeTotalMagnetic k σ q :=
    ae_of_all _ fun x => congrFun (volumeTotalMagnetic_congr_current k σ p q hq.symm) x
  exact hs.2.trans hmag

/-- Full energy balance for every original outgoing weak Maxwell state. -/
theorem scatteringState_energy_balance (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) :
    extinction k B σ s.electric = absorption k B s.electric + scattering k B s.electric := by
  obtain ⟨f, hp, he, _⟩ := scatteringState_body_volume_representation k hk B σ s
  rw [extinction_congr_ae k B σ _ _ he, absorption_congr_ae k B _ _ he, scattering_congr_ae k B _ _ he]
  exact physicalVolume_energy_balance k B σ f hp

/-- Reciprocity gives the common extinction for every pair of original
opposite-incidence weak scattering states of the same reciprocal body. -/
theorem scatteringState_extinction_reciprocity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (ha : B.absorberPermittivity.transpose = B.absorberPermittivity)
    (hb : B.platePermittivity.transpose = B.platePermittivity)
    (sp : ScatteringState k B .plus) (sm : ScatteringState k B .minus) :
    extinction k B .plus sp.electric = extinction k B .minus sm.electric := by
  have hp := scatteringState_converse_material_volume_equation k hk B .plus sp
  have hq := scatteringState_converse_material_volume_equation k hk B .minus sm
  have he := (scatteringState_outgoing_volume_representation k hk B .plus sp).1
  have hm := (scatteringState_outgoing_volume_representation k hk B .minus sm).1
  rw [extinction_congr_ae k B .plus _ _ he, extinction_congr_ae k B .minus _ _ hm]
  exact physicalVolume_extinction_reciprocity k hk B ha hb _ _ hp hq

end OQ7Prescribed
