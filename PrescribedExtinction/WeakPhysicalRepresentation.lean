import PrescribedExtinction.VacuumOutgoingWeakUniqueness
import PrescribedExtinction.WeakScatteringResidual

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

/-- The converse volume representation holds for every original weak
scattering state, without assuming a material volume equation. -/
theorem scatteringState_outgoing_volume_representation (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (σ : Direction) (s : ScatteringState k B σ) :
    let p := physicalCompactPolarization B s.electric s.maxwell.1
    s.electric =ᵐ[volume] volumeTotalElectric k σ p ∧
      s.magnetic =ᵐ[volume] volumeTotalMagnetic k σ p := by
  let p := physicalCompactPolarization B s.electric s.maxwell.1
  obtain ⟨hE, hH, he, hh, hout⟩ := scatteringState_vacuum_residual k B σ s
  have hz := vacuum_outgoing_weak_unique_zero k hk _ _ hE hH he hh hout
  constructor
  · filter_upwards [hz.1] with x hx
    change s.electric x - volumeTotalElectric k σ p x = 0 at hx
    exact sub_eq_zero.mp hx
  · filter_upwards [hz.2] with x hx
    change s.magnetic x - volumeTotalMagnetic k σ p x = 0 at hx
    exact sub_eq_zero.mp hx

theorem scatteringState_converse_material_volume_equation (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (σ : Direction) (s : ScatteringState k B σ) :
    MaterialVolumeEquation k B σ (physicalCompactPolarization B s.electric s.maxwell.1) := by
  have h := (scatteringState_outgoing_volume_representation k hk B σ s).1
  filter_upwards [h] with x hx
  change polarization B s.electric x = polarization B
    (volumeTotalElectric k σ (physicalCompactPolarization B s.electric s.maxwell.1)) x
  unfold polarization
  rw [hx]

end OQ7Prescribed
