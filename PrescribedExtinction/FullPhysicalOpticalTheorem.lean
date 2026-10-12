import PrescribedExtinction.ArbitraryStateOpticalBalance
import PrescribedExtinction.ScatteringStatePhysicalRadiation

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Filter
open scoped Topology

/-- The full physical optical theorem uses the original work, absorption,
and all-angle scattering definitions. The actual radiating representative
is proved to represent the weak solution and its physical sphere power
converges to the original S. -/
def FullPhysicalOpticalStatement (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (s : ScatteringState k B σ) : Prop :=
  s.electric =ᵐ[volume] (fun x => incidentElectric k σ x + scatteringStateRadiatingElectric s x) ∧
    s.magnetic =ᵐ[volume] (fun x => incidentMagnetic k σ x + scatteringStateRadiatingMagnetic s x) ∧
    extinction k B σ s.electric = absorption k B s.electric + scattering k B s.electric ∧
    extinction k B σ s.electric = (4 * Real.pi / k) *
      (pairing (basisC 1) (currentFarField k B s.electric (incidentForwardDirection σ))).im ∧
    scattering k B s.electric = (∫ n : UnitSphere, ‖currentFarField k B s.electric n‖ ^ 2 ∂sphereArea) ∧
    Tendsto (scatteringStateSphereFlux s) atTop (𝓝 (scattering k B s.electric)) ∧
    (let p := physicalCompactPolarization B s.electric s.maxwell.1
      ∀ r : ℝ, 2 * p.radius + 2 ≤ r → ∀ n : UnitSphere,
        ‖((r : ℂ) * Complex.exp (-Complex.I * ((k * r : ℝ) : ℂ))) •
          scatteringStateRadiatingElectric s (r • (n : Position)) - currentFarField k B s.electric n‖ ≤
          farFieldKernelConstant k p.radius / r * (∫ y : Position, ‖p.current y‖))

theorem scatteringState_full_optical_theorem (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) : FullPhysicalOpticalStatement k B σ s := by
  have hrep := scatteringState_radiating_representative k hk B σ s
  exact ⟨hrep.1, hrep.2, scatteringState_energy_balance k hk B σ s,
    scatteringState_forward_optical_theorem k hk B σ s,
    physicalScattering_eq_Haar k B s.electric s.maxwell.1,
    scatteringState_scattering_is_physical_flux k B σ s,
    scatteringState_currentFarField_is_physical k B σ s⟩

end OQ7Prescribed
