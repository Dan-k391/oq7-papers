import work.SphericalAngular
import PrescribedExtinction.FarFieldWorkL2

noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem physicalVolume_scattering_eq_Haar (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    scattering k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) =
      ∫ n : UnitSphere, ‖currentFarField k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) n‖ ^ 2 ∂sphereArea := by
  simp_rw [volumePhysicalFarField_eq k B σ f hp, scattering, squareNorm_eq_norm_sq]
  simp_rw [volumePhysicalFarField_eq k B σ f hp]
  exact (sphereArea_integral_original_angles
    (fun n => ‖compactCurrentFarField k (bodyCurrentPolarization B f) n‖ ^ 2)
    ((compactCurrentFarField_continuous k _).norm.pow 2)).symm

/-- The original physical extinction, dielectric absorption, and theta/phi
radiation cross sections satisfy the exact optical work identity. -/
theorem physicalVolume_energy_balance (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    extinction k B σ (volumeTotalElectric k σ (bodyCurrentPolarization B f)) =
      absorption k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) +
        scattering k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) := by
  rw [physicalVolume_scattering_eq_Haar k B σ f hp]
  exact physicalVolume_Haar_energy_balance k B σ f hp

theorem physicalVolume_scattering_nonneg (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    0 ≤ scattering k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) := by
  rw [physicalVolume_scattering_eq_Haar k B σ f hp]
  exact integral_nonneg (fun _ => sq_nonneg _)

end OQ7Prescribed
