import PrescribedExtinction.Materials
import PrescribedExtinction.Maxwell

/-! Only the exact material projection of the incident field is proved here.
The Fredholm inverse and its uniform bounds remain unverified. -/
noncomputable section
namespace OQ7Prescribed

theorem incident_absorber_coupling (k : ℝ) (σ : Direction) (x : Position) :
    axisCoupling (basisR 0) (incidentElectric k σ x) = 0 := by
  simp [axisCoupling, basisR, incidentElectric, basisC]

theorem incident_plate_coupling (θ k : ℝ) (σ : Direction) (x : Position) :
    axisCoupling (rotatedAxis θ) (incidentElectric k σ x) =
      (Real.sin θ : ℂ) * planePhase k σ x := by
  simp [axisCoupling, rotatedAxis, incidentElectric, basisC]

theorem incident_plate_rankOne (θ k : ℝ) (σ : Direction) (x : Position) :
    tensorApply (rankOne (rotatedAxis θ)) (incidentElectric k σ x) =
      ((Real.sin θ : ℂ) * planePhase k σ x) • complexify (rotatedAxis θ) := by
  rw [tensorApply_rankOne, incident_plate_coupling]

theorem incident_plate_rankOne_zero_angle (k : ℝ) (σ : Direction) (x : Position) :
    tensorApply (rankOne (rotatedAxis 0)) (incidentElectric k σ x) = 0 := by
  rw [incident_plate_rankOne]
  simp

end OQ7Prescribed
