import PrescribedExtinction.PlanarSlabFeedback
import PrescribedExtinction.PlanarSlabChannelGreen
import PrescribedExtinction.PlanarLayerCurrentAlgebra
import PrescribedExtinction.PlanarCoupledGreen
import PrescribedExtinction.PlanarDrive

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabAbsorberAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : Direction → ℂ
  | .plus => slabPlusAbsorberAmplitude k A W θ
  | .minus => slabMinusAbsorberAmplitude k A W θ

def slabPlateLeftAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : Direction → ℂ
  | .plus => slabPlusPlateAmplitude k A W θ
  | .minus => slabMinusPlateLeftAmplitude k A W θ

def slabPlateRightAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) : Direction → ℂ
  | .plus => 0
  | .minus => slabMinusRightAmplitude k A W

def slabLeftAuxiliaryIncident (k : ℝ) (A : OQ7.HomogeneousLayer) : Direction → ℂ
  | .plus => apertureOscillation k A.width
  | .minus => 0

theorem slabAmplitudes_feedback (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ)
    (hD : slabFeedback k A W θ ≠ 0) (σ : Direction) :
    slabAbsorberAmplitude k A W θ σ = (Real.cos θ : ℂ) *
      (dielectricSlabReflection k W.p W.q W.width * slabPlateLeftAmplitude k A W θ σ +
        (dielectricSlabTransmission k W.p W.q W.width - apertureOscillation k W.width) * slabPlateRightAmplitude k A W σ) ∧
    slabPlateLeftAmplitude k A W θ σ = slabLeftAuxiliaryIncident k A σ +
      (Real.cos θ : ℂ) * dielectricSlabReflection k A.p A.q A.width * slabAbsorberAmplitude k A W θ σ := by
  cases σ
  · constructor
    · simp only [slabAbsorberAmplitude, slabPlateLeftAmplitude, slabPlateRightAmplitude, mul_zero, add_zero]
      unfold slabPlusAbsorberAmplitude
      ring
    · exact slabPlusAmplitudes_feedback k A W θ hD
  · constructor
    · have h := slabMinusAmplitudes_feedback k A W θ hD
      simpa only [slabAbsorberAmplitude, slabPlateLeftAmplitude, slabPlateRightAmplitude, add_comm] using h
    · simp only [slabPlateLeftAmplitude, slabAbsorberAmplitude, slabLeftAuxiliaryIncident, zero_add,
        slabMinusPlateLeftAmplitude]

theorem slabAuxiliaryIncident_phase (k : ℝ) (A W : OQ7.HomogeneousLayer) (σ : Direction) (z : ℝ) :
    slabLeftAuxiliaryIncident k A σ * apertureOscillation k (z - A.width) +
      slabPlateRightAmplitude k A W σ * apertureOscillation k (A.width + W.width - z) = planarIncidentPhase k σ z := by
  cases σ
  · simp only [slabLeftAuxiliaryIncident, slabPlateRightAmplitude, zero_mul, add_zero,
      planarIncidentPhase, Direction.sign, one_mul]
    rw [← apertureOscillation_add]
    congr 1
    ring
  · simp only [slabLeftAuxiliaryIncident, slabPlateRightAmplitude, zero_mul, zero_add,
      slabMinusRightAmplitude, planarIncidentPhase, Direction.sign, neg_one_mul]
    unfold apertureOscillation
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

def slabCoupledAbsorber (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpA : 1 ≤ A.p) : PlanarLayerField k 0 A.width :=
  (dielectricSlabRightAt k A.p A.q 0 A.width hpA).const_mul (slabAbsorberAmplitude k A W θ σ)

def slabCoupledPlate (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpW : 1 ≤ W.p) : PlanarLayerField k A.width (A.width + W.width) :=
  ((dielectricSlabLeftAt k W.p W.q A.width (A.width + W.width) hpW).const_mul (slabPlateLeftAmplitude k A W θ σ)).add
    ((dielectricSlabRightAt k W.p W.q A.width (A.width + W.width) hpW).const_mul (slabPlateRightAmplitude k A W σ))

def slabCoupledCurrent (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) : PlanarCurrentL2 (A.width + W.width) :=
  planarLayerL2Current k 0 A.width (A.width + W.width) le_rfl hdA (by linarith) (slabCoupledAbsorber k A W θ σ hpA) +
    planarLayerL2Current k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl (slabCoupledPlate k A W θ σ hpW)

theorem slabCoupledAbsorber_constitutive (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpA : 1 ≤ A.p) (z : ℝ) :
    (slabCoupledAbsorber k A W θ σ hpA).current z =
      (OQ7.relativePermittivity A - 1) * (slabCoupledAbsorber k A W θ σ hpA).electric z := by
  dsimp only [slabCoupledAbsorber, PlanarLayerField.const_mul]
  rw [dielectricSlabRightAt_constitutive]
  dsimp only [OQ7.relativePermittivity]
  ring

theorem slabCoupledPlate_constitutive (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpW : 1 ≤ W.p) (z : ℝ) :
    (slabCoupledPlate k A W θ σ hpW).current z =
      (OQ7.relativePermittivity W - 1) * (slabCoupledPlate k A W θ σ hpW).electric z := by
  dsimp only [slabCoupledPlate, PlanarLayerField.add, PlanarLayerField.const_mul]
  rw [dielectricSlabLeftAt_constitutive, dielectricSlabRightAt_constitutive]
  dsimp only [OQ7.relativePermittivity]
  ring

end OQ7Prescribed
