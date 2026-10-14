import PrescribedExtinction.PlanarSlabCoupledFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem slabCoupledAbsorber_Green_interior (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (z : ℝ) (hz : z ∈ Icc 0 A.width) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k 0 A.width (A.width + W.width) le_rfl hdA (by linarith)
        (slabCoupledAbsorber k A W θ σ hpA) : HeightL2) z =
      (slabCoupledAbsorber k A W θ σ hpA).electric z -
        slabAbsorberAmplitude k A W θ σ * apertureOscillation k (A.width - z) := by
  unfold slabCoupledAbsorber
  rw [planarLayerL2Current_const_mul, scalarPlanarPotential_supported_smul,
    dielectricSlabRightAt_Green_interior k hk A.p A.q 0 A.width (A.width + W.width) hpA hqA le_rfl hdA (by linarith) z hz]
  dsimp only [PlanarLayerField.const_mul]
  ring

theorem slabCoupledAbsorber_Green_exterior_right (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (z : ℝ) (hz : A.width ≤ z) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k 0 A.width (A.width + W.width) le_rfl hdA (by linarith)
        (slabCoupledAbsorber k A W θ σ hpA) : HeightL2) z =
      slabAbsorberAmplitude k A W θ σ * dielectricSlabReflection k A.p A.q A.width * apertureOscillation k (z - A.width) := by
  unfold slabCoupledAbsorber
  rw [planarLayerL2Current_const_mul, scalarPlanarPotential_supported_smul,
    dielectricSlabRightAt_Green_exterior_right k hk A.p A.q 0 A.width (A.width + W.width) hpA hqA le_rfl hdA (by linarith) z hz,
    sub_zero]
  ring

theorem slabCoupledPlate_Green_interior (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpW : 1 ≤ W.p) (hqW : 0 ≤ W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (z : ℝ) (hz : z ∈ Icc A.width (A.width + W.width)) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl
        (slabCoupledPlate k A W θ σ hpW) : HeightL2) z =
      (slabCoupledPlate k A W θ σ hpW).electric z -
        slabPlateLeftAmplitude k A W θ σ * apertureOscillation k (z - A.width) -
        slabPlateRightAmplitude k A W σ * apertureOscillation k (A.width + W.width - z) := by
  unfold slabCoupledPlate
  rw [planarLayerL2Current_add, planarLayerL2Current_const_mul, planarLayerL2Current_const_mul,
    scalarPlanarPotential_supported_add k hk _ (by linarith), scalarPlanarPotential_supported_smul,
    scalarPlanarPotential_supported_smul,
    dielectricSlabLeftAt_Green_interior k hk W.p W.q A.width (A.width + W.width) (A.width + W.width) hpW hqW hdA (by linarith) le_rfl z hz,
    dielectricSlabRightAt_Green_interior k hk W.p W.q A.width (A.width + W.width) (A.width + W.width) hpW hqW hdA (by linarith) le_rfl z hz]
  dsimp only [PlanarLayerField.add, PlanarLayerField.const_mul]
  ring

theorem slabCoupledPlate_Green_exterior_left (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (σ : Direction) (hpW : 1 ≤ W.p) (hqW : 0 ≤ W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width)
    (z : ℝ) (hz : z ≤ A.width) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k A.width (A.width + W.width) (A.width + W.width) hdA (by linarith) le_rfl
        (slabCoupledPlate k A W θ σ hpW) : HeightL2) z =
      (dielectricSlabReflection k W.p W.q W.width * slabPlateLeftAmplitude k A W θ σ +
        (dielectricSlabTransmission k W.p W.q W.width - apertureOscillation k W.width) * slabPlateRightAmplitude k A W σ) *
        apertureOscillation k (A.width - z) := by
  unfold slabCoupledPlate
  rw [planarLayerL2Current_add, planarLayerL2Current_const_mul, planarLayerL2Current_const_mul,
    scalarPlanarPotential_supported_add k hk _ (by linarith), scalarPlanarPotential_supported_smul,
    scalarPlanarPotential_supported_smul,
    dielectricSlabLeftAt_Green_exterior_left k hk W.p W.q A.width (A.width + W.width) (A.width + W.width) hpW hqW hdA (by linarith) le_rfl z hz,
    dielectricSlabRightAt_Green_exterior_left k hk W.p W.q A.width (A.width + W.width) (A.width + W.width) hpW hqW hdA (by linarith) le_rfl z hz,
    add_sub_cancel_left]
  ring

end OQ7Prescribed
