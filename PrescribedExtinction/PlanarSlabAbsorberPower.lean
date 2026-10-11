import PrescribedExtinction.PlanarSlabIntegralPowers
import PrescribedExtinction.PlanarSlabAbsorptionIntegral
import PrescribedExtinction.PlanarActualLosslessPlate

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem dielectricSlabRightAt_absorptance_integral (k : ℝ) (hk : 0 < k)
    (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) :
    k * A.q * (∫ z in (0 : ℝ)..A.width, Complex.normSq
      ((dielectricSlabRightAt k A.p A.q 0 A.width hpA).electric z)) =
      OQ7.absorptanceLeft (dielectricSlabReflection k A.p A.q A.width)
        (dielectricSlabTransmission k A.p A.q A.width) := by
  have h := dielectricSlabRight_absorptance_integral k hk A.p A.q A.width hpA hqA hdA
  simpa only [dielectricSlabRightAt, dielectricSlabLeftAt, dielectricSlabRightLayer,
    dielectricSlabLeftLayer, sub_zero] using h

theorem slabIntegralAbsorption_absorber_part (k : ℝ) (hk : 0 < k)
    (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) :
    slabIntegralAbsorption k A W θ σ hpA hpW =
      Complex.normSq (slabAbsorberAmplitude k A W θ σ) *
        OQ7.absorptanceLeft (dielectricSlabReflection k A.p A.q A.width)
          (dielectricSlabTransmission k A.p A.q A.width) +
        k * W.q * (∫ z in A.width..(A.width + W.width), Complex.normSq
          ((slabCoupledPlate k A W θ σ hpW).electric z)) := by
  unfold slabIntegralAbsorption
  dsimp only [slabCoupledAbsorber, PlanarLayerField.const_mul]
  simp only [Complex.normSq_mul]
  rw [intervalIntegral.integral_const_mul]
  rw [show k * (A.q * (Complex.normSq (slabAbsorberAmplitude k A W θ σ) *
      (∫ z in (0 : ℝ)..A.width, Complex.normSq ((dielectricSlabRightAt k A.p A.q 0 A.width hpA).electric z))) +
      W.q * (∫ z in A.width..(A.width + W.width), Complex.normSq ((slabCoupledPlate k A W θ σ hpW).electric z))) =
      Complex.normSq (slabAbsorberAmplitude k A W θ σ) *
        (k * A.q * (∫ z in (0 : ℝ)..A.width, Complex.normSq ((dielectricSlabRightAt k A.p A.q 0 A.width hpA).electric z))) +
      k * W.q * (∫ z in A.width..(A.width + W.width), Complex.normSq ((slabCoupledPlate k A W θ σ hpW).electric z)) by ring]
  rw [dielectricSlabRightAt_absorptance_integral k hk A hpA hqA hdA]

theorem losslessPlateDesign_coupled_amplitudes (k : ℝ) (hk : 0 < k)
    (A : OQ7.HomogeneousLayer) (j : ℕ) (hj : 1 ≤ j) :
    slabAbsorberAmplitude k A (dielectricSlab (plateDesignPermittivity j) 0 (plateDesignThickness k j)) 0 .plus = 0 ∧
    Complex.normSq (slabAbsorberAmplitude k A (dielectricSlab (plateDesignPermittivity j) 0 (plateDesignThickness k j)) 0 .minus) = 4 := by
  have hc := losslessPlateDesign_actual_coefficients k hk j hj
  have hp := losslessPlateDesign_vacuum_phase k hk j hj
  constructor
  · simp [slabAbsorberAmplitude, slabPlusAbsorberAmplitude, dielectricSlab, hc.1]
  · simp only [slabAbsorberAmplitude, slabMinusAbsorberAmplitude, slabMinusRightAmplitude,
      dielectricSlab, Real.cos_zero, Complex.ofReal_one, slabFeedback, hc.1, hc.2, hp,
      mul_zero, zero_mul, sub_zero, one_mul, div_one]
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (apertureOscillation (-k) _), apertureOscillation_norm]
    norm_num

theorem losslessPlateDesign_coupled_power_values (k : ℝ) (hk : 0 < k)
    (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width)
    (j : ℕ) (hj : 1 ≤ j) :
    let W := dielectricSlab (plateDesignPermittivity j) 0 (plateDesignThickness k j)
    let hpW : 1 ≤ W.p := by dsimp [W, dielectricSlab]; linarith [plateDesignPermittivity_pos_susceptibility j hj]
    slabIntegralAbsorption k A W 0 .plus hpA hpW = 0 ∧
    slabIntegralAbsorption k A W 0 .minus hpA hpW = 4 *
      OQ7.absorptanceLeft (dielectricSlabReflection k A.p A.q A.width)
        (dielectricSlabTransmission k A.p A.q A.width) ∧
    slabFormulaExtinction k A W 0 = 4 := by
  dsimp only
  have ha := losslessPlateDesign_coupled_amplitudes k hk A j hj
  have hc := losslessPlateDesign_actual_coefficients k hk j hj
  have hp := losslessPlateDesign_vacuum_phase k hk j hj
  have hpm : apertureOscillation (-k) (plateDesignThickness k j) = -1 := by
    have h := apertureOscillation_opposite_mul k (plateDesignThickness k j)
    rw [hp] at h
    have hn : -apertureOscillation (-k) (plateDesignThickness k j) = 1 := by simpa using h
    exact neg_eq_iff_eq_neg.mp hn
  constructor
  · rw [slabIntegralAbsorption_absorber_part k hk A _ 0 .plus hpA _ hqA hdA, ha.1]
    simp [dielectricSlab]
  constructor
  · rw [slabIntegralAbsorption_absorber_part k hk A _ 0 .minus hpA _ hqA hdA, ha.2]
    simp [dielectricSlab]
  · norm_num [slabFormulaExtinction, slabFeedback, dielectricSlab, hc.1, hc.2, hpm]

end OQ7Prescribed
