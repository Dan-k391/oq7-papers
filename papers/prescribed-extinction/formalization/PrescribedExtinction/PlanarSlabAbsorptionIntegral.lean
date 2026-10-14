import PrescribedExtinction.PlanarReflectedLayer
import PrescribedExtinction.PlanarSlabStrictAbsorption

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem dielectricSlabLeft_absorptance_integral (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    k * q * (∫ z in (0 : ℝ)..d, Complex.normSq
      (OQ7.layerElectricField k (dielectricSlab p q d)
        (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) z)) =
      OQ7.absorptanceLeft (dielectricSlabReflection k p q d) (dielectricSlabTransmission k p q d) := by
  let E := OQ7.layerElectricField k (dielectricSlab p q d)
    (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d)
  let H := OQ7.layerMagneticField k (dielectricSlab p q d)
    (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d)
  let f := fun z => OQ7.directedFlux (E z) (H z)
  have hf (z : ℝ) : HasDerivAt f (-k * q * Complex.normSq (E z)) z :=
    OQ7.layerDirectedFlux_hasDerivAt k hp _ _ z
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf z).continuousAt
  have hEc : Continuous E := continuous_iff_continuousAt.mpr fun z =>
    (OQ7.layerElectricField_maxwell k hp _ _ z).continuousAt
  have hi : IntervalIntegrable (fun z => -k * q * Complex.normSq (E z)) volume 0 d :=
    (continuous_const.mul (Complex.continuous_normSq.comp hEc)).intervalIntegrable _ _
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hd hfc.continuousOn
    (fun z _ => hf z) hi
  rw [intervalIntegral.integral_const_mul] at hb
  have hbd := dielectricSlab_field_boundary k hk p q d hp hq hd
  have hfd : f d = Complex.normSq (dielectricSlabTransmission k p q d) := by
    change OQ7.directedFlux (E d) (H d) = _
    dsimp only [E, H]
    rw [hbd.1, hbd.2]
    exact directedFlux_transmitted _
  have hf0 : f 0 = 1 - Complex.normSq (dielectricSlabReflection k p q d) := by
    change OQ7.directedFlux (OQ7.electricField k _ _ _ 0) (OQ7.magneticField k _ _ _ 0) = _
    rw [(OQ7.homogeneousField_initial k _ _ _).1, (OQ7.homogeneousField_initial k _ _ _).2]
    exact directedFlux_incident_reflected _
  rw [hfd, hf0] at hb
  change k * q * (∫ z in (0 : ℝ)..d, Complex.normSq (E z)) = _
  unfold OQ7.absorptanceLeft
  linarith

theorem dielectricSlabRight_absorptance_integral (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    k * q * (∫ z in (0 : ℝ)..d, Complex.normSq ((dielectricSlabRightLayer k p q d hp).electric z)) =
      OQ7.absorptanceLeft (dielectricSlabReflection k p q d) (dielectricSlabTransmission k p q d) := by
  dsimp only [dielectricSlabRightLayer, PlanarLayerField.reflect, dielectricSlabLeftLayer, homogeneousPlanarLayerField]
  simp only [zero_add, sub_zero]
  rw [intervalIntegral.integral_comp_sub_left (fun z => Complex.normSq (OQ7.electricField k
    (OQ7.refractiveIndex (dielectricSlab p q d)) (1 + dielectricSlabReflection k p q d)
    (1 - dielectricSlabReflection k p q d) z)) d, sub_self, sub_zero]
  exact dielectricSlabLeft_absorptance_integral k hk p q d hp hq hd

end OQ7Prescribed
