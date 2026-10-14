import work.PlanarSlabCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def dielectricSlabLeftLayer (k p q d : ℝ) (hp : 1 ≤ p) : PlanarLayerField k 0 d :=
  homogeneousPlanarLayerField k 0 d 0 (OQ7.refractiveIndex (dielectricSlab p q d))
    (OQ7.refractiveIndex_ne_zero hp)
    (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d)

def dielectricSlabRightVacuumPoint (k p q d : ℝ) : PlanarLayerField k d d :=
  homogeneousPlanarLayerField k d d d 1 (by norm_num)
    (dielectricSlabTransmission k p q d) (dielectricSlabTransmission k p q d)

def dielectricSlabLeftCurrent (k p q d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d) : PlanarCurrentL2 d :=
  planarTwoLayerL2Current k d d hd le_rfl (dielectricSlabLeftLayer k p q d hp) (dielectricSlabRightVacuumPoint k p q d)

theorem dielectricSlabLeftLayer_boundary_matching (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    (dielectricSlabLeftLayer k p q d hp).electric d = (dielectricSlabRightVacuumPoint k p q d).electric d ∧
    (dielectricSlabLeftLayer k p q d hp).magnetic d = (dielectricSlabRightVacuumPoint k p q d).magnetic d := by
  have hb := dielectricSlab_field_boundary k hk p q d hp hq hd
  constructor
  · change OQ7.electricField k (OQ7.refractiveIndex (dielectricSlab p q d))
      (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) (d - 0) =
        OQ7.electricField k 1 (dielectricSlabTransmission k p q d) (dielectricSlabTransmission k p q d) (d - d)
    rw [sub_zero, sub_self, (OQ7.homogeneousField_initial k 1 _ _).1]
    exact hb.1
  · change OQ7.magneticField k (OQ7.refractiveIndex (dielectricSlab p q d))
      (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) (d - 0) =
        OQ7.magneticField k 1 (dielectricSlabTransmission k p q d) (dielectricSlabTransmission k p q d) (d - d)
    rw [sub_zero, sub_self, (OQ7.homogeneousField_initial k 1 _ _).2]
    exact hb.2

theorem dielectricSlabLeftCurrent_Green_equation (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) (z : ℝ) (hz : z ∈ Icc 0 d) :
    OQ7.layerElectricField k (dielectricSlab p q d)
        (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) z =
      planarIncidentPhase k .plus z +
        (k ^ 2 : ℝ) • scalarPlanarPotential k (dielectricSlabLeftCurrent k p q d hp hd : HeightL2) z := by
  have hm := dielectricSlabLeftLayer_boundary_matching k hk p q d hp hq hd
  have hleft : (dielectricSlabLeftLayer k p q d hp).magnetic 0 +
      (dielectricSlabLeftLayer k p q d hp).electric 0 = 2 := by
    simp [dielectricSlabLeftLayer, homogeneousPlanarLayerField, OQ7.electricField, OQ7.magneticField] <;> ring
  have hright : (dielectricSlabRightVacuumPoint k p q d).magnetic d -
      (dielectricSlabRightVacuumPoint k p q d).electric d = 0 := by
    simp [dielectricSlabRightVacuumPoint, homogeneousPlanarLayerField, OQ7.electricField, OQ7.magneticField]
  have he := planarTwoLayer_plus_incident_equation k d d z hk.ne' hd le_rfl hz
    (dielectricSlabLeftLayer k p q d hp) (dielectricSlabRightVacuumPoint k p q d) hm.1 hm.2 hleft hright
  rw [if_pos hz.2] at he
  change OQ7.electricField k (OQ7.refractiveIndex (dielectricSlab p q d))
      (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) (z - 0) =
    planarIncidentPhase k .plus z +
      (k ^ 2 : ℝ) • scalarPlanarPotential k (dielectricSlabLeftCurrent k p q d hp hd : HeightL2) z at he
  rw [sub_zero] at he
  exact he

theorem dielectricSlabLeftCurrent_constitutive_coe (k p q d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d) :
    (dielectricSlabLeftCurrent k p q d hp hd : HeightL2) =ᵐ[volume]
      (Ioc 0 d).indicator (fun z => ((p : ℂ) + Complex.I * (q : ℂ) - 1) *
        OQ7.layerElectricField k (dielectricSlab p q d)
          (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) z) := by
  filter_upwards [planarTwoLayerL2Current_coe k d d hd le_rfl
    (dielectricSlabLeftLayer k p q d hp) (dielectricSlabRightVacuumPoint k p q d)] with z hz
  change (planarTwoLayerL2Current k d d hd le_rfl (dielectricSlabLeftLayer k p q d hp)
    (dielectricSlabRightVacuumPoint k p q d) : HeightL2) z = _
  rw [hz]
  simp only [planarTwoLayerCurrent, Ioc_self, indicator_empty, add_zero]
  by_cases hm : z ∈ Ioc 0 d
  · simp only [indicator_of_mem hm]
    change (OQ7.refractiveIndex (dielectricSlab p q d) ^ 2 - 1) *
      OQ7.electricField k (OQ7.refractiveIndex (dielectricSlab p q d))
        (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) (z - 0) = _
    rw [sub_zero, OQ7.refractiveIndex_sq]
    rfl
  · simp only [indicator_of_notMem hm]

end OQ7Prescribed
