import PrescribedExtinction.PlanarSlabGreenField

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set

def PlanarLayerField.reflect {k a b : ℝ} (F : PlanarLayerField k a b) : PlanarLayerField k a b := by
  let r := fun t : ℝ => a + b - t
  have hc : Continuous r := continuous_const.sub continuous_id
  have hm : MapsTo r (Icc a b) (Icc a b) := by intro t ht; dsimp [r]; constructor <;> linarith [ht.1, ht.2]
  have ho : MapsTo r (Ioo a b) (Ioo a b) := by intro t ht; dsimp [r]; constructor <;> linarith [ht.1, ht.2]
  refine ⟨fun t => F.electric (r t), fun t => -F.magnetic (r t), fun t => F.current (r t),
    F.electric_continuous.comp hc.continuousOn hm,
    (F.magnetic_continuous.comp hc.continuousOn hm).neg,
    F.current_continuous.comp hc.continuousOn hm, ?_, ?_⟩
  · intro t ht
    convert (F.electric_derivative (r t) (ho ht)).scomp t
      ((hasDerivAt_const t (a + b)).sub (hasDerivAt_id t)) using 1
    · rfl
    · simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_zero, Complex.ofReal_one]; ring
  · intro t ht
    convert ((F.magnetic_derivative (r t) (ho ht)).scomp t
      ((hasDerivAt_const t (a + b)).sub (hasDerivAt_id t))).neg using 1
    · rfl
    · simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_zero, Complex.ofReal_one]; ring

def dielectricSlabRightLayer (k p q d : ℝ) (hp : 1 ≤ p) : PlanarLayerField k 0 d :=
  (dielectricSlabLeftLayer k p q d hp).reflect

theorem dielectricSlabRightLayer_boundary (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    (dielectricSlabRightLayer k p q d hp).electric 0 = dielectricSlabTransmission k p q d ∧
    (dielectricSlabRightLayer k p q d hp).magnetic 0 = -dielectricSlabTransmission k p q d ∧
    (dielectricSlabRightLayer k p q d hp).electric d = 1 + dielectricSlabReflection k p q d ∧
    (dielectricSlabRightLayer k p q d hp).magnetic d = dielectricSlabReflection k p q d - 1 := by
  have hb := dielectricSlab_field_boundary k hk p q d hp hq hd
  dsimp only [dielectricSlabRightLayer, PlanarLayerField.reflect, dielectricSlabLeftLayer, homogeneousPlanarLayerField]
  simp only [zero_add, sub_zero, sub_self, (OQ7.homogeneousField_initial k _ _ _).1,
    (OQ7.homogeneousField_initial k _ _ _).2]
  exact ⟨hb.1, congrArg Neg.neg hb.2, trivial, by ring⟩

end OQ7Prescribed
