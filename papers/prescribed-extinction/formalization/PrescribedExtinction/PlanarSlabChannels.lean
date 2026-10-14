import PrescribedExtinction.PlanarSingleLayerCurrent

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def dielectricSlabLeftAt (k p q a b : ℝ) (hp : 1 ≤ p) : PlanarLayerField k a b :=
  homogeneousPlanarLayerField k a b a (OQ7.refractiveIndex (dielectricSlab p q (b - a)))
    (OQ7.refractiveIndex_ne_zero hp)
    (1 + dielectricSlabReflection k p q (b - a)) (1 - dielectricSlabReflection k p q (b - a))

def dielectricSlabRightAt (k p q a b : ℝ) (hp : 1 ≤ p) : PlanarLayerField k a b :=
  (dielectricSlabLeftAt k p q a b hp).reflect

theorem dielectricSlabLeftAt_boundary (k : ℝ) (hk : 0 < k) (p q a b : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hab : a ≤ b) :
    (dielectricSlabLeftAt k p q a b hp).electric a = 1 + dielectricSlabReflection k p q (b - a) ∧
    (dielectricSlabLeftAt k p q a b hp).magnetic a = 1 - dielectricSlabReflection k p q (b - a) ∧
    (dielectricSlabLeftAt k p q a b hp).electric b = dielectricSlabTransmission k p q (b - a) ∧
    (dielectricSlabLeftAt k p q a b hp).magnetic b = dielectricSlabTransmission k p q (b - a) := by
  have hb := dielectricSlab_field_boundary k hk p q (b - a) hp hq (sub_nonneg.mpr hab)
  dsimp only [dielectricSlabLeftAt, homogeneousPlanarLayerField]
  rw [sub_self, (OQ7.homogeneousField_initial k _ _ _).1, (OQ7.homogeneousField_initial k _ _ _).2]
  exact ⟨rfl, rfl, hb.1, hb.2⟩

theorem dielectricSlabRightAt_boundary (k : ℝ) (hk : 0 < k) (p q a b : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hab : a ≤ b) :
    (dielectricSlabRightAt k p q a b hp).electric a = dielectricSlabTransmission k p q (b - a) ∧
    (dielectricSlabRightAt k p q a b hp).magnetic a = -dielectricSlabTransmission k p q (b - a) ∧
    (dielectricSlabRightAt k p q a b hp).electric b = 1 + dielectricSlabReflection k p q (b - a) ∧
    (dielectricSlabRightAt k p q a b hp).magnetic b = dielectricSlabReflection k p q (b - a) - 1 := by
  have hb := dielectricSlabLeftAt_boundary k hk p q a b hp hq hab
  dsimp only [dielectricSlabRightAt, PlanarLayerField.reflect]
  rw [show a + b - a = b by ring, show a + b - b = a by ring,
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  exact ⟨rfl, rfl, rfl, by ring⟩

theorem dielectricSlabLeftAt_constitutive (k p q a b : ℝ) (hp : 1 ≤ p) (z : ℝ) :
    (dielectricSlabLeftAt k p q a b hp).current z =
      ((p : ℂ) + Complex.I * (q : ℂ) - 1) * (dielectricSlabLeftAt k p q a b hp).electric z := by
  change (OQ7.refractiveIndex (dielectricSlab p q (b - a)) ^ 2 - 1) * _ = _
  rw [OQ7.refractiveIndex_sq]
  rfl

theorem dielectricSlabRightAt_constitutive (k p q a b : ℝ) (hp : 1 ≤ p) (z : ℝ) :
    (dielectricSlabRightAt k p q a b hp).current z =
      ((p : ℂ) + Complex.I * (q : ℂ) - 1) * (dielectricSlabRightAt k p q a b hp).electric z :=
  dielectricSlabLeftAt_constitutive k p q a b hp (a + b - z)

theorem apertureOscillation_add (k a b : ℝ) :
    apertureOscillation k (a + b) = apertureOscillation k a * apertureOscillation k b := by
  unfold apertureOscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end OQ7Prescribed
