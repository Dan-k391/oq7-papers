import PrescribedExtinction.PlanarSlabChannels

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem dielectricSlabLeftAt_Green_interior (k : ℝ) (hk : 0 < k) (p q a b L : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (z : ℝ) (hz : z ∈ Icc a b) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k a b L ha hab hb (dielectricSlabLeftAt k p q a b hp) : HeightL2) z =
        (dielectricSlabLeftAt k p q a b hp).electric z - apertureOscillation k (z - a) := by
  have h := scalarPlanarPotential_layer_interior k a b L hk.ne' ha hab hb
    (dielectricSlabLeftAt k p q a b hp) z hz
  have hv := dielectricSlabLeftAt_boundary k hk p q a b hp hq hab
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] at h
  convert h using 1 <;> ring

theorem dielectricSlabRightAt_Green_interior (k : ℝ) (hk : 0 < k) (p q a b L : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (z : ℝ) (hz : z ∈ Icc a b) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k a b L ha hab hb (dielectricSlabRightAt k p q a b hp) : HeightL2) z =
        (dielectricSlabRightAt k p q a b hp).electric z - apertureOscillation k (b - z) := by
  have h := scalarPlanarPotential_layer_interior k a b L hk.ne' ha hab hb
    (dielectricSlabRightAt k p q a b hp) z hz
  have hv := dielectricSlabRightAt_boundary k hk p q a b hp hq hab
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] at h
  convert h using 1 <;> ring

theorem dielectricSlabLeftAt_Green_exterior_left (k : ℝ) (hk : 0 < k) (p q a b L : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (z : ℝ) (hz : z ≤ a) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k a b L ha hab hb (dielectricSlabLeftAt k p q a b hp) : HeightL2) z =
        dielectricSlabReflection k p q (b - a) * apertureOscillation k (a - z) := by
  have h := scalarPlanarPotential_layer_exterior_left k a b L hk.ne' ha hab hb
    (dielectricSlabLeftAt k p q a b hp) z hz
  have hv := dielectricSlabLeftAt_boundary k hk p q a b hp hq hab
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] at h
  convert h using 1 <;> ring

theorem dielectricSlabRightAt_Green_exterior_right (k : ℝ) (hk : 0 < k) (p q a b L : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (z : ℝ) (hz : b ≤ z) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k a b L ha hab hb (dielectricSlabRightAt k p q a b hp) : HeightL2) z =
        dielectricSlabReflection k p q (b - a) * apertureOscillation k (z - b) := by
  have h := scalarPlanarPotential_layer_exterior_right k a b L hk.ne' ha hab hb
    (dielectricSlabRightAt k p q a b hp) z hz
  have hv := dielectricSlabRightAt_boundary k hk p q a b hp hq hab
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] at h
  convert h using 1 <;> ring

theorem dielectricSlabLeftAt_Green_exterior_right (k : ℝ) (hk : 0 < k) (p q a b L : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (z : ℝ) (hz : b ≤ z) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k a b L ha hab hb (dielectricSlabLeftAt k p q a b hp) : HeightL2) z =
        (dielectricSlabTransmission k p q (b - a) - apertureOscillation k (b - a)) * apertureOscillation k (z - b) := by
  have h := scalarPlanarPotential_layer_exterior_right k a b L hk.ne' ha hab hb
    (dielectricSlabLeftAt k p q a b hp) z hz
  have hv := dielectricSlabLeftAt_boundary k hk p q a b hp hq hab
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] at h
  have hpz : apertureOscillation k (z - a) = apertureOscillation k (z - b) * apertureOscillation k (b - a) := by
    rw [← apertureOscillation_add]
    congr 1
    ring
  rw [hpz] at h
  convert h using 1 <;> ring

theorem dielectricSlabRightAt_Green_exterior_left (k : ℝ) (hk : 0 < k) (p q a b L : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    (z : ℝ) (hz : z ≤ a) :
    (k ^ 2 : ℝ) • scalarPlanarPotential k
      (planarLayerL2Current k a b L ha hab hb (dielectricSlabRightAt k p q a b hp) : HeightL2) z =
        (dielectricSlabTransmission k p q (b - a) - apertureOscillation k (b - a)) * apertureOscillation k (a - z) := by
  have h := scalarPlanarPotential_layer_exterior_left k a b L hk.ne' ha hab hb
    (dielectricSlabRightAt k p q a b hp) z hz
  have hv := dielectricSlabRightAt_boundary k hk p q a b hp hq hab
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] at h
  have hpz : apertureOscillation k (b - z) = apertureOscillation k (a - z) * apertureOscillation k (b - a) := by
    rw [← apertureOscillation_add]
    congr 1
    ring
  rw [hpz] at h
  convert h using 1 <;> ring

end OQ7Prescribed
