import PrescribedExtinction.PlanarSlabCoefficients
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open scoped Matrix

theorem directedFlux_incident_reflected (r : ℂ) :
    OQ7.directedFlux (1 + r) (1 - r) = 1 - Complex.normSq r := by
  simp [OQ7.directedFlux, Complex.star_def, Complex.mul_re, Complex.normSq_apply]
  ring

theorem directedFlux_transmitted (t : ℂ) : OQ7.directedFlux t t = Complex.normSq t := by
  simp [OQ7.directedFlux, Complex.star_def, Complex.mul_re, Complex.normSq_apply]

theorem dielectricSlab_absorptance_pos (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 < q) (hd : 0 < d) :
    0 < OQ7.absorptanceLeft (dielectricSlabReflection k p q d) (dielectricSlabTransmission k p q d) := by
  let r := dielectricSlabReflection k p q d
  let t := dielectricSlabTransmission k p q d
  have hi : (![1 + r, 1 - r] : Fin 2 → ℂ) ≠ 0 := by
    intro hz
    have h0 := congrArg (fun v : Fin 2 → ℂ => v 0) hz
    have h1 := congrArg (fun v : Fin 2 → ℂ => v 1) hz
    change 1 + r = 0 at h0
    change 1 - r = 0 at h1
    have htwo : (2 : ℂ) = 0 := by linear_combination h0 + h1
    norm_num at htwo
  have hflux := OQ7.layerDirectedFlux_strict hk (layer := dielectricSlab p q d) hp hq hd (1 + r) (1 - r) hi
  have hb := dielectricSlab_field_boundary k hk p q d hp hq.le hd.le
  change OQ7.directedFlux
    (OQ7.layerElectricField k (dielectricSlab p q d) (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) d)
    (OQ7.layerMagneticField k (dielectricSlab p q d) (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) d) <
      OQ7.directedFlux (1 + dielectricSlabReflection k p q d) (1 - dielectricSlabReflection k p q d) at hflux
  rw [hb.1, hb.2, directedFlux_incident_reflected, directedFlux_transmitted] at hflux
  change Complex.normSq t < 1 - Complex.normSq r at hflux
  change 0 < 1 - Complex.normSq r - Complex.normSq t
  linarith

theorem dielectricSlab_absorptance_strict_bounds (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 < q) (hd : 0 < d) :
    0 < OQ7.absorptanceLeft (dielectricSlabReflection k p q d) (dielectricSlabTransmission k p q d) ∧
      OQ7.absorptanceLeft (dielectricSlabReflection k p q d) (dielectricSlabTransmission k p q d) < 1 :=
  ⟨dielectricSlab_absorptance_pos k hk p q d hp hq hd,
    dielectricSlab_absorptance_lt_one k hk p q d hp hq.le hd.le⟩

end OQ7Prescribed
