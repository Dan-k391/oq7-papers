import work.PlanarLayerCurrent
import PrescribedExtinction.PlanarDrive
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem apertureOscillation_boundary_phase (k L z : ℝ) :
    apertureOscillation k (L - z) * apertureOscillation (-k) L = apertureOscillation (-k) z := by
  calc
    _ = apertureOscillation (-k) z * (apertureOscillation k L * apertureOscillation (-k) L) := by
      rw [apertureOscillation_sub]
      ring
    _ = _ := by rw [apertureOscillation_opposite_mul, mul_one]

theorem planarTwoLayer_incoming_equation (k h L z : ℝ) (hk : k ≠ 0)
    (hh : 0 ≤ h) (hL : h ≤ L) (hz : z ∈ Icc 0 L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L)
    (hE : A.electric h = W.electric h) (hH : A.magnetic h = W.magnetic h)
    (l r : ℂ) (hleft : A.magnetic 0 + A.electric 0 = 2 * l)
    (hright : W.magnetic L - W.electric L = -2 * r * apertureOscillation (-k) L) :
    (if z ≤ h then A.electric z else W.electric z) =
      l * apertureOscillation k z + r * apertureOscillation (-k) z +
        (k ^ 2 : ℝ) • scalarPlanarPotential k (planarTwoLayerL2Current k h L hh hL A W : HeightL2) z := by
  have he := scalarPlanarPotential_twoLayer_representation k h L z hk hh hL hz A W hE hH
  rw [hleft, hright] at he
  have hphase : (1 / 2 : ℂ) * apertureOscillation k (L - z) *
      (-2 * r * apertureOscillation (-k) L) = -r * apertureOscillation (-k) z := by
    calc
      _ = -r * (apertureOscillation k (L - z) * apertureOscillation (-k) L) := by ring
      _ = _ := by rw [apertureOscillation_boundary_phase]
  rw [hphase] at he
  linear_combination -he

theorem planarIncidentPhase_plus (k z : ℝ) : planarIncidentPhase k .plus z = apertureOscillation k z := by
  simp [planarIncidentPhase, Direction.sign]

theorem planarIncidentPhase_minus (k z : ℝ) : planarIncidentPhase k .minus z = apertureOscillation (-k) z := by
  simp [planarIncidentPhase, Direction.sign]

theorem planarTwoLayer_plus_incident_equation (k h L z : ℝ) (hk : k ≠ 0)
    (hh : 0 ≤ h) (hL : h ≤ L) (hz : z ∈ Icc 0 L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L)
    (hE : A.electric h = W.electric h) (hH : A.magnetic h = W.magnetic h)
    (hleft : A.magnetic 0 + A.electric 0 = 2)
    (hright : W.magnetic L - W.electric L = 0) :
    (if z ≤ h then A.electric z else W.electric z) = planarIncidentPhase k .plus z +
      (k ^ 2 : ℝ) • scalarPlanarPotential k (planarTwoLayerL2Current k h L hh hL A W : HeightL2) z := by
  simpa only [one_mul, zero_mul, add_zero, planarIncidentPhase_plus] using
    planarTwoLayer_incoming_equation k h L z hk hh hL hz A W hE hH 1 0 (by simpa using hleft) (by simpa using hright)

theorem planarTwoLayer_minus_incident_equation (k h L z : ℝ) (hk : k ≠ 0)
    (hh : 0 ≤ h) (hL : h ≤ L) (hz : z ∈ Icc 0 L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L)
    (hE : A.electric h = W.electric h) (hH : A.magnetic h = W.magnetic h)
    (hleft : A.magnetic 0 + A.electric 0 = 0)
    (hright : W.magnetic L - W.electric L = -2 * apertureOscillation (-k) L) :
    (if z ≤ h then A.electric z else W.electric z) = planarIncidentPhase k .minus z +
      (k ^ 2 : ℝ) • scalarPlanarPotential k (planarTwoLayerL2Current k h L hh hL A W : HeightL2) z := by
  simpa only [one_mul, zero_mul, zero_add, planarIncidentPhase_minus] using
    planarTwoLayer_incoming_equation k h L z hk hh hL hz A W hE hH 0 1 (by simpa using hleft) (by simpa using hright)

end OQ7Prescribed
