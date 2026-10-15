import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Dimension-independent power-normalized channel passivity. These results
prove the parabola for actual bounded operators and include its equality case.
The reciprocity identification of the second input is a separate theorem. -/

noncomputable section
namespace GeneralizedResearch
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def channelAbsorption (S : E →L[ℂ] E) (u : E) : ℝ := 1 - ‖S u‖ ^ 2
def channelExtinction (S S₀ : E →L[ℂ] E) (u : E) : ℝ :=
  2 * (1 - (inner ℂ (S₀ u) (S u)).re)
def channelScattering (S S₀ : E →L[ℂ] E) (u : E) : ℝ := ‖(S - S₀) u‖ ^ 2

theorem channel_power_identity (S S₀ : E →L[ℂ] E) (u : E)
    (h₀ : ‖S₀ u‖ = 1) :
    channelExtinction S S₀ u = channelAbsorption S u + channelScattering S S₀ u := by
  have h := norm_sub_sq (𝕜 := ℂ) (S u) (S₀ u)
  have hz : (inner ℂ (S u) (S₀ u)).re = (inner ℂ (S₀ u) (S u)).re := by
    exact inner_re_symm (𝕜 := ℂ) _ _
  unfold channelExtinction channelAbsorption channelScattering
  simp only [sub_apply]
  change 2 * (1 - (inner ℂ (S₀ u) (S u)).re) =
    1 - ‖S u‖ ^ 2 + ‖S u - S₀ u‖ ^ 2
  rw [h, h₀]
  change 2 * (1 - (inner ℂ (S₀ u) (S u)).re) =
    1 - ‖S u‖ ^ 2 + (‖S u‖ ^ 2 - 2 * (inner ℂ (S u) (S₀ u)).re + 1 ^ 2)
  rw [hz]
  ring

theorem channel_passivity_parabola (S S₀ : E →L[ℂ] E) (u : E)
    (h₀ : ‖S₀ u‖ = 1) (hS : ‖S u‖ ≤ 1) :
    0 ≤ channelExtinction S S₀ u ∧ channelExtinction S S₀ u ≤ 4 ∧
    0 ≤ channelAbsorption S u ∧
    channelAbsorption S u ≤ channelExtinction S S₀ u - (channelExtinction S S₀ u) ^ 2 / 4 := by
  have hz := norm_inner_le_norm (𝕜 := ℂ) (S₀ u) (S u)
  rw [h₀, one_mul] at hz
  have hr := (Complex.abs_re_le_norm (inner ℂ (S₀ u) (S u))).trans hz
  have hr' := abs_le.mp (hr.trans hS)
  have hn := norm_nonneg (S u)
  have hre2 : ((inner ℂ (S₀ u) (S u)).re) ^ 2 ≤ ‖S u‖ ^ 2 := by
    exact sq_le_sq.mpr (by simpa using hr)
  unfold channelExtinction channelAbsorption
  constructor
  · linarith [hr'.2]
  constructor
  · linarith [hr'.1]
  constructor
  · nlinarith
  · nlinarith

theorem channel_parabola_equality_iff (S S₀ : E →L[ℂ] E) (u : E)
    (h₀ : ‖S₀ u‖ = 1) :
    channelAbsorption S u =
        channelExtinction S S₀ u - (channelExtinction S S₀ u) ^ 2 / 4 ↔
    S u = ((1 - channelExtinction S S₀ u / 2 : ℝ) : ℂ) • S₀ u := by
  let r : ℝ := (inner ℂ (S₀ u) (S u)).re
  have hr : 1 - channelExtinction S S₀ u / 2 = r := by
    simp [channelExtinction, r]
  rw [hr]
  have hcross : (inner ℂ (S u) (S₀ u)).re = r := by
    exact inner_re_symm (𝕜 := ℂ) _ _
  have hnorm : ‖S u - (r : ℂ) • S₀ u‖ ^ 2 = ‖S u‖ ^ 2 - r ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    change ‖S u‖ ^ 2 - 2 * (inner ℂ (S u) ((r : ℂ) • S₀ u)).re +
      ‖(r : ℂ) • S₀ u‖ ^ 2 = ‖S u‖ ^ 2 - r ^ 2
    rw [inner_smul_right (𝕜 := ℂ) (S u) (S₀ u) (r : ℂ)]
    simp [norm_smul, h₀, hcross, Real.norm_eq_abs]
    ring
  constructor
  · intro h
    have hsq : ‖S u‖ ^ 2 = r ^ 2 := by
      unfold channelAbsorption channelExtinction at h
      dsimp [r]
      nlinarith
    have hzero : S u - (r : ℂ) • S₀ u = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (S u - (r : ℂ) • S₀ u)]
    exact sub_eq_zero.mp hzero
  · intro h
    have hsq : ‖S u‖ ^ 2 = r ^ 2 := by
      rw [h, norm_smul, h₀]
      simp
    unfold channelAbsorption channelExtinction
    change 1 - ‖S u‖ ^ 2 = 2 * (1 - r) - (2 * (1 - r)) ^ 2 / 4
    rw [hsq]
    ring

theorem equal_extinction_absorption_difference (S S₀ : E →L[ℂ] E) (u v : E)
    (hu₀ : ‖S₀ u‖ = 1) (hv₀ : ‖S₀ v‖ = 1)
    (huS : ‖S u‖ ≤ 1) (hvS : ‖S v‖ ≤ 1)
    (hX : channelExtinction S S₀ v = channelExtinction S S₀ u) :
    |channelAbsorption S u - channelAbsorption S v| ≤
      channelExtinction S S₀ u - (channelExtinction S S₀ u) ^ 2 / 4 := by
  have hu := channel_passivity_parabola S S₀ u hu₀ huS
  have hv := channel_passivity_parabola S S₀ v hv₀ hvS
  rw [hX] at hv
  apply abs_le.mpr
  constructor <;> linarith [hu.2.2.1, hu.2.2.2, hv.2.2.1, hv.2.2.2]

end GeneralizedResearch
