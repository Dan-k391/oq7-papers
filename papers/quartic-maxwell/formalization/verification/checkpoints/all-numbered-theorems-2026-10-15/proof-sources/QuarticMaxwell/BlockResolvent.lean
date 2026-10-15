import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! Algebraic interaction bounds for bounded operators. The physical
two-support block identity and the kernel bounds must be proved separately;
none of the desired interaction estimates is an assumed operator field. -/
noncomputable section
namespace QuarticMaxwell.BlockResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem norm_comp_three_le (A C T : H →L[ℂ] H) :
    ‖A ∘L C ∘L T‖ ≤ ‖A‖ * ‖C‖ * ‖T‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le (A ∘L C) T).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le A C) (norm_nonneg T))

theorem identity_of_apply (A C T : H →L[ℂ] H)
    (h : ∀ f, T f = A f + A (C (T f))) : T = A + A ∘L C ∘L T := by
  apply ContinuousLinearMap.ext
  exact h

theorem difference_identity (A C T : H →L[ℂ] H)
    (h : T = A + A ∘L C ∘L T) : T - A = A ∘L C ∘L T := by
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm A _))

theorem inverse_norm_le (A C T : H →L[ℂ] H) {ρ c : ℝ}
    (hρ : 0 ≤ ρ) (_hc : 0 ≤ c) (hA : ‖A‖ ≤ ρ) (hC : ‖C‖ ≤ c)
    (hsmall : ρ * c < 1) (h : T = A + A ∘L C ∘L T) :
    ‖T‖ ≤ ρ / (1 - ρ * c) := by
  have hbound : ‖T‖ ≤ ρ + ρ * c * ‖T‖ := by
    calc
      ‖T‖ = ‖A + A ∘L C ∘L T‖ := congrArg norm h
      _ ≤ ‖A‖ + ‖A ∘L C ∘L T‖ := norm_add_le _ _
      _ ≤ ‖A‖ + ‖A‖ * ‖C‖ * ‖T‖ := add_le_add_right (norm_comp_three_le A C T) _
      _ ≤ _ := by gcongr
  have hden : 0 < 1 - ρ * c := by linarith
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hbound]

theorem inverse_difference_norm_le (A C T : H →L[ℂ] H) {ρ c : ℝ}
    (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hA : ‖A‖ ≤ ρ) (hC : ‖C‖ ≤ c)
    (hsmall : ρ * c < 1) (h : T = A + A ∘L C ∘L T) :
    ‖T - A‖ ≤ ρ ^ 2 * c / (1 - ρ * c) := by
  have hT := inverse_norm_le A C T hρ hc hA hC hsmall h
  have hden : 0 < 1 - ρ * c := by linarith
  rw [difference_identity A C T h]
  calc
    _ ≤ ‖A‖ * ‖C‖ * ‖T‖ := norm_comp_three_le A C T
    _ ≤ ρ * c * (ρ / (1 - ρ * c)) := by gcongr
    _ = _ := by ring

theorem inverse_difference_norm_le_of_common_bound (A C T : H →L[ℂ] H) {μ c : ℝ}
    (hμ : 0 ≤ μ) (hc : 0 ≤ c) (hA : ‖A‖ ≤ μ) (hC : ‖C‖ ≤ c) (hT : ‖T‖ ≤ μ)
    (h : T = A + A ∘L C ∘L T) : ‖T - A‖ ≤ μ ^ 2 * c := by
  rw [difference_identity A C T h]
  calc
    _ ≤ ‖A‖ * ‖C‖ * ‖T‖ := norm_comp_three_le A C T
    _ ≤ μ * c * μ := by gcongr
    _ = _ := by ring

theorem first_order_remainder_identity (A C T : H →L[ℂ] H)
    (h : T = A + A ∘L C ∘L T) :
    T - A - A ∘L C ∘L A = A ∘L C ∘L (T - A) := by
  have hd := difference_identity A C T h
  calc
    _ = (A ∘L C ∘L T) - A ∘L C ∘L A := congrArg (fun S => S - A ∘L C ∘L A) hd
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro f
      simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]

theorem second_order_remainder_norm_le (A C T : H →L[ℂ] H) {μ c : ℝ}
    (hμ : 0 ≤ μ) (hc : 0 ≤ c) (hA : ‖A‖ ≤ μ) (hC : ‖C‖ ≤ c) (hT : ‖T‖ ≤ μ)
    (h : T = A + A ∘L C ∘L T) :
    ‖T - A - A ∘L C ∘L A‖ ≤ μ ^ 3 * c ^ 2 := by
  have hd := inverse_difference_norm_le_of_common_bound A C T hμ hc hA hC hT h
  rw [first_order_remainder_identity A C T h]
  calc
    _ ≤ ‖A‖ * ‖C‖ * ‖T - A‖ := norm_comp_three_le A C (T - A)
    _ ≤ μ * c * (μ ^ 2 * c) := by gcongr
    _ = _ := by ring

theorem second_order_remainder_apply_norm_le (A C T : H →L[ℂ] H) {μ c : ℝ}
    (hμ : 0 ≤ μ) (hc : 0 ≤ c) (hA : ‖A‖ ≤ μ) (hC : ‖C‖ ≤ c) (hT : ‖T‖ ≤ μ)
    (h : T = A + A ∘L C ∘L T) (f : H) :
    ‖T f - A f - A (C (A f))‖ ≤ (μ ^ 3 * c ^ 2) * ‖f‖ := by
  have hn := ((T - A - A ∘L C ∘L A).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (second_order_remainder_norm_le A C T hμ hc hA hC hT h) (norm_nonneg f))
  simpa only [sub_apply, ContinuousLinearMap.comp_apply] using hn

end QuarticMaxwell.BlockResolvent
