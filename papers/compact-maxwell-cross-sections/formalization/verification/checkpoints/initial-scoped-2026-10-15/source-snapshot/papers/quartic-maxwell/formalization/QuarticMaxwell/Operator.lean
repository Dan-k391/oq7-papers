import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Shared-inverse quartic estimate

This is a dimension-independent operator theorem. It derives the quartic chain
from a single inverse, imaginary coercivity, a radiation-map estimate and a
source-pair estimate. These analytic hypotheses must still be proved for the
actual measurable-support Maxwell operator to obtain manuscript Theorem 1.1.
They are not axioms, and this theorem is not advertised as a Maxwell theorem.
-/

noncomputable section
namespace QuarticMaxwell

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Difference of the complete radiation quadratic forms. -/
theorem radiation_quadratic_difference (F : H →L[ℂ] E) (p q : H) :
    |‖F p‖ ^ 2 - ‖F q‖ ^ 2| ≤
      ‖F‖ ^ 2 * ‖p - q‖ * (‖p‖ + ‖q‖) := by
  have hd : |‖F p‖ - ‖F q‖| ≤ ‖F‖ * ‖p - q‖ := by
    apply (abs_norm_sub_norm_le (F p) (F q)).trans
    rw [← map_sub]
    exact F.le_opNorm _
  have hs : ‖F p‖ + ‖F q‖ ≤ ‖F‖ * (‖p‖ + ‖q‖) := by
    have hp := F.le_opNorm p
    have hq := F.le_opNorm q
    nlinarith
  calc
    _ = |‖F p‖ - ‖F q‖| * (‖F p‖ + ‖F q‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← abs_mul]
      congr 1
      ring
    _ ≤ (‖F‖ * ‖p - q‖) * (‖F‖ * (‖p‖ + ‖q‖)) :=
      mul_le_mul hd hs (by positivity) (by positivity)
    _ = _ := by ring

/-- The current difference comes from the same bounded inverse. -/
theorem common_inverse_difference (A : H ≃L[ℂ] H) (ρ : ℝ)
    (hρ : ‖A.symm.toContinuousLinearMap‖ ≤ ρ) (f g : H) :
    ‖A.symm f - A.symm g‖ ≤ ρ * ‖f - g‖ := by
  rw [← map_sub]
  exact (A.symm.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))

/-- Negative imaginary coercivity gives the passivity norm bound. -/
theorem inverse_current_power (A : H ≃L[ℂ] H) {k ρ X : ℝ} (hk : 0 < k)
    (hρ : 0 < ρ) (hc : ∀ p, ‖p‖ ^ 2 / ρ ≤ -(inner ℂ p (A p)).im)
    (f : H) (hX : X = -k * (inner ℂ (A.symm f) f).im) :
    ‖A.symm f‖ ^ 2 ≤ ρ * X / k := by
  have h := hc (A.symm f)
  rw [A.apply_symm_apply] at h
  have hxk : X / k = -(inner ℂ (A.symm f) f).im := by rw [hX]; field_simp
  rw [← hxk] at h
  exact (div_le_iff₀ hρ).mp h |>.trans_eq (by ring)

/-- The exact coefficient `2/(3π)` follows from operator, source and power
estimates. No square-root auxiliary variables are assumed. In Maxwell, `F` is
the full vector far-field map and `X` is common extinction. -/
theorem shared_inverse_quartic_bound (A : H ≃L[ℂ] H) (F : H →L[ℂ] E)
    {k R V ρ L X : ℝ} (hk : 0 < k) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hX : 0 < X)
    (hA : ‖A.toContinuousLinearMap‖ ≤ L)
    (hAi : ‖A.symm.toContinuousLinearMap‖ ≤ ρ)
    (hc : ∀ p, ‖p‖ ^ 2 / ρ ≤ -(inner ℂ p (A p)).im)
    (hF : ‖F‖ ^ 2 ≤ 8 * Real.pi * V / 3)
    (f g : H) (hfg : ‖f - g‖ ≤ 2 * k * R * ‖f‖)
    (hXp : X = -k * (inner ℂ (A.symm f) f).im)
    (hXm : X = -k * (inner ℂ (A.symm g) g).im) :
    |k ^ 4 / (16 * Real.pi ^ 2) *
      (‖F (A.symm f)‖ ^ 2 - ‖F (A.symm g)‖ ^ 2)| / X ≤
      2 / (3 * Real.pi) * ρ ^ 2 * L * k ^ 4 * R * V := by
  let p := A.symm f
  let q := A.symm g
  have hp : ‖p‖ ^ 2 ≤ ρ * X / k := inverse_current_power A hk hρ hc f hXp
  have hq : ‖q‖ ^ 2 ≤ ρ * X / k := inverse_current_power A hk hρ hc g hXm
  have hcross : ‖p‖ * (‖p‖ + ‖q‖) ≤ 2 * (ρ * X / k) := by
    nlinarith [sq_nonneg (‖p‖ - ‖q‖)]
  have hf : ‖f‖ ≤ L * ‖p‖ := by
    have he : A p = f := A.apply_symm_apply f
    rw [← he]
    exact (A.toContinuousLinearMap.le_opNorm p).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg p))
  have hd : ‖p - q‖ ≤ 2 * ρ * k * R * L * ‖p‖ := by
    apply (common_inverse_difference A ρ hAi f g).trans
    calc
      ρ * ‖f - g‖ ≤ ρ * (2 * k * R * ‖f‖) :=
        mul_le_mul_of_nonneg_left hfg hρ.le
      _ ≤ ρ * (2 * k * R * (L * ‖p‖)) := by gcongr
      _ = _ := by ring
  have hpq : ‖p - q‖ * (‖p‖ + ‖q‖) ≤
      (2 * ρ * k * R * L) * (2 * (ρ * X / k)) := by
    calc
      _ ≤ (2 * ρ * k * R * L * ‖p‖) * (‖p‖ + ‖q‖) := by gcongr
      _ = (2 * ρ * k * R * L) * (‖p‖ * (‖p‖ + ‖q‖)) := by ring
      _ ≤ _ := by gcongr
  have hr : |‖F p‖ ^ 2 - ‖F q‖ ^ 2| ≤
      (8 * Real.pi * V / 3) *
        ((2 * ρ * k * R * L) * (2 * (ρ * X / k))) := by
    apply (radiation_quadratic_difference F p q).trans
    calc
      ‖F‖ ^ 2 * ‖p - q‖ * (‖p‖ + ‖q‖) =
          ‖F‖ ^ 2 * (‖p - q‖ * (‖p‖ + ‖q‖)) := by ring
      _ ≤ _ := mul_le_mul hF hpq (by positivity) (by positivity)
  have hs : |k ^ 4 / (16 * Real.pi ^ 2) *
      (‖F p‖ ^ 2 - ‖F q‖ ^ 2)| ≤
      (2 / (3 * Real.pi) * ρ ^ 2 * L * k ^ 4 * R * V) * X := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ k ^ 4 / (16 * Real.pi ^ 2))]
    apply (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq
    field_simp
    ring
  exact (div_le_iff₀ hX).mpr hs

/-- Positive absorption implies the additional universal bound `Γ ≤ 1`. -/
theorem normalized_absorption_difference_le_one {A₁ A₂ X : ℝ}
    (hX : 0 < X) (h₁ : 0 ≤ A₁) (h₂ : 0 ≤ A₂)
    (h₁X : A₁ ≤ X) (h₂X : A₂ ≤ X) : |A₁ - A₂| / X ≤ 1 := by
  rw [div_le_iff₀ hX, one_mul, abs_le]
  constructor <;> linarith

end QuarticMaxwell
