import OQ7.ExpRemainder
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FunProp

noncomputable section
namespace OQ7
open Finset Filter Asymptotics
open scoped Topology

def algebraExpTaylor {A : Type*} [Ring A] [Algebra ℝ A]
    (X : A) (n : ℕ) (t : ℝ) : A :=
  ∑ j ∈ range n, (t ^ j / (j.factorial : ℝ)) • X ^ j

theorem algebraExpTaylor_continuous {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : A) (n : ℕ) : Continuous (algebraExpTaylor X n) := by
  unfold algebraExpTaylor
  fun_prop

theorem algebraExp_scaled_isBigO_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [NormOneClass A] [CompleteSpace A] (X : A) :
    (fun t : ℝ => NormedSpace.exp (t • X)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound (Real.exp ‖X‖)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ))] with t ht
  have ht1 : |t| ≤ 1 := by
    have hb : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    exact hb.le
  have hb := norm_algebra_exp_le (t • X)
  have hex : Real.exp ‖t • X‖ ≤ Real.exp ‖X‖ := by
    apply Real.exp_le_exp.mpr
    simpa only [norm_smul, Real.norm_eq_abs, one_mul] using
      mul_le_mul_of_nonneg_right ht1 (norm_nonneg X)
  simpa only [norm_one, mul_one] using hb.trans hex

theorem algebraExpTaylor_isBigO_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : A) (n : ℕ) :
    algebraExpTaylor X n =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
  isBigO_const_of_tendsto ((algebraExpTaylor_continuous X n).tendsto 0) one_ne_zero

/-- Multiplying the three genuine exponential remainders preserves their full order. -/
theorem triple_expTaylor_product_remainder_isBigO {A : Type*} [NormedRing A]
    [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A] (X Y Z : A) (n : ℕ) :
    (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) *
      NormedSpace.exp (t • Z) - algebraExpTaylor X n t * algebraExpTaylor Y n t *
        algebraExpTaylor Z n t) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have hX := algebra_exp_scaled_remainder_isBigO X n
  have hY := algebra_exp_scaled_remainder_isBigO Y n
  have hZ := algebra_exp_scaled_remainder_isBigO Z n
  have hEY := algebraExp_scaled_isBigO_one Y
  have hEZ := algebraExp_scaled_isBigO_one Z
  have hPX := algebraExpTaylor_isBigO_one X n
  have hPY := algebraExpTaylor_isBigO_one Y n
  have h₁ : (fun t : ℝ => (NormedSpace.exp (t • X) - algebraExpTaylor X n t) *
      NormedSpace.exp (t • Y) * NormedSpace.exp (t • Z)) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
    simpa only [algebraExpTaylor, mul_one] using (hX.mul hEY).mul hEZ
  have h₂ : (fun t : ℝ => algebraExpTaylor X n t *
      (NormedSpace.exp (t • Y) - algebraExpTaylor Y n t) *
      NormedSpace.exp (t • Z)) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
    simpa only [algebraExpTaylor, one_mul, mul_one] using (hPX.mul hY).mul hEZ
  have h₃ : (fun t : ℝ => algebraExpTaylor X n t * algebraExpTaylor Y n t *
      (NormedSpace.exp (t • Z) - algebraExpTaylor Z n t)) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
    simpa only [algebraExpTaylor, one_mul, mul_one] using (hPX.mul hPY).mul hZ
  exact ((h₁.add h₂).add h₃).congr_left (fun t => by noncomm_ring)

theorem scalarPower_smul_continuous_isBigO {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {tail : ℝ → A} (htail : ContinuousAt tail 0) (n : ℕ) :
    (fun t : ℝ => t ^ n • tail t) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have hb : tail =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto htail.tendsto one_ne_zero
  simpa only [smul_eq_mul, mul_one] using (isBigO_refl (fun t : ℝ => t ^ n) (𝓝 0)).smul hb

/-- The algebraic low-order coefficients are a proved input; the analytic bound is generic. -/
theorem triple_exp_remainder_of_tail_identity {A : Type*} [NormedRing A]
    [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X Y Z : A) (n : ℕ) (polynomial tail : ℝ → A)
    (htail : ContinuousAt tail 0)
    (hidentity : ∀ t, algebraExpTaylor X n t * algebraExpTaylor Y n t *
      algebraExpTaylor Z n t = polynomial t + t ^ n • tail t) :
    (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) *
      NormedSpace.exp (t • Z) - polynomial t) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have h₁ := triple_expTaylor_product_remainder_isBigO X Y Z n
  have h₂ := scalarPower_smul_continuous_isBigO htail n
  exact (h₁.add h₂).congr_left (fun t => by rw [hidentity]; abel)

theorem scalarPower_isBigO_of_le {n d : ℕ} (hnd : n ≤ d) :
    (fun t : ℝ => t ^ d) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ))] with t ht
  have ht1 : |t| ≤ 1 := by
    have hb : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    exact hb.le
  simpa only [norm_pow, Real.norm_eq_abs, one_mul] using
    pow_le_pow_of_le_one (abs_nonneg t) ht1 hnd

/-- A fifth-order cell expansion supplies the cubic perturbation used in repetition. -/
theorem linear_remainder_isBigO_cubic_of_quartic {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] (D : ℝ → A) (B C E : A)
    (h₅ : (fun t : ℝ => D t - (1 + t • B + t ^ 3 • C + t ^ 4 • E))
      =O[𝓝 0] (fun t : ℝ => t ^ 5)) :
    (fun t : ℝ => D t - (1 + t • B)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have h₁ := h₅.trans (scalarPower_isBigO_of_le (by norm_num : (3 : ℕ) ≤ 5))
  have h₂ : (fun t : ℝ => t ^ 3 • C) =O[𝓝 0] (fun t : ℝ => t ^ 3) :=
    scalarPower_smul_continuous_isBigO continuousAt_const 3
  have h₃ : (fun t : ℝ => t ^ 4 • E) =O[𝓝 0] (fun t : ℝ => t ^ 3) :=
    (scalarPower_smul_continuous_isBigO continuousAt_const 4).trans
      (scalarPower_isBigO_of_le (by norm_num : (3 : ℕ) ≤ 4))
  exact ((h₁.add h₂).add h₃).congr_left (fun t => by abel)

/-- Evaluating a local power bound at the actual reciprocal cell scale gives a uniform constant. -/
theorem isBigO_reciprocal_scale_norm_bound {A : Type*} [NormedAddCommGroup A]
    {F : ℝ → A} {n : ℕ} (h : F =O[𝓝 0] (fun t : ℝ => t ^ n)) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ‖F (a / (m : ℝ))‖ ≤ C / (m : ℝ) ^ n := by
  have ht : Tendsto (fun m : ℕ => a / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨c, hc, hcb⟩ := (h.comp_tendsto ht).exists_pos
  refine ⟨c * |a| ^ n + 1, by positivity, ?_⟩
  filter_upwards [hcb.bound] with m hm
  have heq : |(a / (m : ℝ)) ^ n| = |a| ^ n / (m : ℝ) ^ n := by
    simp only [abs_pow, abs_div, abs_of_nonneg (Nat.cast_nonneg m : 0 ≤ (m : ℝ)), div_pow]
  dsimp [Function.comp_def] at hm
  rw [heq, ← mul_div_assoc] at hm
  exact hm.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg (Nat.cast_nonneg m) n))

#print axioms algebraExpTaylor_continuous
#print axioms algebraExp_scaled_isBigO_one
#print axioms algebraExpTaylor_isBigO_one
#print axioms triple_expTaylor_product_remainder_isBigO
#print axioms scalarPower_smul_continuous_isBigO
#print axioms triple_exp_remainder_of_tail_identity
#print axioms scalarPower_isBigO_of_le
#print axioms linear_remainder_isBigO_cubic_of_quartic
#print axioms isBigO_reciprocal_scale_norm_bound
end OQ7
