import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
namespace OQ7
open Finset

theorem factorial_product_le (n j : ℕ) : n.factorial * j.factorial ≤ (j + n).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.factorial_succ, Nat.succ_add, Nat.factorial_succ]
    nlinarith

theorem real_exp_tail_bound (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (∑' j : ℕ, r ^ (j + n) / ((j + n).factorial : ℝ)) ≤
      r ^ n / (n.factorial : ℝ) * Real.exp r := by
  have hf := (Real.summable_pow_div_factorial r).comp_injective
    (fun _ _ h => Nat.add_right_cancel h : Function.Injective (fun j : ℕ => j + n))
  have hg := (Real.summable_pow_div_factorial r).mul_left (r ^ n / (n.factorial : ℝ))
  have hb : ∀ j : ℕ, r ^ (j + n) / ((j + n).factorial : ℝ) ≤
      r ^ n / (n.factorial : ℝ) * (r ^ j / (j.factorial : ℝ)) := by
    intro j
    rw [div_mul_div_comm, ← pow_add, add_comm n j]
    exact div_le_div_of_nonneg_left (pow_nonneg hr _)
      (by positivity) (by exact_mod_cast factorial_product_le n j)
  have hs := hf.tsum_le_tsum hb hg
  rw [tsum_mul_left] at hs
  have he : (∑' j : ℕ, r ^ j / (j.factorial : ℝ)) = Real.exp r := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rwa [he] at hs

theorem norm_algebra_exp_remainder {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (x : A) (n : ℕ) :
    ‖NormedSpace.exp x - ∑ j ∈ range n, (j.factorial : ℝ)⁻¹ • x ^ j‖ ≤
      ‖x‖ ^ n / (n.factorial : ℝ) * Real.exp ‖x‖ := by
  let f : ℕ → A := fun j => (j.factorial : ℝ)⁻¹ • x ^ j
  have hf : Summable f := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
  have hfn : Summable (fun j => ‖f j‖) := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have htail : NormedSpace.exp x - ∑ j ∈ range n, f j = ∑' j : ℕ, f (j + n) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    change (∑' j : ℕ, f j) - ∑ j ∈ range n, f j = ∑' j : ℕ, f (j + n)
    rw [← hf.sum_add_tsum_nat_add n]
    exact add_sub_cancel_left _ _
  rw [htail]
  have hi : Function.Injective (fun j : ℕ => j + n) := fun _ _ h => Nat.add_right_cancel h
  apply (norm_tsum_le_tsum_norm (hfn.comp_injective hi)).trans
  apply le_trans _ (real_exp_tail_bound ‖x‖ (norm_nonneg x) n)
  apply (hfn.comp_injective hi).tsum_le_tsum _
    ((Real.summable_pow_div_factorial ‖x‖).comp_injective hi)
  intro j
  dsimp [f]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (norm_pow_le x (j + n))
      (inv_nonneg.mpr (Nat.cast_nonneg (j + n).factorial))

#print axioms factorial_product_le
#print axioms real_exp_tail_bound

theorem norm_algebra_exp_le {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa only [range_zero, sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul] using norm_algebra_exp_remainder x 0

theorem norm_algebra_exp_scaled_remainder {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (X : A) (t : ℝ) (n : ℕ) :
    ‖NormedSpace.exp (t • X) - ∑ j ∈ range n, (t ^ j / (j.factorial : ℝ)) • X ^ j‖ ≤
      |t| ^ n * ‖X‖ ^ n * Real.exp (|t| * ‖X‖) / (n.factorial : ℝ) := by
  have hb := norm_algebra_exp_remainder (t • X) n
  simp only [smul_pow, smul_smul, norm_smul, Real.norm_eq_abs, mul_pow] at hb
  rw [div_mul_eq_mul_div] at hb
  simpa only [div_eq_mul_inv, mul_comm] using hb

#print axioms norm_algebra_exp_le

/-- The fixed-generator Taylor remainder required by the checkpoint is fifth order. -/
theorem algebra_exp_scaled_remainder_isBigO {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (X : A) (n : ℕ) :
    Asymptotics.IsBigO (nhds (0 : ℝ))
      (fun t : ℝ => NormedSpace.exp (t • X) -
        ∑ j ∈ range n, (t ^ j / (j.factorial : ℝ)) • X ^ j)
      (fun t : ℝ => t ^ n) := by
  apply Asymptotics.IsBigO.of_bound (‖X‖ ^ n * Real.exp ‖X‖ / (n.factorial : ℝ))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ))] with t ht
  have ht1 : |t| ≤ 1 := by
    have hb : |t| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    exact hb.le
  have hex : Real.exp (|t| * ‖X‖) ≤ Real.exp ‖X‖ := by
    apply Real.exp_le_exp.mpr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (norm_nonneg X)
  apply (norm_algebra_exp_scaled_remainder X t n).trans
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hex (mul_nonneg (pow_nonneg (abs_nonneg t) n)
      (pow_nonneg (norm_nonneg X) n))) (Nat.cast_nonneg n.factorial)
  simpa only [norm_pow, Real.norm_eq_abs, mul_div_assoc, mul_left_comm, mul_comm, mul_assoc] using hb

#print axioms algebra_exp_scaled_remainder_isBigO
#print axioms norm_algebra_exp_scaled_remainder
#print axioms norm_algebra_exp_remainder
end OQ7
