import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

noncomputable section
namespace QuarticMaxwell
theorem orthogonal_split_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (P : E →L[ℂ] E)
    (horth : ∀ v, inner ℂ (P v) (v - P v) = 0)
    (a b : ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) :
    ‖a • P + b • (ContinuousLinearMap.id ℂ E - P)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hdec : P v + (v - P v) = v := by abel
  have hv := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (P v) (v - P v) (horth v)
  rw [hdec] at hv
  have hs : inner ℂ (a • P v) (b • (v - P v)) = 0 := by
    simp only [inner_smul_left, inner_smul_right, horth, mul_zero]
  have hw := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (a • P v) (b • (v - P v)) hs
  have ha2 : ‖a‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg a]
  have hb2 : ‖b‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg b]
  have hpa := mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖P v‖)
  have hpb := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖v - P v‖)
  simp only [norm_smul] at hw
  have hsq : ‖a • P v + b • (v - P v)‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
    nlinarith [hw, hv]
  have hn : 0 ≤ C * ‖v‖ := mul_nonneg hC (norm_nonneg v)
  have hout : ‖a • P v + b • (v - P v)‖ ≤ C * ‖v‖ := by
    nlinarith [norm_nonneg (a • P v + b • (v - P v))]
  simpa only [add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply] using hout

end QuarticMaxwell
