import OQ7.SharpDeficit
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace OQ7
open Filter Asymptotics
open scoped Topology

theorem reciprocal_square_norm_rate {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ m : ℕ in atTop, ‖f m‖ ≤ C / (m : ℝ) ^ 2) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * ‖f m‖ ^ 2) atTop (𝓝 0) := by
  have ht := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul (C ^ 2)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [] with m
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · filter_upwards [hf, eventually_gt_atTop (0 : ℕ)] with m hf hm
    have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
    have hb := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (div_nonneg hC (sq_nonneg _))).mpr hf)
      (sq_nonneg (m : ℝ))
    convert hb using 1
    field_simp

theorem reciprocal_square_scalar_rate (f : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ m : ℕ in atTop, |f m| ≤ C / (m : ℝ) ^ 2) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (f m) ^ 2) atTop (𝓝 0) := by
  simpa only [Real.norm_eq_abs, sq_abs] using reciprocal_square_norm_rate f hC hf

theorem reciprocal_square_bound_of_isBigO {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → E} (hf : f =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ‖f m‖ ≤ C / (m : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨|C|, abs_nonneg C, ?_⟩
  filter_upwards [hC] with m hm
  calc
    ‖f m‖ ≤ C * ‖1 / (m : ℝ) ^ 2‖ := hm
    _ ≤ |C| * ‖1 / (m : ℝ) ^ 2‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ = |C| / (m : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      ring

theorem reciprocal_square_norm_rate_of_isBigO {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → E} (hf : f =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2)) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * ‖f m‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := reciprocal_square_bound_of_isBigO hf
  exact reciprocal_square_norm_rate f hC hb

theorem differentiable_sequence_reciprocal_square_rate
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x0 : E} {x : ℕ → E}
    (hf : DifferentiableAt ℝ f x0) (hx : Tendsto x atTop (𝓝 x0))
    (hr : (fun m => x m - x0) =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2)) :
    (fun m => f (x m) - f x0) =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
  exact (hf.isBigO_sub.comp_tendsto hx).trans hr

theorem sharp_deficit_limit_of_quadratic_rates {T a C : ℝ}
    (h : ScalarEnvelope.ActiveTarget T a) (x c : ℕ → ℝ)
    (hx : ∀ᶠ m : ℕ in atTop, 0 ≤ x m ∧ x m ≤ ScalarEnvelope.x0 T a)
    (hc : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * c m) atTop (𝓝 C))
    (hphase : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      (ScalarEnvelope.F T a (x m) - T * c m)) atTop (𝓝 0))
    (hrate : (fun m => ScalarEnvelope.x0 T a - x m) =O[atTop]
      (fun m : ℕ => 1 / (m : ℝ) ^ 2)) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (ScalarEnvelope.D0 T a - 2 * x m))
      atTop (𝓝 (ScalarEnvelope.alpha T a * C)) := by
  have hsq := reciprocal_square_norm_rate_of_isBigO hrate
  simp only [Real.norm_eq_abs, sq_abs] at hsq
  have hyrate : (fun m => Real.sqrt ((ScalarEnvelope.b T a) ^ 2 - (x m) ^ 2) -
      ScalarEnvelope.y0 T a) =O[atTop] (fun m => ScalarEnvelope.x0 T a - x m) := by
    apply IsBigO.of_bound (ScalarEnvelope.x0 T a / ScalarEnvelope.y0 T a)
    filter_upwards [hx] with m hm
    have hb := ScalarEnvelope.sqrt_displacement_bound h hm.1 hm.2
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1,
      abs_of_nonneg (sub_nonneg.mpr hm.2)] using hb.2
  have hysq := reciprocal_square_norm_rate_of_isBigO (hyrate.trans hrate)
  simp only [Real.norm_eq_abs, sq_abs] at hysq
  have hp := ScalarEnvelope.active_target_properties h
  have hrem := ((hphase.const_mul (ScalarEnvelope.y0 T a)).add
    ((hsq.const_mul (ScalarEnvelope.y0 T a)).add
      ((hsq.add hysq).const_mul T))).div_const (ScalarEnvelope.s a * ScalarEnvelope.x0 T a)
  have ht := (hc.const_mul (ScalarEnvelope.alpha T a)).add hrem
  simp only [mul_zero, add_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [hx] with m hm
  have hid := ScalarEnvelope.tangent_remainder h hm.1 hm.2
  unfold ScalarEnvelope.alpha ScalarEnvelope.D0
  field_simp [hp.1.ne', hp.2.2.2.1.ne']
  nlinarith [congrArg (fun z : ℝ => (m : ℝ) ^ 2 * z) hid]

#print axioms reciprocal_square_norm_rate
#print axioms reciprocal_square_scalar_rate
#print axioms reciprocal_square_bound_of_isBigO
#print axioms reciprocal_square_norm_rate_of_isBigO
#print axioms differentiable_sequence_reciprocal_square_rate
#print axioms sharp_deficit_limit_of_quadratic_rates
end OQ7
