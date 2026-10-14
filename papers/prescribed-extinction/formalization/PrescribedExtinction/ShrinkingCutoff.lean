import PrescribedExtinction.NewtonShell
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Shrinking radial cutoff errors for an actual locally bounded function.
The derivative cutoff is supported in a ball of radius twice its scale,
and its amplitude is at most a fixed constant divided by that scale. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter Metric
open scoped Topology

theorem transitionDerivative_hasCompactSupport : HasCompactSupport transitionDerivative := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro s hs
  by_cases h : s ≤ 0
  · exact transitionDerivative_zero_of_nonpos h
  · have ho : 1 ≤ s := by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hn | hn
      · exact False.elim (h hn.le)
      · exact hn.le
    exact transitionDerivative_zero_of_one_le ho

theorem transitionDerivative_global_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, ‖transitionDerivative s‖ ≤ M := by
  obtain ⟨M, hM⟩ := transitionDerivative_continuous.bounded_above_of_compact_support
    transitionDerivative_hasCompactSupport
  exact ⟨M, (norm_nonneg (transitionDerivative 0)).trans (hM 0), hM⟩

theorem exteriorCutoffPartial_norm_le (r t M : ℝ) (ht : 0 < t) (hM : 0 ≤ M)
    (hbound : ∀ s : ℝ, ‖transitionDerivative s‖ ≤ M) (i : Fin 3) (x : Position) :
    ‖exteriorCutoffPartial r t i x‖ ≤ M / t := by
  by_cases hx : x = 0
  · subst x
    simp only [exteriorCutoffPartial, PiLp.zero_apply, norm_zero, div_zero, mul_zero,
      zero_div]
    positivity
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : ‖x i / ‖x‖‖ ≤ 1 := by
    rw [norm_div, Real.norm_of_nonneg (norm_nonneg x)]
    exact (div_le_one hr).mpr (PiLp.norm_apply_le x i)
  rw [exteriorCutoffPartial, norm_div, norm_mul, Real.norm_of_nonneg ht.le]
  calc
    _ ≤ (M * 1) / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      exact mul_le_mul (hbound _) hi (norm_nonneg _) hM
    _ = M / t := by rw [mul_one]

theorem shrinkingCutoffPartial_support (ε : ℝ) (hε : 0 < ε) (i : Fin 3) :
    Function.support (exteriorCutoffPartial ε ε i) ⊆ closedBall (0 : Position) (2 * ε) := by
  intro x hx
  by_contra hn
  have ho : ε + ε ≤ ‖x‖ := by
    have hh : 2 * ε < ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hn
    linarith
  exact hx (exteriorCutoffPartial_zero_outer ε ε hε i x ho)

theorem shrinkingCutoffError_integrable (ε : ℝ) (hε : 0 < ε)
    (F : Position → ℝ) (hF : ∀ x, x ≠ 0 → ContinuousAt F x)
    (φ : ScalarTest) (i : Fin 3) :
    Integrable (fun x => exteriorCutoffPartial ε ε i x * F x * φ x) volume := by
  simpa only [mul_assoc] using exteriorCutoffPartial_mul_integrable ε ε hε hε i
    (fun x => F x * φ x) (fun x hx => (hF x hx).mul φ.continuous.continuousAt)

theorem shrinkingCutoffError_norm_le (ε R M C T : ℝ) (hε : 0 < ε)
    (hεR : 2 * ε ≤ R) (hM : 0 ≤ M) (hC : 0 ≤ C) (_hT : 0 ≤ T)
    (hMb : ∀ s : ℝ, ‖transitionDerivative s‖ ≤ M)
    (F : Position → ℝ) (hFb : ∀ x, ‖x‖ ≤ R → ‖F x‖ ≤ C)
    (φ : ScalarTest) (hφb : ∀ x, ‖φ x‖ ≤ T) (i : Fin 3) :
    ‖∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x‖ ≤
      (8 * M * C * T * volume.real (ball (0 : Position) 1)) * ε ^ 2 := by
  have hz : ∀ x ∉ closedBall (0 : Position) (2 * ε),
      exteriorCutoffPartial ε ε i x * F x * φ x = 0 := by
    intro x hx
    have hp : exteriorCutoffPartial ε ε i x = 0 := by
      by_contra hn
      exact hx (shrinkingCutoffPartial_support ε hε i hn)
    rw [hp, zero_mul, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ((M / ε) * C * T) * volume.real (closedBall (0 : Position) (2 * ε)) := by
      apply norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top
      intro x hx
      have hn : ‖x‖ ≤ R := (by simpa only [mem_closedBall, dist_zero_right] using hx :
        ‖x‖ ≤ 2 * ε).trans hεR
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (exteriorCutoffPartial_norm_le ε ε M hε hM hMb i x)
        (hFb x hn) (norm_nonneg _) (by positivity)) (hφb x) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Measure.addHaar_real_closedBall volume (0 : Position)
        (by positivity : 0 ≤ 2 * ε)]
      simp only [Position, finrank_euclideanSpace_fin]
      field_simp [hε.ne']
      ring

theorem shrinkingCutoffError_tendsto_of_bound (F : Position → ℝ)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ R → ‖F x‖ ≤ C)
    (φ : ScalarTest) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨R, hR, C, hC, hFb⟩ := hbound
  obtain ⟨M, hM, hMb⟩ := transitionDerivative_global_bound
  obtain ⟨T, hTb⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hT : 0 ≤ T := (norm_nonneg (φ 0)).trans (hTb 0)
  let A : ℝ := 8 * M * C * T * volume.real (ball (0 : Position) 1)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x‖ ≤ A * ε ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iio_mem_nhds (by linarith : (0 : ℝ) < R / 2))] with ε hε hεR
    change 0 < ε at hε
    change ε < R / 2 at hεR
    exact shrinkingCutoffError_norm_le ε R M C T hε (by linarith) hM hC hT hMb F hFb φ hTb i
  have hl : Tendsto (fun ε : ℝ => A * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.mul (ht.pow 2)
  exact squeeze_zero_norm' he hl

theorem shrinkingCutoffError_integrable_and_tendsto (F : Position → ℝ)
    (hF : ∀ x, x ≠ 0 → ContinuousAt F x)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ R → ‖F x‖ ≤ C)
    (φ : ScalarTest) (i : Fin 3) :
    (∀ ε : ℝ, 0 < ε →
      Integrable (fun x => exteriorCutoffPartial ε ε i x * F x * φ x) volume) ∧
    Tendsto (fun ε : ℝ => ∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact ⟨fun ε hε => shrinkingCutoffError_integrable ε hε F hF φ i,
    shrinkingCutoffError_tendsto_of_bound F hbound φ i⟩

theorem shrinkingCutoffError_tendsto (F : Position → ℝ)
    (hF : ∀ x, x ≠ 0 → ContinuousAt F x)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ R → ‖F x‖ ≤ C)
    (φ : ScalarTest) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (shrinkingCutoffError_integrable_and_tendsto F hF hbound φ i).2

end OQ7Prescribed
