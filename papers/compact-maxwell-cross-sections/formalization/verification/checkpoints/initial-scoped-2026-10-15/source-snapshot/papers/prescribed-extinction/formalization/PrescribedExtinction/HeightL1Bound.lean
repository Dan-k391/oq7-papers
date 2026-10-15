import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped ENNReal

theorem heightProfile_integrable (q : ℝ → ℂ) (hq : MemLp q 2 volume) (L : ℝ)
    (hs : ∀ᵐ t : ℝ ∂volume, t ∉ Icc (-L) L → q t = 0) : Integrable q volume := by
  have hqr : MemLp q 2 (volume.restrict (Icc (-L) L)) := hq.mono_measure Measure.restrict_le_self
  have hr := hqr.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi : Integrable ((Icc (-L) L).indicator q) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hr
  apply hi.congr
  filter_upwards [hs] with t ht
  by_cases hn : t ∈ Icc (-L) L
  · simp only [indicator_of_mem hn]
  · simp [hn, ht hn]

theorem heightProfile_integral_norm_bound (q : ℝ → ℂ) (hq : MemLp q 2 volume)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ᵐ t : ℝ ∂volume, t ∉ Icc (-L) L → q t = 0) :
    (∫ t : ℝ, ‖q t‖) ≤ ‖hq.toLp q‖ * Real.sqrt (2 * L) := by
  have hind : (Icc (-L) L).indicator q =ᵐ[volume] q := by
    filter_upwards [hs] with t ht
    by_cases hn : t ∈ Icc (-L) L
    · simp only [indicator_of_mem hn]
    · simp [hn, ht hn]
  have heq (p : ℝ≥0∞) : eLpNorm q p (volume.restrict (Icc (-L) L)) = eLpNorm q p volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc, eLpNorm_congr_ae hind]
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := q)
    (μ := volume.restrict (Icc (-L) L)) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (hq.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  rw [heq 1, heq 2, Measure.restrict_apply_univ, Real.volume_Icc] at he
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div_one, one_div] at he
  have hfinite : eLpNorm q 2 volume * ENNReal.ofReal (L - -L) ^ ((1 : ℝ) / 2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top hq.eLpNorm_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  have hr := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ L - -L)] at hr
  rw [Lp.norm_toLp, ← lpNorm_one_eq_integral_norm hq.aestronglyMeasurable]
  change (eLpNorm q 1 volume).toReal ≤ _
  simpa [Real.sqrt_eq_rpow, sub_neg_eq_add, two_mul] using hr

end OQ7Prescribed
