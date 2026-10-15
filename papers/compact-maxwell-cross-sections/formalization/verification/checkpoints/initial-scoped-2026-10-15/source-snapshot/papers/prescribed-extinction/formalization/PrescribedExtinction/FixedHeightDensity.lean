import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped ENNReal

theorem heightProfile_fixed_support_smooth_density (f : ℝ → ℂ)
    (hf : MemLp f 2 volume) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ᵐ t : ℝ ∂volume, t ∉ Metric.closedBall 0 L → f t = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) q ∧ HasCompactSupport q ∧
      tsupport q ⊆ Metric.closedBall 0 (L + 2) ∧
      eLpNorm (f - q) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hgc, hgd, hge⟩ := hf.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hε
  let η : ContDiffBump (0 : ℝ) := ⟨L + 1, L + 2, by linarith, by linarith⟩
  let q : ℝ → ℂ := fun t => η t • g t
  have hqs : tsupport q ⊆ Metric.closedBall 0 (L + 2) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro t ht
    by_contra hn
    have he : η t = 0 := η.zero_of_le_dist (by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using (lt_of_not_ge
        (show ¬ ‖t‖ ≤ L + 2 by simpa only [Metric.mem_closedBall, dist_zero_right] using hn)).le)
    exact ht (by simp [q, he])
  have hqc : HasCompactSupport q := (isCompact_closedBall 0 (L + 2)).of_isClosed_subset
    (isClosed_tsupport q) hqs
  have hqd : ContDiff ℝ (⊤ : ℕ∞) q := η.contDiff.smul hgd
  have hqm : MemLp q 2 volume := hqd.continuous.memLp_of_hasCompactSupport hqc
  refine ⟨q, hqd, hqc, hqs, ?_⟩
  apply (eLpNorm_mono_ae (hf.sub hqm).aestronglyMeasurable ?_).trans hge
  filter_upwards [hs] with t ht
  have hfix : η t • f t = f t := by
    by_cases hn : t ∈ Metric.closedBall 0 L
    · have hm : t ∈ Metric.closedBall 0 (L + 1) := by
        simp only [Metric.mem_closedBall, dist_zero_right] at hn ⊢
        linarith
      rw [η.one_of_mem_closedBall hm, one_smul]
    · rw [ht hn, smul_zero]
  change ‖f t - η t • g t‖ ≤ ‖f t - g t‖
  have hd : f t - η t • g t = η t • (f t - g t) := by
    rw [smul_sub, hfix]
  rw [hd, norm_smul]
  have hb : ‖η t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg η.nonneg]
    exact η.le_one
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (f t - g t))

end OQ7Prescribed
