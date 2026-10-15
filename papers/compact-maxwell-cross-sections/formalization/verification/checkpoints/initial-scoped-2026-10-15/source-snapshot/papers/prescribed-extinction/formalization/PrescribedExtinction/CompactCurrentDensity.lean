import PrescribedExtinction.VolumePotential
import PrescribedExtinction.StaticFourier
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! Smooth compact currents approximate every original compact L² current
inside one fixed support ball. The support radius does not grow as the
approximation error shrinks. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped ENNReal

theorem compactPolarization_smooth_function_approximation (p : CompactPolarization)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Field, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ x : Position, p.radius + 2 < ‖x‖ → f x = 0) ∧
      eLpNorm (p.current - f) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hgs, hgc, hgerr⟩ := MemLp.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2) p.memLp hε
  let η : ContDiffBump (0 : Position) := ⟨p.radius + 1, p.radius + 2, by linarith [p.radius_nonneg], by linarith⟩
  let f : Field := fun x => η x • g x
  have hfv : ∀ x : Position, p.radius + 2 < ‖x‖ → f x = 0 := by
    intro x hx
    change η x • g x = 0
    rw [η.zero_of_le_dist (by simpa [dist_zero_right] using hx.le), zero_smul]
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) (p.radius + 2))
    intro x hx
    apply hfv
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hfc : ContDiff ℝ (⊤ : ℕ∞) f := η.contDiff.smul hgc
  have hfm : MemLp f 2 volume := hfc.continuous.memLp_of_hasCompactSupport hfs
  have hpf : ∀ x : Position, p.current x = η x • p.current x := by
    intro x
    by_cases hx : ‖x‖ ≤ p.radius
    · rw [η.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using
        (show ‖x‖ ≤ p.radius + 1 by linarith)), one_smul]
    · rw [p.vanish x (lt_of_not_ge hx), smul_zero]
  have herr : eLpNorm (p.current - f) 2 volume ≤ ENNReal.ofReal ε := by
    apply le_trans (eLpNorm_mono_ae (p.memLp.sub hfm).aestronglyMeasurable ?_) hgerr
    apply ae_of_all
    intro x
    change ‖p.current x - η x • g x‖ ≤ ‖p.current x - g x‖
    have hd : p.current x - η x • g x = η x • (p.current x - g x) := by
      rw [smul_sub, ← hpf x]
    rw [hd, norm_smul]
    have hb : ‖η x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg η.nonneg]; exact η.le_one
    simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  exact ⟨f, hfc, hfs, hfv, herr⟩

theorem compactPolarization_smooth_approximation (p : CompactPolarization) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : CompactPolarization, q.radius = p.radius + 2 ∧
      ContDiff ℝ (⊤ : ℕ∞) q.current ∧
      ‖p.memLp.toLp p.current - q.memLp.toLp q.current‖ ≤ ε := by
  obtain ⟨f, hfc, hfs, hfv, herr⟩ := compactPolarization_smooth_function_approximation p ε hε
  have hfm : MemLp f 2 volume := hfc.continuous.memLp_of_hasCompactSupport hfs
  let q : CompactPolarization := {
    current := f
    radius := p.radius + 2
    radius_nonneg := by linarith [p.radius_nonneg]
    memLp := hfm
    vanish := hfv }
  refine ⟨q, rfl, hfc, ?_⟩
  change ‖p.memLp.toLp p.current - hfm.toLp f‖ ≤ ε
  rw [← MemLp.toLp_sub, Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top herr).trans_eq (ENNReal.toReal_ofReal hε.le)

end OQ7Prescribed
