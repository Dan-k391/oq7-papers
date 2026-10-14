import work.SlabSupportedLift
import PrescribedExtinction.FixedHeightDensity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped ENNReal

def heightSmoothElement (M : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Metric.closedBall 0 M) : HeightSupportedL2 M :=
  ⟨(hf.continuous.memLp_of_hasCompactSupport hc).toLp f, by
    filter_upwards [(hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc).coeFn_toLp] with t ht
    intro hn
    rw [ht]
    apply image_eq_zero_of_notMem_tsupport
    intro hfmem
    apply hn
    have he : |t| ≤ M := by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hs hfmem
    exact abs_le.mp he⟩

theorem heightSmoothElement_coe (M : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Metric.closedBall 0 M) :
    (heightSmoothElement M f hf hc hs : HeightL2) =ᵐ[volume] f :=
  (hf.continuous.memLp_of_hasCompactSupport hc).coeFn_toLp

def heightSupportEnlargement (L : ℝ) (q : HeightSupportedL2 L) : HeightSupportedL2 (L + 2) :=
  ⟨(q : HeightL2), by
    change ∀ᵐ t : ℝ ∂volume, t ∉ Icc (-(L + 2)) (L + 2) → (q : HeightL2) t = 0
    filter_upwards [q.property] with t ht
    intro hn
    apply ht
    intro hm
    apply hn
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩⟩

theorem heightSupportEnlargement_norm (L : ℝ) (q : HeightSupportedL2 L) :
    ‖heightSupportEnlargement L q‖ = ‖q‖ := rfl

theorem heightSupported_fixed_smooth_approximation (L : ℝ) (hL : 0 ≤ L)
    (q : HeightSupportedL2 L) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
      (hs : tsupport f ⊆ Metric.closedBall 0 (L + 2)),
      ‖heightSupportEnlargement L q - heightSmoothElement (L + 2) f hf hc hs‖ ≤ ε := by
  have hball : ∀ᵐ t : ℝ ∂volume, t ∉ Metric.closedBall 0 L → (q : HeightL2) t = 0 := by
    filter_upwards [q.property] with t ht
    intro hn
    apply ht
    intro hm
    apply hn
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact abs_le.mpr hm
  obtain ⟨f, hf, hc, hs, he⟩ := heightProfile_fixed_support_smooth_density
    (q : HeightL2) (Lp.memLp (q : HeightL2)) L hL hball ε hε
  refine ⟨f, hf, hc, hs, ?_⟩
  have hfm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  change ‖(q : HeightL2) - hfm.toLp f‖ ≤ ε
  nth_rw 1 [← Lp.toLp_coeFn (q : HeightL2) (Lp.memLp (q : HeightL2))]
  rw [← MemLp.toLp_sub, Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hε.le)

end OQ7Prescribed
