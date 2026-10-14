import PrescribedExtinction.SlabDyadicSeparation

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped InnerProductSpace

def planarSlabTransverse (k : ℝ) (w : ℂ → ℂ) (q : ℝ → ℂ) (x : ℂ) (z : ℝ) (u v : ℂ) : ℂ :=
  ∫ t : ℝ, ((k ^ 2 * inner ℝ u v : ℝ) • (planarScalarGreen k (z - t) * w x)) * q t

theorem planarSlabTransverse_integrable (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hq : Continuous q) (hqc : HasCompactSupport q) (x u v : ℂ) (z : ℝ) :
    Integrable (fun t : ℝ => ((k ^ 2 * inner ℝ u v : ℝ) •
      (planarScalarGreen k (z - t) * w x)) * q t) volume := by
  have hg : Continuous (fun t : ℝ => planarScalarGreen k (z - t)) := by
    unfold planarScalarGreen
    exact continuous_const.mul ((apertureOscillation_continuous k).comp
      ((continuous_const.sub continuous_id).abs))
  have hf : Continuous (fun t : ℝ => (k ^ 2 * inner ℝ u v : ℝ) •
      (planarScalarGreen k (z - t) * w x)) :=
    (continuous_const : Continuous (fun _ : ℝ => (k ^ 2 * inner ℝ u v : ℝ))).smul
      (hg.mul (continuous_const : Continuous (fun _ : ℝ => w x)))
  apply (hq.integrable_of_hasCompactSupport (μ := volume) hqc).bdd_mul
    (c := ‖(k ^ 2 * inner ℝ u v : ℝ)‖ * ((2 * k)⁻¹ * ‖w x‖)) hf.aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    change ‖(k ^ 2 * inner ℝ u v : ℝ) • (planarScalarGreen k (z - t) * w x)‖ ≤ _
    simp only [norm_smul, norm_mul, planarScalarGreen_norm k (z - t) hk, one_div, le_refl])

theorem scalarOutgoingSlabTransverse_uniform_aperture_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) q → HasCompactSupport q →
      tsupport q ⊆ Icc 0 L → ∀ (R z : ℝ) (x u v : ℂ), 1 ≤ R → z ∈ Icc 0 L →
      ‖x‖ ≤ X * R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ‖scalarOutgoingSlabTransverse k (scaledApertureWindow w R) q x z u v -
        planarSlabTransverse k (scaledApertureWindow w R) q x z u v‖ ≤
          (C / R) * ∫ t : ℝ, ‖q t‖ := by
  obtain ⟨C, hC, he⟩ := horizontalSlabTransverseKernel_uniform_error k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨C, hC, ?_⟩
  intro q hq hqc hqs R z x u v hR hz hx hu hv
  have hR0 : 0 < R := by linarith
  have hW := scaledApertureWindow_contDiff w hw R
  have hWc := scaledApertureWindow_hasCompactSupport w hwc R hR0.ne'
  have hi := scalarOutgoingSlabTransverse_height_integrable k _ q hW hq hWc hqc x u v z
  have hp := planarSlabTransverse_integrable k hk (scaledApertureWindow w R) q hq.continuous hqc x u v z
  rw [scalarOutgoingSlabTransverse_separation k _ q hW hq hWc hqc, planarSlabTransverse,
    ← integral_sub hi hp]
  have hbound : ∀ t : ℝ,
      ‖horizontalSlabTransverseKernel k (z - t) (scaledApertureWindow w R) x u v * q t -
        ((k ^ 2 * inner ℝ u v : ℝ) • (planarScalarGreen k (z - t) * scaledApertureWindow w R x)) * q t‖ ≤
        (C / R) * ‖q t‖ := by
    intro t
    by_cases ht : t ∈ tsupport q
    · have ht' := hqs ht
      have hzt : |z - t| ≤ L := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2, ht'.1, ht'.2]
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (he R (z - t) x u v hR hzt hx hu hv) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hqi := hq.continuous.integrable_of_hasCompactSupport (μ := volume) hqc
  have hbi : Integrable (fun t : ℝ => (C / R) * ‖q t‖) volume := hqi.norm.const_mul _
  have hb := norm_integral_le_of_norm_le hbi (ae_of_all _ hbound)
  rw [integral_const_mul] at hb
  exact hb

end OQ7Prescribed
