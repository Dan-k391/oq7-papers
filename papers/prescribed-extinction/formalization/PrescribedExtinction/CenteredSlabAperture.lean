import PrescribedExtinction.SlabPhysicalAperture

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem scalarOutgoingSlabTransverse_centered_uniform_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) q → HasCompactSupport q →
      tsupport q ⊆ Metric.closedBall 0 L → ∀ (R z : ℝ) (x u v : ℂ), 1 ≤ R → |z| ≤ L →
      ‖x‖ ≤ X * R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ‖scalarOutgoingSlabTransverse k (scaledApertureWindow w R) q x z u v -
        planarSlabTransverse k (scaledApertureWindow w R) q x z u v‖ ≤
          (C / R) * ∫ t : ℝ, ‖q t‖ := by
  obtain ⟨C, hC, he⟩ := horizontalSlabTransverseKernel_uniform_error k hk w hw hwc A X (2 * L)
    hA0 hX (by positivity) hA
  refine ⟨C, hC, ?_⟩
  intro q hq hqc hqs R z x u v hR hz hx hu hv
  have hR0 : 0 < R := by linarith
  have hW := scaledApertureWindow_contDiff w hw R
  have hWc := scaledApertureWindow_hasCompactSupport w hwc R hR0.ne'
  have hi := scalarOutgoingSlabTransverse_height_integrable k _ q hW hq hWc hqc x u v z
  have hp := planarSlabTransverse_integrable k hk (scaledApertureWindow w R) q hq.continuous hqc x u v z
  rw [scalarOutgoingSlabTransverse_separation k _ q hW hq hWc hqc, planarSlabTransverse,
    ← integral_sub hi hp]
  have hb : ∀ t : ℝ,
      ‖horizontalSlabTransverseKernel k (z - t) (scaledApertureWindow w R) x u v * q t -
        ((k ^ 2 * inner ℝ u v : ℝ) • (planarScalarGreen k (z - t) * scaledApertureWindow w R x)) * q t‖ ≤
        (C / R) * ‖q t‖ := by
    intro t
    by_cases ht : t ∈ tsupport q
    · have ht' : |t| ≤ L := by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hqs ht
      have hzt : |z - t| ≤ 2 * L := by
        have ha := abs_sub z t
        linarith
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (he R (z - t) x u v hR hzt hx hu hv) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hqi := hq.continuous.integrable_of_hasCompactSupport (μ := volume) hqc
  have hbi : Integrable (fun t : ℝ => (C / R) * ‖q t‖) volume := hqi.norm.const_mul _
  have hn := norm_integral_le_of_norm_le hbi (ae_of_all _ hb)
  rw [integral_const_mul] at hn
  exact hn

theorem electricVolumeField_centered_slab_uniform_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) q → HasCompactSupport q →
      tsupport q ⊆ Metric.closedBall 0 L → ∀ (R : ℝ) (u v : ℂ), 1 ≤ R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ p : CompactPolarization,
      p.current = (fun y => slabSeparatedFunction (scaledApertureWindow w R) q y • complexify (slabPosition u 0)) →
      ∀ᵐ y : Position ∂volume, ‖slabHorizontalCoordinate y‖ ≤ X * R → |y 2| ≤ L →
        ‖axisCoupling (slabPosition v 0) (electricVolumeField k p y) -
          planarSlabTransverse k (scaledApertureWindow w R) q (slabHorizontalCoordinate y) (y 2) u v‖ ≤
            (C / R) * ∫ t : ℝ, ‖q t‖ := by
  obtain ⟨C, hC, he⟩ := scalarOutgoingSlabTransverse_centered_uniform_error k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨C, hC, ?_⟩
  intro q hq hqc hqs R u v hR hu hv p hp
  have hR0 : 0 < R := by linarith
  have hW := scaledApertureWindow_contDiff w hw R
  have hWc := scaledApertureWindow_hasCompactSupport w hwc R hR0.ne'
  have hpc : ContDiff ℝ (⊤ : ℕ∞) p.current := by
    rw [hp]
    exact (slabSeparatedFunction_contDiff _ q hW hq).smul contDiff_const
  filter_upwards [smoothDyadicField_eq_electricVolumeField k p hpc] with y hy
  intro hx hz
  rw [← hy, ← slabPosition_horizontal_height y,
    smoothDyadicField_slab_source_projection k p _ q hW hq hWc hqc u v _ _ hp]
  simpa only [slabPosition_horizontal_height] using he q hq hqc hqs R (y 2)
    (slabHorizontalCoordinate y) u v hR hz hx hu hv

end OQ7Prescribed
