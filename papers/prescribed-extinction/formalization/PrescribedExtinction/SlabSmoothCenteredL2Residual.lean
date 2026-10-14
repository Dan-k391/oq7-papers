import PrescribedExtinction.CenteredSlabAperture
import PrescribedExtinction.SlabSmoothL2Residual
import PrescribedExtinction.HeightL1Bound

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
theorem electricVolumeField_centered_smooth_slab_uniform_L2_residual (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) q → HasCompactSupport q →
      tsupport q ⊆ Metric.closedBall 0 L → ∀ (R : ℝ) (u v : ℂ), 1 ≤ R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ p : CompactPolarization,
      p.current = (fun y => slabSeparatedFunction (scaledApertureWindow w R) q y •
        complexify (slabPosition u 0)) →
      (∫ y in slabProductRegion (X * R) L,
        ‖slabPhysicalProjectionError k p (scaledApertureWindow w R) q u v y‖ ^ 2) ≤
          C ^ 2 * (∫ t : ℝ, ‖q t‖) ^ 2 * X ^ 2 * Real.pi * L := by
  obtain ⟨C, hC, he⟩ := electricVolumeField_centered_slab_uniform_error k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨C, hC, ?_⟩
  intro q hq hqc hqs R u v hR hu hv p hp
  have hR0 : 0 < R := by linarith
  have hW := scaledApertureWindow_contDiff w hw R
  have hWc := scaledApertureWindow_hasCompactSupport w hwc R hR0.ne'
  have hmeas := slabPhysicalProjectionError_aestronglyMeasurable k p _ q hW hq hWc hqc u v hp
  have heq := slabCoordinateEquiv_measurePreserving.quasiMeasurePreserving.ae
    (he q hq hqc hqs R u v hR hu hv p hp)
  have hb : ∀ᵐ y : ℂ × ℝ ∂volume, y ∈ slabProductRegion (X * R) L →
      ‖slabPhysicalProjectionError k p (scaledApertureWindow w R) q u v y‖ ≤
        (C * ∫ t : ℝ, ‖q t‖) / R := by
    filter_upwards [heq] with y hy
    intro hs
    have hx : ‖y.1‖ ≤ X * R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hs.1
    have hid : slabHorizontalCoordinate (slabCoordinateEquiv y) = y.1 := by
      simp [slabCoordinateEquiv_apply, slabHorizontalCoordinate, slabPosition]
    have hheight : (slabCoordinateEquiv y) 2 = y.2 := by simp [slabCoordinateEquiv_apply, slabPosition]
    rw [hid, hheight] at hy
    have hz : |y.2| ≤ L := by rw [abs_of_nonneg hs.2.1]; exact hs.2.2
    have h := hy hx hz
    simpa only [slabPhysicalProjectionError, slabCoordinateEquiv_apply, div_mul_eq_mul_div] using h
  have hD : 0 ≤ C * ∫ t : ℝ, ‖q t‖ := mul_nonneg hC.le (integral_nonneg (fun _ => norm_nonneg _))
  have hl := slabProduct_uniform_error_integral_sq _ hmeas _ X L R hD hX hL hR0 hb
  simpa only [mul_pow, mul_assoc] using hl

theorem electricVolumeField_smooth_slab_residual_norm_sq (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
      (hqc : HasCompactSupport q), tsupport q ⊆ Metric.closedBall 0 L →
      ∀ (R : ℝ) (u v : ℂ), 1 ≤ R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ∀ p : CompactPolarization,
      p.current = (fun y => slabSeparatedFunction (scaledApertureWindow w R) q y • complexify (slabPosition u 0)) →
      (∫ y in slabProductRegion (X * R) L,
        ‖slabPhysicalProjectionError k p (scaledApertureWindow w R) q u v y‖ ^ 2) ≤
          2 * C ^ 2 * X ^ 2 * Real.pi * L ^ 2 *
            ‖(hq.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hqc).toLp q‖ ^ 2 := by
  obtain ⟨C, hC, he⟩ := electricVolumeField_centered_smooth_slab_uniform_L2_residual k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨C, hC, ?_⟩
  intro q hq hqc hqs R u v hR hu hv p hp
  have hqm : MemLp q 2 volume := hq.continuous.memLp_of_hasCompactSupport hqc
  have hs : ∀ᵐ t : ℝ ∂volume, t ∉ Icc (-L) L → q t = 0 := by
    apply ae_of_all
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hn
    apply ht
    have hb : |t| ≤ L := by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hqs hn
    exact abs_le.mp hb
  have hi := heightProfile_integral_norm_bound q hqm L hL hs
  have hQ : 0 ≤ ∫ t : ℝ, ‖q t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hn : (∫ t : ℝ, ‖q t‖) ^ 2 ≤ ‖hqm.toLp q‖ ^ 2 * (2 * L) := by
    have hr := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
    have hp := mul_nonneg (norm_nonneg (hqm.toLp q)) (Real.sqrt_nonneg (2 * L))
    nlinarith
  have hc : 0 ≤ C ^ 2 * X ^ 2 * Real.pi * L := by positivity
  have hm := mul_le_mul_of_nonneg_right hn hc
  refine (he q hq hqc hqs R u v hR hu hv p hp).trans ?_
  convert hm using 1 <;> ring

end OQ7Prescribed
