import PrescribedExtinction.PlanarScalarPotential
import PrescribedExtinction.SlabProductResidual

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabPhysicalProjectionError (k : ℝ) (p : CompactPolarization)
    (w : ℂ → ℂ) (q : ℝ → ℂ) (u v : ℂ) (y : ℂ × ℝ) : ℂ :=
  axisCoupling (slabPosition v 0) (electricVolumeField k p (slabPosition y.1 y.2)) -
    planarSlabTransverse k w q y.1 y.2 u v

theorem slabPhysicalProjectionError_aestronglyMeasurable (k : ℝ) (p : CompactPolarization)
    (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (u v : ℂ)
    (hp : p.current = fun y => slabSeparatedFunction w q y • complexify (slabPosition u 0)) :
    AEStronglyMeasurable (slabPhysicalProjectionError k p w q u v) volume := by
  have hpc : ContDiff ℝ (⊤ : ℕ∞) p.current := by
    rw [hp]
    exact (slabSeparatedFunction_contDiff w q hw hq).smul contDiff_const
  have hslab : Continuous (fun y : ℂ × ℝ => slabPosition y.1 y.2) := by
    unfold slabPosition
    fun_prop
  have hfield := (smoothDyadicField_contDiff k p hpc).continuous.comp hslab
  have haxis : Continuous (fun y : ℂ × ℝ =>
      axisCoupling (slabPosition v 0) (smoothDyadicField k p (slabPosition y.1 y.2))) := by
    simp_rw [axisCoupling_eq_inner]
    exact continuous_const.inner hfield
  have heq := slabCoordinateEquiv_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (smoothDyadicField_eq_electricVolumeField k p hpc)
  have hae : (fun y : ℂ × ℝ => axisCoupling (slabPosition v 0)
      (smoothDyadicField k p (slabPosition y.1 y.2))) =ᵐ[volume]
      fun y => axisCoupling (slabPosition v 0) (electricVolumeField k p (slabPosition y.1 y.2)) := by
    filter_upwards [heq] with y hy
    simpa only [Function.comp_apply, slabCoordinateEquiv_apply] using congrArg (axisCoupling (slabPosition v 0)) hy
  exact (haxis.aestronglyMeasurable.congr hae).sub
    (planarSlabTransverse_continuous_product k w q hw.continuous hq hqc u v).aestronglyMeasurable

theorem electricVolumeField_smooth_slab_uniform_L2_residual (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) q → HasCompactSupport q →
      tsupport q ⊆ Icc 0 L → ∀ (R : ℝ) (u v : ℂ), 1 ≤ R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ p : CompactPolarization,
      p.current = (fun y => slabSeparatedFunction (scaledApertureWindow w R) q y •
        complexify (slabPosition u 0)) →
      (∫ y in slabProductRegion (X * R) L,
        ‖slabPhysicalProjectionError k p (scaledApertureWindow w R) q u v y‖ ^ 2) ≤
          C ^ 2 * (∫ t : ℝ, ‖q t‖) ^ 2 * X ^ 2 * Real.pi * L := by
  obtain ⟨C, hC, he⟩ := electricVolumeField_slab_uniform_aperture_error k hk w hw hwc A X L hA0 hX hL hA
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
    have h := hy hx hs.2
    simpa only [slabPhysicalProjectionError, slabCoordinateEquiv_apply, div_mul_eq_mul_div] using h
  have hD : 0 ≤ C * ∫ t : ℝ, ‖q t‖ := mul_nonneg hC.le (integral_nonneg (fun _ => norm_nonneg _))
  have hl := slabProduct_uniform_error_integral_sq _ hmeas _ X L R hD hX hL hR0 hb
  simpa only [mul_pow, mul_assoc] using hl

end OQ7Prescribed
