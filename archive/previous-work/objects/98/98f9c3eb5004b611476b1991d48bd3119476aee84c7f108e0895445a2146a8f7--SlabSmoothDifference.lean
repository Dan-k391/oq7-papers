import work.SlabPlanarMap
import work.HeightSupportDensity
import PrescribedExtinction.SlabSmoothCenteredL2Residual

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarSlabTransverse_congr_height_ae (k : ℝ) (w : ℂ → ℂ) (q f : ℝ → ℂ)
    (he : q =ᵐ[volume] f) (x : ℂ) (z : ℝ) (u v : ℂ) :
    planarSlabTransverse k w q x z u v = planarSlabTransverse k w f x z u v := by
  simp only [planarSlabTransverse_factorization, scalarPlanarPotential_congr_ae k q f he]

theorem slabLiftPolarization_smooth_current (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M : ℝ) (hAM : 0 ≤ A + M) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u : ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Metric.closedBall 0 M) :
    (slabLiftPolarization w hw A M hAM hA u (heightSmoothElement M f hf hc hs)).current =ᵐ[volume]
      fun x => slabSeparatedFunction w f x • complexify (slabPosition u 0) := by
  filter_upwards [slabLiftPolarization_current_ae w hw A M hAM hA u (heightSmoothElement M f hf hc hs),
    slabHeight_quasiMeasurePreserving.ae (heightSmoothElement_coe M f hf hc hs)] with x hp hf
  rw [hp]
  change (w (slabHorizontalCoordinate x) * (heightSmoothElement M f _ _ _ : HeightL2) (x 2)) • _ = _
  rw [hf]
  rfl

theorem slabApertureDifference_smooth_coe (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A M r L : ℝ) (hAM : 0 ≤ A + M) (hM : 0 ≤ M) (hL : 0 ≤ L) (hObs : r + L ≤ A + M)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (u v : ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Metric.closedBall 0 M) (p : CompactPolarization)
    (hp : p.current = fun x => slabSeparatedFunction w f x • complexify (slabPosition u 0)) :
    slabApertureDifference k hk w (hw.continuous.memLp_of_hasCompactSupport hwc)
      A M r L hAM hM hL hA u v (heightSmoothElement M f hf hc hs) =ᵐ[volume]
      (slabObservationRegion r L).indicator (fun x =>
        axisCoupling (slabPosition v 0) (electricVolumeField k p x) -
          planarSlabTransverse k w f (slabHorizontalCoordinate x) (x 2) u v) := by
  have hcur := slabLiftPolarization_smooth_current w (hw.continuous.memLp_of_hasCompactSupport hwc)
    A M hAM hA u f hf hc hs
  rw [← hp] at hcur
  have hfield := electricVolumeField_congr_current k _ p hcur
  filter_upwards [slabApertureDifference_coe k hk w (hw.continuous.memLp_of_hasCompactSupport hwc)
    A M r L hAM hM hL hObs hA u v (heightSmoothElement M f hf hc hs)] with x hx
  rw [hx]
  by_cases hm : x ∈ slabObservationRegion r L
  · simp only [indicator_of_mem hm]
    rw [hfield, planarSlabTransverse_congr_height_ae k w _ f (heightSmoothElement_coe M f hf hc hs)]
  · simp only [indicator_of_notMem hm]

theorem slabApertureDifference_smooth_norm_sq (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A M r L : ℝ) (hAM : 0 ≤ A + M) (hM : 0 ≤ M) (hL : 0 ≤ L) (hObs : r + L ≤ A + M)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (u v : ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Metric.closedBall 0 M) (p : CompactPolarization)
    (hp : p.current = fun x => slabSeparatedFunction w f x • complexify (slabPosition u 0)) :
    ‖slabApertureDifference k hk w (hw.continuous.memLp_of_hasCompactSupport hwc)
      A M r L hAM hM hL hA u v (heightSmoothElement M f hf hc hs)‖ ^ 2 =
      ∫ y in slabProductRegion r L, ‖slabPhysicalProjectionError k p w f u v y‖ ^ 2 := by
  let D := slabApertureDifference k hk w (hw.continuous.memLp_of_hasCompactSupport hwc)
    A M r L hAM hM hL hA u v (heightSmoothElement M f hf hc hs)
  have hi := memLp_two_integral_norm_sq (D : Position → ℂ) (Lp.memLp D)
  rw [Lp.toLp_coeFn] at hi
  change ‖D‖ ^ 2 = _
  have ht := integral_slabObservationRegion r L (fun x =>
    ‖axisCoupling (slabPosition v 0) (electricVolumeField k p x) -
      planarSlabTransverse k w f (slabHorizontalCoordinate x) (x 2) u v‖ ^ 2)
  have ht' : (∫ x in slabObservationRegion r L,
      ‖axisCoupling (slabPosition v 0) (electricVolumeField k p x) -
        planarSlabTransverse k w f (slabHorizontalCoordinate x) (x 2) u v‖ ^ 2) =
        ∫ y in slabProductRegion r L, ‖slabPhysicalProjectionError k p w f u v y‖ ^ 2 := by
    simpa [slabPhysicalProjectionError, slabHorizontalCoordinate, slabPosition] using ht
  rw [← hi, ← ht', ← integral_indicator (slabObservationRegion_measurable r L)]
  apply integral_congr_ae
  filter_upwards [slabApertureDifference_smooth_coe k hk w hw hwc A M r L hAM hM hL hObs hA u v f hf hc hs p hp] with x hx
  change ‖D x‖ ^ 2 = _
  rw [hx]
  by_cases hm : x ∈ slabObservationRegion r L
  · simp only [indicator_of_mem hm]
  · simp only [indicator_of_notMem hm, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

end OQ7Prescribed
