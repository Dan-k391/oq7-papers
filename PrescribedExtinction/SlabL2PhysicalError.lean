import PrescribedExtinction.SlabL2Aperture

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem lp_norm_sq_eq_restricted_integral (D : ScalarVolumeL2) (s : Set Position)
    (hs : MeasurableSet s) (f : Position → ℂ) (he : D =ᵐ[volume] s.indicator f) :
    ‖D‖ ^ 2 = ∫ x in s, ‖f x‖ ^ 2 := by
  have hi := memLp_two_integral_norm_sq (D : Position → ℂ) (Lp.memLp D)
  rw [Lp.toLp_coeFn] at hi
  rw [← hi, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]
  by_cases hm : x ∈ s
  · simp only [indicator_of_mem hm]
  · simp only [indicator_of_notMem hm, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

def scaledSlabPolarization (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (R : ℝ) (hR : 1 ≤ R) (u : ℂ)
    (q : HeightSupportedL2 L) : CompactPolarization :=
  slabLiftPolarization (scaledApertureWindow w R)
    ((scaledApertureWindow_contDiff w hw R).continuous.memLp_of_hasCompactSupport
      (scaledApertureWindow_hasCompactSupport w hwc R (by linarith)))
    ((A + X) * R) (L + 2) (by positivity)
    (scaledApertureWindow_support_enlarged w A X R hX (by linarith) hA) u
    (heightSupportEnlargement L q)

theorem scaledSlabPolarization_current_ae (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (R : ℝ) (hR : 1 ≤ R) (u : ℂ)
    (q : HeightSupportedL2 L) :
    (scaledSlabPolarization w hw hwc A X L hA0 hX hL hA R hR u q).current =ᵐ[volume]
      fun x => slabSeparatedFunction (scaledApertureWindow w R) (q : HeightL2) x • complexify (slabPosition u 0) :=
  slabLiftPolarization_current_ae _ _ _ _ _ _ _ _

theorem scaledSlabApertureDifference_coe (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (R : ℝ) (hR : 1 ≤ R) (u v : ℂ)
    (q : HeightSupportedL2 L) :
    scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
      (heightSupportEnlargement L q) =ᵐ[volume]
      (slabObservationRegion (X * R) (L + 2)).indicator (fun x =>
        axisCoupling (slabPosition v 0)
          (electricVolumeField k (scaledSlabPolarization w hw hwc A X L hA0 hX hL hA R hR u q) x) -
            planarSlabTransverse k (scaledApertureWindow w R) (q : HeightL2)
              (slabHorizontalCoordinate x) (x 2) u v) := by
  have hR0 : 0 < R := by linarith
  have hM : 0 ≤ L + 2 := by linarith
  have hAM : 0 ≤ (A + X) * R + (L + 2) := by positivity
  have hObs : X * R + (L + 2) ≤ (A + X) * R + (L + 2) := by nlinarith
  exact slabApertureDifference_coe k hk _ _ ((A + X) * R) (L + 2) (X * R) (L + 2)
    hAM hM hM hObs (scaledApertureWindow_support_enlarged w A X R hX hR0 hA) u v (heightSupportEnlargement L q)

theorem electricVolumeField_L2_slab_uniform_error (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 1 ≤ R) (u v : ℂ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ q : HeightSupportedL2 L,
        (∫ x in slabObservationRegion (X * R) (L + 2),
          ‖axisCoupling (slabPosition v 0)
            (electricVolumeField k (scaledSlabPolarization w hw hwc A X L hA0 hX hL hA R hR u q) x) -
              planarSlabTransverse k (scaledApertureWindow w R) (q : HeightL2)
                (slabHorizontalCoordinate x) (x 2) u v‖ ^ 2) ≤ K ^ 2 * ‖q‖ ^ 2 := by
  obtain ⟨K, hK, he⟩ := physicalSlab_uniform_L2_aperture_residual k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨K, hK, ?_⟩
  intro R hR u v hu hv q
  rw [← lp_norm_sq_eq_restricted_integral _ _ (slabObservationRegion_measurable _ _) _
    (scaledSlabApertureDifference_coe k hk w hw hwc A X L hA0 hX hL hA R hR u v q)]
  have hb := he R hR u v hu hv q
  have hn := norm_nonneg (scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
    (heightSupportEnlargement L q))
  have hp := mul_nonneg hK.le (norm_nonneg q)
  nlinarith

end OQ7Prescribed
