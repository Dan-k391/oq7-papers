import work.SlabSmoothDifference
import work.DenseNormBound

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem scaledApertureWindow_support_enlarged (w : ℂ → ℂ) (A X R : ℝ)
    (hX : 0 ≤ X) (hR : 0 < R) (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    tsupport (scaledApertureWindow w R) ⊆ Metric.closedBall 0 ((A + X) * R) := by
  refine (scaledApertureWindow_support w R A hR hA).trans (Metric.closedBall_subset_closedBall ?_)
  nlinarith

def scaledSlabApertureDifference (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (R : ℝ) (hR : 1 ≤ R) (u v : ℂ) :
    HeightSupportedL2 (L + 2) →L[ℂ] ScalarVolumeL2 :=
  slabApertureDifference k hk (scaledApertureWindow w R)
    ((scaledApertureWindow_contDiff w hw R).continuous.memLp_of_hasCompactSupport
      (scaledApertureWindow_hasCompactSupport w hwc R (by linarith)))
    ((A + X) * R) (L + 2) (X * R) (L + 2) (by positivity) (by linarith) (by linarith)
    (scaledApertureWindow_support_enlarged w A X R hX (by linarith) hA) u v

theorem scaledSlabApertureDifference_smooth_bound (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 1 ≤ R) (u v : ℂ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
        (hs : tsupport f ⊆ Metric.closedBall 0 (L + 2)),
        ‖scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
          (heightSmoothElement (L + 2) f hf hc hs)‖ ≤ K * ‖heightSmoothElement (L + 2) f hf hc hs‖ := by
  have hM : 0 ≤ L + 2 := by linarith
  obtain ⟨C, hC, he⟩ := electricVolumeField_smooth_slab_residual_norm_sq k hk w hw hwc A X (L + 2) hA0 hX hM hA
  let B := 2 * C ^ 2 * X ^ 2 * Real.pi * (L + 2) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨Real.sqrt B + 1, by positivity, ?_⟩
  intro R hR u v hu hv f hf hc hs
  have hR0 : 0 < R := by linarith
  let W := scaledApertureWindow w R
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := scaledApertureWindow_contDiff w hw R
  have hWc : HasCompactSupport W := scaledApertureWindow_hasCompactSupport w hwc R hR0.ne'
  let F := slabSeparatedFunction W f
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := slabSeparatedFunction_contDiff W f hW hf
  have hFc : HasCompactSupport F := slabSeparatedFunction_hasCompactSupport W f hWc hc
  let p := scalarAxisPolarization F hF.continuous hFc (slabPosition u 0)
  have hp : p.current = fun x => slabSeparatedFunction W f x • complexify (slabPosition u 0) := rfl
  have hWsupport := scaledApertureWindow_support_enlarged w A X R hX hR0 hA
  have hAM : 0 ≤ (A + X) * R + (L + 2) := by positivity
  have hObs : X * R + (L + 2) ≤ (A + X) * R + (L + 2) := by nlinarith
  have hid := slabApertureDifference_smooth_norm_sq k hk W hW hWc ((A + X) * R) (L + 2)
    (X * R) (L + 2) hAM hM hM hObs hWsupport u v f hf hc hs p hp
  have hb := he f hf hc hs R u v hR hu hv p hp
  rw [← hid] at hb
  change ‖scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
    (heightSmoothElement (L + 2) f hf hc hs)‖ ^ 2 ≤ B * ‖heightSmoothElement (L + 2) f hf hc hs‖ ^ 2 at hb
  have hsqrt := Real.sq_sqrt hB
  have hn := norm_nonneg (heightSmoothElement (L + 2) f hf hc hs)
  have hleft := norm_nonneg (scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
    (heightSmoothElement (L + 2) f hf hc hs))
  have hprod := mul_nonneg (Real.sqrt_nonneg B) hn
  have hsmall : ‖scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
      (heightSmoothElement (L + 2) f hf hc hs)‖ ≤ Real.sqrt B * ‖heightSmoothElement (L + 2) f hf hc hs‖ := by
    nlinarith
  nlinarith

theorem physicalSlab_uniform_L2_aperture_residual (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 1 ≤ R) (u v : ℂ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ q : HeightSupportedL2 L,
        ‖scaledSlabApertureDifference k hk w hw hwc A X L hA0 hX hL hA R hR u v
          (heightSupportEnlargement L q)‖ ≤ K * ‖q‖ := by
  obtain ⟨K, hK, he⟩ := scaledSlabApertureDifference_smooth_bound k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨K, hK, ?_⟩
  intro R hR u v hu hv q
  rw [← heightSupportEnlargement_norm L q]
  apply norm_bound_of_close_approximants
  intro ε hε
  obtain ⟨f, hf, hc, hs, hclose⟩ := heightSupported_fixed_smooth_approximation L hL q ε hε
  exact ⟨heightSmoothElement (L + 2) f hf hc hs, hclose, he R hR u v hu hv f hf hc hs⟩

end OQ7Prescribed
