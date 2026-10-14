import work.BodyLayerSeparatedCurrent
import work.BodyApertureWindow
import PrescribedExtinction.SlabL2PhysicalError

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem bodyHeight_pos (B : TwoLayerBody) : 0 < B.absorberThickness + B.plateThickness :=
  add_pos B.absorberThickness_pos B.plateThickness_pos

def bodyScaledScalarLift (B : TwoLayerBody) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    PlanarCurrentL2 (B.absorberThickness + B.plateThickness) →L[ℂ] ScalarBodyCurrentL2 B :=
  bodySeparatedScalarLift B (scaledApertureWindow w B.aperture)
    ((scaledApertureWindow_contDiff w hw B.aperture).continuous.memLp_of_hasCompactSupport
      (scaledApertureWindow_hasCompactSupport w hwc B.aperture B.aperture_pos.ne'))
    (scaledApertureWindow_support_square w B.aperture B.aperture_pos hs)

theorem bodyScaledScalarLift_norm (B : TwoLayerBody) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    ‖bodyScaledScalarLift B w hw hwc hs q‖ =
      B.aperture * ‖(hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc).toLp w‖ * ‖q‖ := by
  rw [bodyScaledScalarLift, bodySeparatedScalarLift_norm,
    scaledApertureWindow_L2_norm w hw hwc B.aperture B.aperture_pos]

def bodySlabComponent (B : TwoLayerBody) (hR : 1 ≤ B.aperture) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (u : ℂ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) : CompactPolarization :=
  scaledSlabPolarization w hw hwc 1 1 (B.absorberThickness + B.plateThickness)
    (by norm_num) (by norm_num) (bodyHeight_pos B).le
    (hs.trans horizontalSquareAperture_subset_ball) B.aperture hR u
    (planarHeightEmbedding _ (bodyHeight_pos B).le q)

theorem bodyScaledLayerField_decomposition (k : ℝ) (B : TwoLayerBody) (hR : 1 ≤ B.aperture)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (θ : ℝ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    electricVolumeField k (bodyCurrentPolarization B
      (activeInjection B (basisR 0) (rotatedAxis θ) (bodyScaledScalarLift B w hw hwc hs q))) =ᵐ[volume]
      fun x => electricVolumeField k (bodySlabComponent B hR w hw hwc hs 1
        (planarLayerAxisMap _ B.absorberThickness 1 (Real.cos θ) q)) x +
          electricVolumeField k (bodySlabComponent B hR w hw hwc hs Complex.I
            (planarLayerAxisMap _ B.absorberThickness 0 (Real.sin θ) q)) x := by
  let C := planarLayerAxisMap (B.absorberThickness + B.plateThickness) B.absorberThickness 1 (Real.cos θ) q
  let S := planarLayerAxisMap (B.absorberThickness + B.plateThickness) B.absorberThickness 0 (Real.sin θ) q
  let p := bodySlabComponent B hR w hw hwc hs 1 C
  let r := bodySlabComponent B hR w hw hwc hs Complex.I S
  have hp := scaledSlabPolarization_current_ae w hw hwc 1 1 _ (by norm_num) (by norm_num)
    (bodyHeight_pos B).le (hs.trans horizontalSquareAperture_subset_ball) B.aperture hR 1
    (planarHeightEmbedding _ (bodyHeight_pos B).le C)
  have hr := scaledSlabPolarization_current_ae w hw hwc 1 1 _ (by norm_num) (by norm_num)
    (bodyHeight_pos B).le (hs.trans horizontalSquareAperture_subset_ball) B.aperture hR Complex.I
    (planarHeightEmbedding _ (bodyHeight_pos B).le S)
  have hcur : (bodyCurrentPolarization B
      (activeInjection B (basisR 0) (rotatedAxis θ) (bodyScaledScalarLift B w hw hwc hs q))).current
      =ᵐ[volume] (p.add r).current := by
    filter_upwards [bodyLayerSeparatedPolarization_current_ae B _ _ _ θ q, hp, hr] with x hx hp hr
    change (bodyLayerSeparatedPolarization B _ _ _ θ q).current x = p.current x + r.current x
    rw [hx]
    change p.current x = _ at hp
    change r.current x = _ at hr
    rw [hp, hr]
    change _ = (scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (C : HeightL2) (x 2)) •
      complexify (slabPosition 1 0) + (scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (S : HeightL2) (x 2)) •
      complexify (slabPosition Complex.I 0)
    rw [smul_add, smul_smul, smul_smul]
    congr 1 <;> ext i <;> fin_cases i <;> simp [complexify, slabPosition, basisC, C, S]
  rw [electricVolumeField_congr_current k _ _ hcur]
  exact electricVolumeField_add_ae k p r

end OQ7Prescribed
