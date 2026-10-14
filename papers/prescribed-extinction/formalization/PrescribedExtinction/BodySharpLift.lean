import PrescribedExtinction.DriveWindowMismatch
import PrescribedExtinction.SquareWindowApproximation

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def bodySharpScalarLiftLinear (B : TwoLayerBody) :
    PlanarCurrentL2 (B.absorberThickness + B.plateThickness) →ₗ[ℂ] ScalarBodyCurrentL2 B where
  toFun q := ⟨slabScalarLift (squareApertureWindow B.aperture) (squareApertureWindow_memLp B.aperture) (q : HeightL2), by
    filter_upwards [slabScalarLift_coe (squareApertureWindow B.aperture) (squareApertureWindow_memLp B.aperture) (q : HeightL2),
      slabHeight_quasiMeasurePreserving.ae q.property,
      slabHeight_quasiMeasurePreserving.ae (volume.ae_ne (0 : ℝ)),
      slabHeight_quasiMeasurePreserving.ae (volume.ae_ne (B.absorberThickness + B.plateThickness))] with x hx hq hz0 hzH
    intro hn
    rw [hx]
    change squareApertureWindow B.aperture (slabHorizontalCoordinate x) * (q : HeightL2) (x 2) = 0
    by_cases hhor : slabHorizontalCoordinate x ∈ horizontalSquareAperture B.aperture
    · by_cases hz : x 2 ∈ Icc 0 (B.absorberThickness + B.plateThickness)
      · exact False.elim (hn ⟨(horizontalSquareAperture_physical _ _).mp hhor,
          lt_of_le_of_ne hz.1 (Ne.symm hz0), lt_of_le_of_ne hz.2 hzH⟩)
      · rw [hq hz, mul_zero]
    · simp [squareApertureWindow, indicator_of_notMem hhor]⟩
  map_add' q r := Subtype.ext (map_add (slabScalarLift (squareApertureWindow B.aperture) (squareApertureWindow_memLp B.aperture)) _ _)
  map_smul' a q := Subtype.ext (map_smul (slabScalarLift (squareApertureWindow B.aperture) (squareApertureWindow_memLp B.aperture)) a _)

def bodySharpScalarLift (B : TwoLayerBody) :
    PlanarCurrentL2 (B.absorberThickness + B.plateThickness) →L[ℂ] ScalarBodyCurrentL2 B :=
  (bodySharpScalarLiftLinear B).mkContinuous
    ‖(squareApertureWindow_memLp B.aperture).toLp (squareApertureWindow B.aperture)‖ fun q =>
      (slabScalarLift_norm _ _ (q : HeightL2)).le

theorem bodySharpScalarLift_coe (B : TwoLayerBody)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    (bodySharpScalarLift B q : ScalarVolumeL2) =ᵐ[volume]
      slabSeparatedFunction (squareApertureWindow B.aperture) (q : HeightL2) :=
  slabScalarLift_coe _ _ _

theorem squareApertureWindow_L2_norm (R : ℝ) (hR : 0 ≤ R) :
    ‖(squareApertureWindow_memLp R).toLp (squareApertureWindow R)‖ = R := by
  have he := squareApertureWindow_integral_norm_sq R hR
  rw [memLp_two_integral_norm_sq _ (squareApertureWindow_memLp R)] at he
  nlinarith [norm_nonneg ((squareApertureWindow_memLp R).toLp (squareApertureWindow R))]

theorem bodySharpScalarLift_norm (B : TwoLayerBody)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    ‖bodySharpScalarLift B q‖ = B.aperture * ‖q‖ := by
  change ‖slabScalarLift (squareApertureWindow B.aperture) (squareApertureWindow_memLp B.aperture) (q : HeightL2)‖ = _
  rw [slabScalarLift_norm, squareApertureWindow_L2_norm B.aperture B.aperture_pos.le]
  rfl

theorem normalizedIncidentDrive_eq_sharpLift (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    normalizedIncidentDrive k B σ = bodySharpScalarLift B
      (planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness) :=
  Subtype.ext (Lp.ext ((normalizedIncidentDrive_separated k B σ).trans (bodySharpScalarLift_coe B _).symm))

theorem bodySharpScalarLift_window_difference_norm (B : TwoLayerBody)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    ‖bodySharpScalarLift B q - bodyScaledScalarLift B w hw hwc hs q‖ =
      B.aperture * ‖((squareApertureWindow_memLp 1).sub
        (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp (squareApertureWindow 1 - w)‖ * ‖q‖ := by
  let J := bodySharpScalarLift B q
  let F := bodyScaledScalarLift B w hw hwc hs q
  let m := apertureWindowMismatch_memLp w hw hwc B.aperture B.aperture_pos
  have hid : ((J : ScalarVolumeL2) - (F : ScalarVolumeL2)) =
      slabScalarLift (apertureWindowMismatch w B.aperture) m (q : HeightL2) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (J : ScalarVolumeL2) (F : ScalarVolumeL2),
      bodySharpScalarLift_coe B q, bodySeparatedScalarLift_coe B _ _ _ q,
      slabScalarLift_coe (apertureWindowMismatch w B.aperture) m (q : HeightL2)] with x hd hj hf hm
    rw [hd]
    change (J : ScalarVolumeL2) x - (F : ScalarVolumeL2) x = _
    change (J : ScalarVolumeL2) x = _ at hj
    change (F : ScalarVolumeL2) x = _ at hf
    rw [hj, hf, hm]
    change _ = (squareApertureWindow B.aperture (slabHorizontalCoordinate x) -
      scaledApertureWindow w B.aperture (slabHorizontalCoordinate x)) * (q : HeightL2) (x 2)
    simp only [slabSeparatedFunction]
    ring
  change ‖((J : ScalarVolumeL2) - (F : ScalarVolumeL2))‖ = _
  rw [hid, slabScalarLift_norm, apertureWindowMismatch_L2_norm w hw hwc B.aperture B.aperture_pos]
  rfl

end OQ7Prescribed

