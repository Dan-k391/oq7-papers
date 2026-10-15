import PrescribedExtinction.BodyApertureResidual
import PrescribedExtinction.PlanarResponse

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarInverseMaterial_coe (L h : ℝ) (α β : ℂ) (q : PlanarCurrentL2 L) :
    (planarInverseMaterial L h α β q : HeightL2) =ᵐ[volume]
      fun z => if z < h then α⁻¹ * (q : HeightL2) z else β⁻¹ * (q : HeightL2) z :=
  twoPieceSupportedOperator_coe _ _ _ _ _ _ _

theorem bodyScaledScalarLift_inverse_material (B : TwoLayerBody) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (α β : ℂ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    activeInverseMaterial B α β (bodyScaledScalarLift B w hw hwc hs q) =
      bodyScaledScalarLift B w hw hwc hs (planarInverseMaterial _ B.absorberThickness α β q) := by
  let F := bodyScaledScalarLift B w hw hwc hs
  let M := planarInverseMaterial (B.absorberThickness + B.plateThickness) B.absorberThickness α β q
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [activeInverseMaterial_coe B α β (F q),
    bodySeparatedScalarLift_coe B _ _ _ q, bodySeparatedScalarLift_coe B _ _ _ M,
    slabHeight_quasiMeasurePreserving.ae (planarInverseMaterial_coe _ B.absorberThickness α β q)] with x hm hq hM hp
  change (activeInverseMaterial B α β (F q) : ScalarVolumeL2) x = (F M : ScalarVolumeL2) x
  change (F q : ScalarVolumeL2) x = _ at hq
  change (F M : ScalarVolumeL2) x = _ at hM
  change (M : HeightL2) (x 2) = _ at hp
  rw [hm, hq, hM]
  change (if x 2 < B.absorberThickness then α⁻¹ * (scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (q : HeightL2) (x 2))
    else β⁻¹ * (scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (q : HeightL2) (x 2))) =
      scaledApertureWindow w B.aperture (slabHorizontalCoordinate x) * (M : HeightL2) (x 2)
  rw [hp]
  by_cases hx : x 2 < B.absorberThickness <;> simp only [hx, ite_true, ite_false] <;> ring

theorem bodyScaledScalarLift_material_residual_identity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) (θ : ℝ) (α β : ℂ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    activeMaterialOperator k B (basisR 0) (rotatedAxis θ) α β (bodyScaledScalarLift B w hw hwc hs q) -
      bodyScaledScalarLift B w hw hwc hs
        (planarActiveMaterialOperator k hk _ (bodyHeight_pos B).le B.absorberThickness θ α β q) =
      activeProjection B (basisR 0) (rotatedAxis θ) (bodyOutgoingOperator k B
        (activeInjection B (basisR 0) (rotatedAxis θ) (bodyScaledScalarLift B w hw hwc hs q))) -
          bodyScaledScalarLift B w hw hwc hs
            (planarActiveOutgoing k hk _ (bodyHeight_pos B).le B.absorberThickness θ q) := by
  simp only [activeMaterialOperator, planarActiveMaterialOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, bodyScaledScalarLift_inverse_material]
  abel

end OQ7Prescribed

