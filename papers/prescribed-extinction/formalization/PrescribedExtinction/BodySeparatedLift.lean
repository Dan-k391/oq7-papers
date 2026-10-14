import PrescribedExtinction.PlanarCurrentSpace
import PrescribedExtinction.SlabL2Lift

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def horizontalSquareAperture (R : ℝ) : Set ℂ :=
  {z | -R / 2 < z.re ∧ z.re < R / 2 ∧ -R / 2 < z.im ∧ z.im < R / 2}

theorem horizontalSquareAperture_physical (R : ℝ) (x : Position) :
    slabHorizontalCoordinate x ∈ horizontalSquareAperture R ↔ x ∈ squareAperture R := by
  simp [horizontalSquareAperture, squareAperture, slabHorizontalCoordinate]

def bodySeparatedScalarLiftLinear (B : TwoLayerBody) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (hs : tsupport w ⊆ horizontalSquareAperture B.aperture) :
    PlanarCurrentL2 (B.absorberThickness + B.plateThickness) →ₗ[ℂ] ScalarBodyCurrentL2 B where
  toFun q := ⟨slabScalarLift w hw (q : HeightL2), by
    change ∀ᵐ x : Position ∂volume, x ∉ B.domain → (slabScalarLift w hw (q : HeightL2)) x = 0
    filter_upwards [slabScalarLift_coe w hw (q : HeightL2), slabHeight_quasiMeasurePreserving.ae q.property,
      slabHeight_quasiMeasurePreserving.ae (volume.ae_ne (0 : ℝ)),
      slabHeight_quasiMeasurePreserving.ae (volume.ae_ne (B.absorberThickness + B.plateThickness))] with x hx hq hzero hend
    intro hn
    rw [hx]
    change w (slabHorizontalCoordinate x) * (q : HeightL2) (x 2) = 0
    by_cases hwx : slabHorizontalCoordinate x ∈ tsupport w
    · by_cases hz : x 2 ∈ Icc 0 (B.absorberThickness + B.plateThickness)
      · exfalso
        apply hn
        change x ∈ squareAperture B.aperture ∧ 0 < x 2 ∧ x 2 < B.absorberThickness + B.plateThickness
        exact ⟨(horizontalSquareAperture_physical _ _).mp (hs hwx),
          lt_of_le_of_ne hz.1 (Ne.symm hzero), lt_of_le_of_ne hz.2 hend⟩
      · rw [hq hz, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hwx, zero_mul]⟩
  map_add' q r := Subtype.ext (map_add (slabScalarLift w hw) (q : HeightL2) (r : HeightL2))
  map_smul' a q := Subtype.ext (map_smul (slabScalarLift w hw) a (q : HeightL2))

def bodySeparatedScalarLift (B : TwoLayerBody) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (hs : tsupport w ⊆ horizontalSquareAperture B.aperture) :
    PlanarCurrentL2 (B.absorberThickness + B.plateThickness) →L[ℂ] ScalarBodyCurrentL2 B :=
  (bodySeparatedScalarLiftLinear B w hw hs).mkContinuous ‖hw.toLp w‖ fun q =>
    (slabScalarLift_norm w hw (q : HeightL2)).le

theorem bodySeparatedScalarLift_coe (B : TwoLayerBody) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (hs : tsupport w ⊆ horizontalSquareAperture B.aperture)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    (bodySeparatedScalarLift B w hw hs q : ScalarVolumeL2) =ᵐ[volume] slabSeparatedFunction w (q : HeightL2) :=
  slabScalarLift_coe w hw (q : HeightL2)

theorem bodySeparatedScalarLift_norm (B : TwoLayerBody) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (hs : tsupport w ⊆ horizontalSquareAperture B.aperture)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    ‖bodySeparatedScalarLift B w hw hs q‖ = ‖hw.toLp w‖ * ‖q‖ :=
  slabScalarLift_norm w hw (q : HeightL2)

end OQ7Prescribed

