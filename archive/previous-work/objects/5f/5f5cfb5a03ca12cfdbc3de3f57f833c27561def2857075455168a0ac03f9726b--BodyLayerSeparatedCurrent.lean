import work.BodySeparatedLift
import PrescribedExtinction.PlanarLayerKernel

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem electricVolumeField_add_ae (k : ℝ) (p q : CompactPolarization) :
    electricVolumeField k (p.add q) =ᵐ[volume] fun x => electricVolumeField k p x + electricVolumeField k q x := by
  have he : (p.add q).memLp.toLp (p.add q).current = p.memLp.toLp p.current + q.memLp.toLp q.current := by
    apply Lp.ext
    filter_upwards [(p.add q).memLp.coeFn_toLp, p.memLp.coeFn_toLp, q.memLp.coeFn_toLp,
      Lp.coeFn_add (p.memLp.toLp p.current) (q.memLp.toLp q.current)] with x hs hp hq ha
    rw [hs, ha]
    change p.current x + q.current x = (p.memLp.toLp p.current) x + (q.memLp.toLp q.current) x
    rw [hp, hq]
  filter_upwards [Lp.coeFn_add (staticFourierOperator (p.memLp.toLp p.current))
    (staticFourierOperator (q.memLp.toLp q.current))] with x hx
  simp only [electricVolumeField, he, map_add, remainderPotential_add]
  rw [hx]
  simp only [Pi.add_apply]
  abel

def bodyLayerSeparatedPolarization (B : TwoLayerBody) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (hs : tsupport w ⊆ horizontalSquareAperture B.aperture) (θ : ℝ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) : CompactPolarization :=
  bodyCurrentPolarization B (activeInjection B (basisR 0) (rotatedAxis θ) (bodySeparatedScalarLift B w hw hs q))

theorem bodyLayerSeparatedPolarization_current_ae (B : TwoLayerBody) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (hs : tsupport w ⊆ horizontalSquareAperture B.aperture) (θ : ℝ)
    (q : PlanarCurrentL2 (B.absorberThickness + B.plateThickness)) :
    (bodyLayerSeparatedPolarization B w hw hs θ q).current =ᵐ[volume] fun x =>
      w (slabHorizontalCoordinate x) •
        (((planarLayerAxisMap (B.absorberThickness + B.plateThickness) B.absorberThickness 1 (Real.cos θ) q : HeightL2) (x 2)) • basisC 0 +
          ((planarLayerAxisMap (B.absorberThickness + B.plateThickness) B.absorberThickness 0 (Real.sin θ) q : HeightL2) (x 2)) • basisC 1) := by
  filter_upwards [bodyCurrentPolarization_current_ae B (activeInjection B (basisR 0) (rotatedAxis θ)
      (bodySeparatedScalarLift B w hw hs q)),
    activeInjection_coe B (basisR 0) (rotatedAxis θ) (bodySeparatedScalarLift B w hw hs q),
    bodySeparatedScalarLift_coe B w hw hs q,
    slabHeight_quasiMeasurePreserving.ae (planarActiveAxisMaps_vector_current _ B.absorberThickness θ q)] with x hp hi hq hv
  unfold bodyLayerSeparatedPolarization
  rw [hp, hi, hv]
  by_cases hx : x 2 < B.absorberThickness <;> simp only [hx, ite_true, ite_false]
  all_goals rw [hq]
  all_goals change (w (slabHorizontalCoordinate x) * (q : HeightL2) (x 2)) • _ = _
  all_goals rw [smul_smul]

end OQ7Prescribed
