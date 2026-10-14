import PrescribedExtinction.PlanarHeightMap
import PrescribedExtinction.SlabPhysicalMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabPlanarMap (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (M r L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (u v : ℂ) :
    HeightSupportedL2 M →L[ℂ] ScalarVolumeL2 :=
  (k ^ 2 * inner ℝ u v : ℝ) •
    ((setSupportedL2 (E := ℂ) volume (slabObservationRegion r L)).subtypeL ∘L
      setRestrictionCLM volume (slabObservationRegion r L) (slabObservationRegion_measurable r L) ∘L
        slabScalarLift w hw ∘L planarHeightMap k hk M L hM hL)

theorem slabPlanarMap_coe (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (M r L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (u v : ℂ) (q : HeightSupportedL2 M) :
    slabPlanarMap k hk w hw M r L hM hL u v q =ᵐ[volume]
      (slabObservationRegion r L).indicator (fun x =>
        planarSlabTransverse k w (q : HeightL2) (slabHorizontalCoordinate x) (x 2) u v) := by
  let c := (k ^ 2 * inner ℝ u v : ℝ)
  let H := planarHeightMap k hk M L hM hL q
  let g := slabScalarLift w hw H
  let out := indicatorL2 volume (slabObservationRegion r L) (slabObservationRegion_measurable r L) g
  filter_upwards [Lp.coeFn_smul c out, indicatorL2_coe volume (slabObservationRegion r L)
    (slabObservationRegion_measurable r L) g, slabScalarLift_coe w hw H,
    slabHeight_quasiMeasurePreserving.ae (planarHeightMap_coe k hk M L hM hL q)] with x hs hi hg hh
  change (c • out) x = _
  rw [hs]
  change c • out x = _
  rw [hi]
  by_cases hx : x ∈ slabObservationRegion r L
  · rw [indicator_of_mem hx, indicator_of_mem hx, hg]
    change c • (w (slabHorizontalCoordinate x) * H (x 2)) = _
    rw [hh, indicator_of_mem ((slabObservationRegion_mem_iff r L x).mp hx).2,
      planarSlabTransverse_factorization]
  · simp only [indicator_of_notMem hx, smul_zero]

def slabApertureDifference (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M r L : ℝ) (hAM : 0 ≤ A + M) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (u v : ℂ) :
    HeightSupportedL2 M →L[ℂ] ScalarVolumeL2 :=
  slabPhysicalMap k w hw A M r L hAM hA u v - slabPlanarMap k hk w hw M r L hM hL u v

theorem slabApertureDifference_coe (k : ℝ) (hk : 0 < k) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M r L : ℝ) (hAM : 0 ≤ A + M) (hM : 0 ≤ M) (hL : 0 ≤ L) (hObs : r + L ≤ A + M)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (u v : ℂ) (q : HeightSupportedL2 M) :
    slabApertureDifference k hk w hw A M r L hAM hM hL hA u v q =ᵐ[volume]
      (slabObservationRegion r L).indicator (fun x =>
        axisCoupling (slabPosition v 0) (electricVolumeField k (slabLiftPolarization w hw A M hAM hA u q) x) -
          planarSlabTransverse k w (q : HeightL2) (slabHorizontalCoordinate x) (x 2) u v) := by
  let p := slabPhysicalMap k w hw A M r L hAM hA u v q
  let t := slabPlanarMap k hk w hw M r L hM hL u v q
  filter_upwards [Lp.coeFn_sub p t,
    slabPhysicalMap_coe k w hw A M r L hAM hL hObs hA u v q,
    slabPlanarMap_coe k hk w hw M r L hM hL u v q] with x hs hp ht
  change (p - t) x = _
  rw [hs]
  change p x - t x = _
  rw [hp, ht]
  by_cases hx : x ∈ slabObservationRegion r L
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, sub_self]

end OQ7Prescribed
