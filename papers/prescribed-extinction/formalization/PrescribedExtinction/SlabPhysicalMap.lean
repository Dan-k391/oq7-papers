import PrescribedExtinction.SlabSupportedLift
import PrescribedExtinction.SlabObservationRegion

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabPhysicalMap (k : ℝ) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M r L : ℝ) (hAM : 0 ≤ A + M) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u v : ℂ) :
    HeightSupportedL2 M →L[ℂ] ScalarVolumeL2 :=
  (setSupportedL2 (E := ℂ) volume (slabObservationRegion r L)).subtypeL ∘L
    setRestrictionCLM volume (slabObservationRegion r L) (slabObservationRegion_measurable r L) ∘L
      (axisEmbedding (slabPosition v 0)).adjoint.compLpL 2 volume ∘L
        (supportedVectorL2 (A + M)).subtypeL ∘L
          compactOutgoingOperator k (A + M) hAM ∘L slabSupportedAxisLift w hw A M hA u

def slabLiftPolarization (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M : ℝ) (hAM : 0 ≤ A + M) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u : ℂ)
    (q : HeightSupportedL2 M) : CompactPolarization :=
  supportedPolarization (A + M) hAM (slabSupportedAxisLift w hw A M hA u q)

theorem slabLiftPolarization_current_ae (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M : ℝ) (hAM : 0 ≤ A + M) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u : ℂ)
    (q : HeightSupportedL2 M) : (slabLiftPolarization w hw A M hAM hA u q).current =ᵐ[volume]
      fun x => slabSeparatedFunction w (q : HeightL2) x • complexify (slabPosition u 0) :=
  (supportedPolarization_current_ae _ _ _).trans (slabSupportedAxisLift_coe w hw A M hA u q)

theorem slabPhysicalMap_coe (k : ℝ) (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A M r L : ℝ) (hAM : 0 ≤ A + M) (hL : 0 ≤ L) (hObs : r + L ≤ A + M)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) (u v : ℂ) (q : HeightSupportedL2 M) :
    slabPhysicalMap k w hw A M r L hAM hA u v q =ᵐ[volume]
      (slabObservationRegion r L).indicator (fun x => axisCoupling (slabPosition v 0)
        (electricVolumeField k (slabLiftPolarization w hw A M hAM hA u q) x)) := by
  let f := slabSupportedAxisLift w hw A M hA u q
  let T := compactOutgoingOperator k (A + M) hAM f
  let ap := (axisEmbedding (slabPosition v 0)).adjoint
  let g := ap.compLp (T : VectorL2)
  have hBall := slabObservationRegion_subset_ball r L (A + M) hL hObs
  filter_upwards [indicatorL2_coe volume (slabObservationRegion r L)
    (slabObservationRegion_measurable r L) g, ap.coeFn_compLp (T : VectorL2),
    compactOutgoingOperator_coe k (A + M) hAM f] with x hi ha ht
  change indicatorL2 volume (slabObservationRegion r L) (slabObservationRegion_measurable r L) g x = _
  rw [hi]
  by_cases hx : x ∈ slabObservationRegion r L
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    change g x = _
    rw [ha, ht, indicator_of_mem (hBall hx)]
    change (axisEmbedding (slabPosition v 0)).adjoint (staticFourierOperator (f : VectorL2) x +
      remainderPotential k (supportedPolarization (A + M) hAM f) x) = _
    rw [axisEmbedding_adjoint_apply]
    simp only [slabLiftPolarization, electricVolumeField, supportedPolarization_toLp]
    rfl
  · simp only [indicator_of_notMem hx]

end OQ7Prescribed
