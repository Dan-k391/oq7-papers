import PrescribedExtinction.SlabPhysicalAperture
import PrescribedExtinction.SlabProductResidual

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabObservationRegion (r L : ℝ) : Set Position :=
  slabCoordinateHomeomorph '' slabProductRegion r L

theorem slabObservationRegion_compact (r L : ℝ) : IsCompact (slabObservationRegion r L) :=
  ((isCompact_closedBall (0 : ℂ) r).prod isCompact_Icc).image slabCoordinateHomeomorph.continuous

theorem slabObservationRegion_measurable (r L : ℝ) : MeasurableSet (slabObservationRegion r L) :=
  (slabObservationRegion_compact r L).measurableSet

theorem slabObservationRegion_mem_iff (r L : ℝ) (x : Position) :
    x ∈ slabObservationRegion r L ↔ ‖slabHorizontalCoordinate x‖ ≤ r ∧ x 2 ∈ Icc 0 L := by
  change x ∈ slabCoordinateEquiv '' slabProductRegion r L ↔ _
  rw [slabCoordinateEquiv.image_eq_preimage_symm]
  simp only [mem_preimage, slabCoordinateEquiv_symm_apply, slabProductRegion, mem_prod,
    Metric.mem_closedBall, dist_zero_right]

theorem slabObservationRegion_preimage (r L : ℝ) :
    slabCoordinateEquiv ⁻¹' slabObservationRegion r L = slabProductRegion r L := by
  change slabCoordinateEquiv ⁻¹' (slabCoordinateEquiv '' slabProductRegion r L) = _
  exact preimage_image_eq _ slabCoordinateEquiv.injective

theorem slabObservationRegion_volume_real (r L : ℝ) (hr : 0 ≤ r) (hL : 0 ≤ L) :
    (volume (slabObservationRegion r L)).toReal = r ^ 2 * Real.pi * L := by
  have he := slabCoordinateEquiv_measurePreserving.measure_preimage
    (slabObservationRegion_measurable r L).nullMeasurableSet
  rw [slabObservationRegion_preimage] at he
  rw [← he]
  exact slabProductRegion_volume_real r L hr hL

theorem slabObservationRegion_subset_ball (r L S : ℝ) (hL : 0 ≤ L) (hS : r + L ≤ S) :
    slabObservationRegion r L ⊆ Metric.closedBall 0 S := by
  intro x hx
  obtain ⟨hxr, hxz⟩ := (slabObservationRegion_mem_iff r L x).mp hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖x‖ ≤ ‖slabHorizontalCoordinate x‖ + |x 2| := by
    have hn := slabPosition_norm_sq (slabHorizontalCoordinate x) (x 2)
    rw [slabPosition_horizontal_height] at hn
    nlinarith [norm_nonneg x,
      norm_nonneg (slabHorizontalCoordinate x), abs_nonneg (x 2), sq_abs (x 2)]
  rw [abs_of_nonneg hxz.1] at hnorm
  linarith [hxz.2]

theorem integral_slabObservationRegion (r L : ℝ) (f : Position → ℝ) :
    (∫ x in slabObservationRegion r L, f x) =
      ∫ y in slabProductRegion r L, f (slabPosition y.1 y.2) := by
  rw [← integral_indicator (slabObservationRegion_measurable r L), integral_slabCoordinates,
    ← integral_indicator (slabProductRegion_measurable r L)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    have hm : slabPosition y.1 y.2 ∈ slabObservationRegion r L ↔ y ∈ slabProductRegion r L := by
      rw [← slabCoordinateEquiv_apply y]
      change y ∈ slabCoordinateEquiv ⁻¹' slabObservationRegion r L ↔ _
      rw [slabObservationRegion_preimage]
    by_cases hy : y ∈ slabProductRegion r L
    · simp only [indicator_of_mem hy, indicator_of_mem (hm.mpr hy)]
    · simp only [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hm.mp h))])

end OQ7Prescribed
