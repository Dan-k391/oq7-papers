import work.SlabL2Lift
import PrescribedExtinction.SlabPhysicalAperture

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

abbrev HeightSupportedL2 (L : ℝ) := SetSupportedL2 (E := ℂ) (volume : Measure ℝ) (Icc (-L) L)

instance heightSupportedL2_completeSpace (L : ℝ) : CompleteSpace (HeightSupportedL2 L) := by
  let : IsClosed (setSupportedL2 (E := ℂ) (volume : Measure ℝ) (Icc (-L) L) : Set HeightL2) :=
    setSupportedL2_isClosed volume (Icc (-L) L) measurableSet_Icc
  exact inferInstance

theorem slabPosition_norm_le_sum (x : ℂ) (z : ℝ) : ‖slabPosition x z‖ ≤ ‖x‖ + |z| := by
  have hs := slabPosition_norm_sq x z
  nlinarith [norm_nonneg (slabPosition x z), norm_nonneg x, abs_nonneg z, sq_abs z]

def slabSupportedAxisLiftLinear (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A L : ℝ) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u : ℂ) :
    HeightSupportedL2 L →ₗ[ℂ] SupportedVectorL2 (A + L) where
  toFun q := ⟨slabAxisLift w hw u (q : HeightL2), by
    change ∀ᵐ x : Position ∂volume, x ∉ Metric.closedBall 0 (A + L) →
      (slabAxisLift w hw u (q : HeightL2)) x = 0
    filter_upwards [slabAxisLift_coe w hw u (q : HeightL2),
      slabHeight_quasiMeasurePreserving.ae q.property] with x hx hq
    intro hxb
    rw [hx]
    by_cases hwx : slabHorizontalCoordinate x ∈ tsupport w
    · have hxn : ‖slabHorizontalCoordinate x‖ ≤ A := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hA hwx
      have hz : x 2 ∉ Icc (-L) L := by
        intro h
        apply hxb
        simp only [Metric.mem_closedBall, dist_zero_right]
        have hzn : |x 2| ≤ L := abs_le.mpr h
        have he := slabPosition_norm_le_sum (slabHorizontalCoordinate x) (x 2)
        rw [slabPosition_horizontal_height] at he
        linarith
      change (w (slabHorizontalCoordinate x) * (q : HeightL2) (x 2)) • _ = 0
      rw [hq hz, mul_zero, zero_smul]
    · change (w (slabHorizontalCoordinate x) * (q : HeightL2) (x 2)) • _ = 0
      rw [image_eq_zero_of_notMem_tsupport hwx, zero_mul, zero_smul]⟩
  map_add' q r := Subtype.ext (map_add (slabAxisLift w hw u) (q : HeightL2) (r : HeightL2))
  map_smul' z q := Subtype.ext (map_smul (slabAxisLift w hw u) z (q : HeightL2))

def slabSupportedAxisLift (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A L : ℝ) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u : ℂ) :
    HeightSupportedL2 L →L[ℂ] SupportedVectorL2 (A + L) :=
  (slabSupportedAxisLiftLinear w hw A L hA u).mkContinuous
    (‖axisEmbedding (slabPosition u 0)‖ * ‖hw.toLp w‖) fun q =>
      slabAxisLift_norm_le w hw u (q : HeightL2)

theorem slabSupportedAxisLift_coe (w : ℂ → ℂ) (hw : MemLp w 2 volume)
    (A L : ℝ) (hA : tsupport w ⊆ Metric.closedBall 0 A) (u : ℂ) (q : HeightSupportedL2 L) :
    (slabSupportedAxisLift w hw A L hA u q : VectorL2) =ᵐ[volume]
      fun x => slabSeparatedFunction w (q : HeightL2) x • complexify (slabPosition u 0) :=
  slabAxisLift_coe w hw u (q : HeightL2)

end OQ7Prescribed
