import PrescribedExtinction.SlabSeparatedL2
import PrescribedExtinction.ActiveCurrentSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory MeasureTheory.Measure

abbrev HeightL2 := Lp ℂ 2 (volume : Measure ℝ)
abbrev ScalarVolumeL2 := Lp ℂ 2 (volume : Measure Position)

theorem slabHeight_quasiMeasurePreserving :
    QuasiMeasurePreserving (fun x : Position => x 2) volume volume := by
  have hp : QuasiMeasurePreserving (Prod.snd : ℂ × ℝ → ℝ) volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (quasiMeasurePreserving_snd (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℝ)))
  have hm : MeasurePreserving (fun x : Position => slabCoordinateEquiv.symm x)
      (volume : Measure Position) (volume : Measure (ℂ × ℝ)) := slabCoordinateEquiv_measurePreserving.symm
  have he := hp.comp hm.quasiMeasurePreserving
  have hid : (Prod.snd : ℂ × ℝ → ℝ) ∘ (fun x : Position => slabCoordinateEquiv.symm x) =
      fun x => x 2 := by
    funext x
    simp only [Function.comp_apply, slabCoordinateEquiv_symm_apply]
  rw [hid] at he
  exact he

def slabScalarLiftRaw (w : ℂ → ℂ) (hw : MemLp w 2 volume) (q : HeightL2) : ScalarVolumeL2 :=
  (slabSeparatedFunction_memLp_two w q hw (Lp.memLp q)).toLp (slabSeparatedFunction w q)

theorem slabScalarLiftRaw_coe (w : ℂ → ℂ) (hw : MemLp w 2 volume) (q : HeightL2) :
    slabScalarLiftRaw w hw q =ᵐ[volume] slabSeparatedFunction w q :=
  (slabSeparatedFunction_memLp_two w q hw (Lp.memLp q)).coeFn_toLp

theorem slabScalarLiftRaw_norm (w : ℂ → ℂ) (hw : MemLp w 2 volume) (q : HeightL2) :
    ‖slabScalarLiftRaw w hw q‖ = ‖hw.toLp w‖ * ‖q‖ := by
  rw [slabScalarLiftRaw, slabSeparatedFunction_L2_norm w q hw (Lp.memLp q), Lp.toLp_coeFn]

def slabScalarLiftLinear (w : ℂ → ℂ) (hw : MemLp w 2 volume) : HeightL2 →ₗ[ℂ] ScalarVolumeL2 where
  toFun := slabScalarLiftRaw w hw
  map_add' q r := by
    apply Lp.ext
    filter_upwards [slabScalarLiftRaw_coe w hw (q + r), slabScalarLiftRaw_coe w hw q,
      slabScalarLiftRaw_coe w hw r, Lp.coeFn_add (slabScalarLiftRaw w hw q) (slabScalarLiftRaw w hw r),
      slabHeight_quasiMeasurePreserving.ae (Lp.coeFn_add q r)] with x ha hq hr hb hh
    rw [ha, hb]
    change slabSeparatedFunction w ((q + r : HeightL2) : ℝ → ℂ) x =
      slabScalarLiftRaw w hw q x + slabScalarLiftRaw w hw r x
    rw [hq, hr]
    change w (slabHorizontalCoordinate x) * ((q + r) (x 2)) =
      w (slabHorizontalCoordinate x) * q (x 2) + w (slabHorizontalCoordinate x) * r (x 2)
    rw [hh]
    exact mul_add _ _ _
  map_smul' z q := by
    apply Lp.ext
    filter_upwards [slabScalarLiftRaw_coe w hw (z • q), slabScalarLiftRaw_coe w hw q,
      Lp.coeFn_smul z (slabScalarLiftRaw w hw q),
      slabHeight_quasiMeasurePreserving.ae (Lp.coeFn_smul z q)] with x ha hq hb hh
    change slabScalarLiftRaw w hw (z • q) x = (z • slabScalarLiftRaw w hw q) x
    rw [ha, hb]
    change slabSeparatedFunction w ((z • q : HeightL2) : ℝ → ℂ) x = z * slabScalarLiftRaw w hw q x
    rw [hq]
    change w (slabHorizontalCoordinate x) * ((z • q) (x 2)) = z * (w (slabHorizontalCoordinate x) * q (x 2))
    rw [hh]
    change w (slabHorizontalCoordinate x) * (z * q (x 2)) = _
    ring

def slabScalarLift (w : ℂ → ℂ) (hw : MemLp w 2 volume) : HeightL2 →L[ℂ] ScalarVolumeL2 :=
  (slabScalarLiftLinear w hw).mkContinuous ‖hw.toLp w‖ fun q =>
    (slabScalarLiftRaw_norm w hw q).le

theorem slabScalarLift_coe (w : ℂ → ℂ) (hw : MemLp w 2 volume) (q : HeightL2) :
    slabScalarLift w hw q =ᵐ[volume] slabSeparatedFunction w q := slabScalarLiftRaw_coe w hw q

theorem slabScalarLift_norm (w : ℂ → ℂ) (hw : MemLp w 2 volume) (q : HeightL2) :
    ‖slabScalarLift w hw q‖ = ‖hw.toLp w‖ * ‖q‖ := slabScalarLiftRaw_norm w hw q

def slabAxisLift (w : ℂ → ℂ) (hw : MemLp w 2 volume) (u : ℂ) : HeightL2 →L[ℂ] VectorL2 :=
  (axisEmbedding (slabPosition u 0)).compLpL 2 volume ∘L slabScalarLift w hw

theorem slabAxisLift_coe (w : ℂ → ℂ) (hw : MemLp w 2 volume) (u : ℂ) (q : HeightL2) :
    slabAxisLift w hw u q =ᵐ[volume]
      fun x => slabSeparatedFunction w q x • complexify (slabPosition u 0) := by
  filter_upwards [(axisEmbedding (slabPosition u 0)).coeFn_compLp (slabScalarLift w hw q),
    slabScalarLift_coe w hw q] with x ha hb
  change ((axisEmbedding (slabPosition u 0)).compLp (slabScalarLift w hw q)) x = _
  rw [ha, hb, axisEmbedding_apply]

theorem slabAxisLift_norm_le (w : ℂ → ℂ) (hw : MemLp w 2 volume) (u : ℂ) (q : HeightL2) :
    ‖slabAxisLift w hw u q‖ ≤ ‖axisEmbedding (slabPosition u 0)‖ * ‖hw.toLp w‖ * ‖q‖ := by
  have he := (axisEmbedding (slabPosition u 0)).norm_compLp_le (slabScalarLift w hw q)
  rw [slabScalarLift_norm, ← mul_assoc] at he
  exact he

end OQ7Prescribed
