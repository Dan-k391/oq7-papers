import PrescribedExtinction.BodyResponseResidual
import PrescribedExtinction.SquareApertureWindow

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def apertureWindowMismatch (w : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  squareApertureWindow R - scaledApertureWindow w R

theorem apertureWindowMismatch_memLp (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) (R : ℝ) (hR : 0 < R) :
    MemLp (apertureWindowMismatch w R) 2 volume :=
  (squareApertureWindow_memLp R).sub ((scaledApertureWindow_contDiff w hw R).continuous.memLp_of_hasCompactSupport
    (scaledApertureWindow_hasCompactSupport w hwc R hR.ne'))

theorem apertureWindowMismatch_L2_norm (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) (R : ℝ) (hR : 0 < R) :
    ‖(apertureWindowMismatch_memLp w hw hwc R hR).toLp (apertureWindowMismatch w R)‖ =
      R * ‖((squareApertureWindow_memLp 1).sub
        (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp (squareApertureWindow 1 - w)‖ := by
  have hid : apertureWindowMismatch w R = scaledApertureWindow (squareApertureWindow 1 - w) R := by
    rw [apertureWindowMismatch, squareApertureWindow_scaled R hR]
    rfl
  have he := scaledApertureWindow_integral_norm_sq (squareApertureWindow 1 - w) R hR
  rw [← hid] at he
  rw [memLp_two_integral_norm_sq _ (apertureWindowMismatch_memLp w hw hwc R hR),
    memLp_two_integral_norm_sq _ ((squareApertureWindow_memLp 1).sub
      (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc))] at he
  have hn := norm_nonneg ((apertureWindowMismatch_memLp w hw hwc R hR).toLp (apertureWindowMismatch w R))
  have hr := mul_nonneg hR.le (norm_nonneg (((squareApertureWindow_memLp 1).sub
    (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp (squareApertureWindow 1 - w)))
  nlinarith

theorem normalizedIncidentDrive_separated (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    (normalizedIncidentDrive k B σ : ScalarVolumeL2) =ᵐ[volume]
      slabSeparatedFunction (squareApertureWindow B.aperture)
        (planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness : HeightL2) := by
  filter_upwards [normalizedIncidentDrive_coe k B σ,
    slabHeight_quasiMeasurePreserving.ae (planarNormalizedDrive_coe k σ (B.absorberThickness + B.plateThickness) B.absorberThickness),
    slabHeight_quasiMeasurePreserving.ae (volume.ae_ne (0 : ℝ)),
    slabHeight_quasiMeasurePreserving.ae (volume.ae_ne (B.absorberThickness + B.plateThickness))] with x hi hp hz0 hzH
  rw [hi]
  change _ = squareApertureWindow B.aperture (slabHorizontalCoordinate x) * _
  rw [hp]
  have hphase : planePhase k σ x = planarIncidentPhase k σ (x 2) := by
    rw [← slabPosition_horizontal_height x]
    exact (planarIncidentPhase_physical k σ _ _).symm
  by_cases hhor : slabHorizontalCoordinate x ∈ horizontalSquareAperture B.aperture
  · have hsquare := (horizontalSquareAperture_physical _ _).mp hhor
    have hwindow : squareApertureWindow B.aperture (slabHorizontalCoordinate x) = 1 := indicator_of_mem hhor _
    rw [hwindow, one_mul]
    by_cases hh : x 2 ∈ Icc 0 (B.absorberThickness + B.plateThickness)
    · have hbody : x ∈ B.domain := ⟨hsquare, lt_of_le_of_ne hh.1 (Ne.symm hz0), lt_of_le_of_ne hh.2 hzH⟩
      simp only [indicator_of_mem hbody, indicator_of_mem hh, hphase]
    · have hbody : x ∉ B.domain := fun hx => hh ⟨hx.2.1.le, hx.2.2.le⟩
      simp [indicator_of_notMem hbody, indicator_of_notMem hh]
  · have hbody : x ∉ B.domain := fun hx => hhor ((horizontalSquareAperture_physical _ _).mpr hx.1)
    have hwindow : squareApertureWindow B.aperture (slabHorizontalCoordinate x) = 0 := indicator_of_notMem hhor _
    simp [indicator_of_notMem hbody, hwindow]

theorem normalizedIncidentDrive_window_mismatch_norm (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hs : tsupport w ⊆ horizontalSquareAperture 1) :
    ‖normalizedIncidentDrive k B σ - bodyScaledScalarLift B w hw hwc hs
      (planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness)‖ =
      B.aperture * ‖((squareApertureWindow_memLp 1).sub
        (hw.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwc)).toLp (squareApertureWindow 1 - w)‖ *
          ‖planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness‖ := by
  let g := planarNormalizedDrive k σ (B.absorberThickness + B.plateThickness) B.absorberThickness
  let F := bodyScaledScalarLift B w hw hwc hs g
  let m := apertureWindowMismatch_memLp w hw hwc B.aperture B.aperture_pos
  have hid : ((normalizedIncidentDrive k B σ : ScalarVolumeL2) - (F : ScalarVolumeL2)) =
      slabScalarLift (apertureWindowMismatch w B.aperture) m (g : HeightL2) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (normalizedIncidentDrive k B σ : ScalarVolumeL2) (F : ScalarVolumeL2),
      normalizedIncidentDrive_separated k B σ, bodySeparatedScalarLift_coe B _ _ _ g,
      slabScalarLift_coe (apertureWindowMismatch w B.aperture) m (g : HeightL2)] with x hd hi hf hm
    rw [hd]
    change (normalizedIncidentDrive k B σ : ScalarVolumeL2) x - (F : ScalarVolumeL2) x = _
    change (F : ScalarVolumeL2) x = _ at hf
    rw [hi, hf, hm]
    change _ = (squareApertureWindow B.aperture (slabHorizontalCoordinate x) -
      scaledApertureWindow w B.aperture (slabHorizontalCoordinate x)) * (g : HeightL2) (x 2)
    simp only [slabSeparatedFunction]
    ring
  change ‖((normalizedIncidentDrive k B σ : ScalarVolumeL2) - (F : ScalarVolumeL2))‖ = _
  rw [hid, slabScalarLift_norm, apertureWindowMismatch_L2_norm w hw hwc B.aperture B.aperture_pos]
  rfl

end OQ7Prescribed
