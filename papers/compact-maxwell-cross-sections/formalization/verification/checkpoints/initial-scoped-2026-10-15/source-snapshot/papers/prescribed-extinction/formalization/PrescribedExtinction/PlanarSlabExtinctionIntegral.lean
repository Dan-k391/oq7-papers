import PrescribedExtinction.PlanarSlabResponseIdentification

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Classical

theorem planarIncidentPhase_plus_star (k z : ℝ) :
    (starRingEnd ℂ) (planarIncidentPhase k .plus z) = apertureOscillation (-k) z := by
  rw [planarIncidentPhase_plus]
  unfold apertureOscillation
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem slabCoupledCurrent_plus_drive_inner (k : ℝ) (A W : OQ7.HomogeneousLayer)
    (θ : ℝ) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) :
    inner ℂ (planarNormalizedDrive k .plus (A.width + W.width) A.width)
      (slabCoupledCurrent k A W θ .plus hpA hpW hdA hdW) =
      ∫ z in A.width..(A.width + W.width), apertureOscillation (-k) z *
        (slabCoupledPlate k A W θ .plus hpW).current z := by
  let L := A.width + W.width
  let F := slabCoupledAbsorber k A W θ .plus hpA
  let G := slabCoupledPlate k A W θ .plus hpW
  let q := slabCoupledCurrent k A W θ .plus hpA hpW hdA hdW
  let g := planarNormalizedDrive k .plus L A.width
  have hpoint : (fun z => inner ℂ ((g : HeightL2) z) ((q : HeightL2) z)) =ᵐ[volume]
      (Ioc A.width L).indicator (fun z => apertureOscillation (-k) z * G.current z) := by
    filter_upwards [slabCoupledCurrent_coe k A W θ .plus hpA hpW hdA hdW,
      planarNormalizedDrive_coe k .plus L A.width, volume.ae_ne A.width] with z hq hg hzh
    change (q : HeightL2) z = (Ioc 0 A.width).indicator (fun t => (OQ7.relativePermittivity A - 1) * F.electric t) z +
      (Ioc A.width L).indicator (fun t => (OQ7.relativePermittivity W - 1) * G.electric t) z at hq
    change (g : HeightL2) z = _ at hg
    rw [hg, hq]
    by_cases hzw : z ∈ Ioc A.width L
    · have hzL : z ∈ Icc 0 L := ⟨hdA.trans hzw.1.le, hzw.2⟩
      have hzA : ¬ z < A.width := not_lt.mpr hzw.1.le
      have hza : z ∉ Ioc 0 A.width := fun hm => (not_le_of_gt hzw.1) hm.2
      simp only [indicator_of_mem hzw, indicator_of_mem hzL, indicator_of_notMem hza,
        if_neg hzA, zero_add, RCLike.inner_apply, planarIncidentPhase_plus_star]
      change ((OQ7.relativePermittivity W - 1) * G.electric z) * apertureOscillation (-k) z =
        apertureOscillation (-k) z * G.current z
      change ((OQ7.relativePermittivity W - 1) * G.electric z) * apertureOscillation (-k) z =
        apertureOscillation (-k) z * (slabCoupledPlate k A W θ .plus hpW).current z
      rw [slabCoupledPlate_constitutive]
      change ((OQ7.relativePermittivity W - 1) * G.electric z) * apertureOscillation (-k) z =
        apertureOscillation (-k) z * ((OQ7.relativePermittivity W - 1) * G.electric z)
      ring
    · rw [indicator_of_notMem hzw, indicator_of_notMem hzw, add_zero]
      by_cases hzA : z < A.width
      · by_cases hzL : z ∈ Icc 0 L <;>
          simp [indicator_of_mem, indicator_of_notMem, hzL, hzA]
      · have hza : z ∉ Ioc 0 A.width := fun hm => hzA (lt_of_le_of_ne hm.2 hzh)
        rw [indicator_of_notMem hza, inner_zero_right]
  change inner ℂ (g : HeightL2) (q : HeightL2) = _
  rw [L2.inner_def, integral_congr_ae hpoint, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (show A.width ≤ L by dsimp [L]; linarith)]

theorem slabCoupledPlate_plus_weighted_moment (k : ℝ) (hk : 0 < k)
    (A W : OQ7.HomogeneousLayer) (θ : ℝ) (hpW : 1 ≤ W.p)
    (hqW : 0 ≤ W.q) (hdW : 0 ≤ W.width) :
    (Complex.I * (k : ℂ)) * (∫ z in A.width..(A.width + W.width), apertureOscillation (-k) z *
      (slabCoupledPlate k A W θ .plus hpW).current z) =
    2 * slabPlusPlateAmplitude k A W θ *
      (apertureOscillation (-k) (A.width + W.width) * dielectricSlabTransmission k W.p W.q W.width -
        apertureOscillation (-k) A.width) := by
  let G := slabCoupledPlate k A W θ .plus hpW
  have hm := (planarWaveMoments_boundary k A.width (A.width + W.width) (by linarith)
    G.electric G.magnetic G.current G.electric_continuous G.magnetic_continuous G.current_continuous
    G.electric_derivative G.magnetic_derivative).1
  have hb := dielectricSlabLeftAt_boundary k hk W.p W.q A.width (A.width + W.width) hpW hqW (by linarith)
  have hd : A.width + W.width - A.width = W.width := by ring
  have hbG : G.magnetic (A.width + W.width) + G.electric (A.width + W.width) =
      2 * slabPlusPlateAmplitude k A W θ * dielectricSlabTransmission k W.p W.q W.width := by
    dsimp only [G, slabCoupledPlate, PlanarLayerField.add, PlanarLayerField.const_mul,
      slabPlateLeftAmplitude, slabPlateRightAmplitude]
    simp only [zero_mul, add_zero, hb.2.2.1, hb.2.2.2, hd]
    ring
  have haG : G.magnetic A.width + G.electric A.width = 2 * slabPlusPlateAmplitude k A W θ := by
    dsimp only [G, slabCoupledPlate, PlanarLayerField.add, PlanarLayerField.const_mul,
      slabPlateLeftAmplitude, slabPlateRightAmplitude]
    simp only [zero_mul, add_zero, hb.1, hb.2.1, hd]
    ring
  rw [hbG, haG] at hm
  change (Complex.I * (k : ℂ)) * _ = _ at hm
  rw [hm]
  ring

end OQ7Prescribed
