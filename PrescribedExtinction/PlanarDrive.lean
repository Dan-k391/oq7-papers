import PrescribedExtinction.PlanarCurrentSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def planarIncidentPhase (k : ℝ) (σ : Direction) (z : ℝ) : ℂ := apertureOscillation (σ.sign * k) z

theorem planarIncidentPhase_norm (k : ℝ) (σ : Direction) (z : ℝ) : ‖planarIncidentPhase k σ z‖ = 1 :=
  apertureOscillation_norm _ _

theorem planarIncidentPhase_physical (k : ℝ) (σ : Direction) (x : ℂ) (z : ℝ) :
    planarIncidentPhase k σ z = planePhase k σ (slabPosition x z) := by
  simp [planarIncidentPhase, apertureOscillation, planePhase, slabPosition, mul_assoc]

theorem planarIncidentPhase_memLp (k : ℝ) (σ : Direction) (L : ℝ) :
    MemLp ((Icc 0 L).indicator (planarIncidentPhase k σ)) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  have hc : Continuous (planarIncidentPhase k σ) := apertureOscillation_continuous _
  apply MemLp.of_bound (hc.aestronglyMeasurable.mono_measure Measure.restrict_le_self) 1
  exact ae_of_all _ fun z => (planarIncidentPhase_norm k σ z).le

def planarIncidentProfile (k : ℝ) (σ : Direction) (L : ℝ) : PlanarCurrentL2 L :=
  ⟨(planarIncidentPhase_memLp k σ L).toLp ((Icc 0 L).indicator (planarIncidentPhase k σ)), by
    change ∀ᵐ z : ℝ ∂volume, z ∉ Icc 0 L → _ = 0
    filter_upwards [(planarIncidentPhase_memLp k σ L).coeFn_toLp] with z hz
    intro hn
    rw [hz, indicator_of_notMem hn]⟩

theorem planarIncidentProfile_coe (k : ℝ) (σ : Direction) (L : ℝ) :
    (planarIncidentProfile k σ L : HeightL2) =ᵐ[volume] (Icc 0 L).indicator (planarIncidentPhase k σ) :=
  (planarIncidentPhase_memLp k σ L).coeFn_toLp

def planarNormalizedDrive (k : ℝ) (σ : Direction) (L h : ℝ) : PlanarCurrentL2 L :=
  planarIncidentProfile k σ L - supportedSliceCLM volume (Icc 0 L) (Iio h) measurableSet_Iio (planarIncidentProfile k σ L)

theorem planarNormalizedDrive_coe (k : ℝ) (σ : Direction) (L h : ℝ) :
    (planarNormalizedDrive k σ L h : HeightL2) =ᵐ[volume]
      (Icc 0 L).indicator (fun z => if z < h then 0 else planarIncidentPhase k σ z) := by
  let p := planarIncidentProfile k σ L
  let s := supportedSliceCLM volume (Icc 0 L) (Iio h) measurableSet_Iio p
  filter_upwards [Lp.coeFn_sub (p : HeightL2) (s : HeightL2), planarIncidentProfile_coe k σ L,
    supportedSliceCLM_coe volume (Icc 0 L) (Iio h) measurableSet_Iio p] with z hd hp hs
  change ((p : HeightL2) - (s : HeightL2)) z = _
  rw [hd]
  change (p : HeightL2) z - (s : HeightL2) z = _
  rw [hs, hp]
  change (Icc 0 L).indicator (planarIncidentPhase k σ) z - (Iio h).indicator (fun z => (p : HeightL2) z) z = _
  by_cases hz : z ∈ Icc 0 L <;> by_cases hh : z < h <;>
    simp [hz, hh, mem_Iio, hp, p]

theorem planarNormalizedDrive_ne_zero (k : ℝ) (σ : Direction) (L h : ℝ) (hh : 0 ≤ h) (hL : h < L) :
    planarNormalizedDrive k σ L h ≠ 0 := by
  intro he
  have ha : ∀ᵐ z : ℝ ∂volume, z ∉ Ioo h L := by
    filter_upwards [planarNormalizedDrive_coe k σ L h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with z hz hzero
    intro hm
    rw [he] at hz
    change (0 : HeightL2) z = _ at hz
    rw [hzero, indicator_of_mem (show z ∈ Icc 0 L from ⟨hh.trans hm.1.le, hm.2.le⟩),
      if_neg (not_lt.mpr hm.1.le)] at hz
    have hn := planarIncidentPhase_norm k σ z
    rw [← hz] at hn
    norm_num at hn
  have hnull := measure_eq_zero_iff_ae_notMem.mpr ha
  have hpos : 0 < volume (Ioo h L) := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hL)
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

end OQ7Prescribed
