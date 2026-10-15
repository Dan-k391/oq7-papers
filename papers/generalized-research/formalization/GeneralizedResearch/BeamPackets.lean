import GeneralizedResearch.BeamFibers
import GeneralizedResearch.FiniteHilbertBridge
import Mathlib.Analysis.Fourier.LpSpace

/-! Genuine L² angular-spectrum packets and their spatial inverse Fourier
transforms. Norms and real inner products are exact disk averages, with no
formal delta-function plane wave used as a finite-power input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.BeamPackets
open MeasureTheory Set BeamAveraging
open scoped Topology
abbrev Transverse := BeamAveraging.Transverse

def disk (r:ℝ) : Set Transverse := Metric.closedBall 0 r
def packet {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (r:ℝ) (F:Transverse→E) : Transverse→E :=
  fun q=>(aperture volume (disk r) q:ℂ) • F q

theorem packet_memLp {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopology E] (r:ℝ) (F:Transverse→E) (hF:ContinuousOn F (disk r)) :
    MemLp (packet r F) 2 volume := by
  have hK : IsCompact (disk r) := isCompact_closedBall _ _
  have hm : MeasurableSet (disk r) := hK.measurableSet
  let : IsFiniteMeasure (volume.restrict (disk r)) := ⟨by simpa using hK.measure_ne_top.lt_top⟩
  have hc : ContinuousOn (fun q=>((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) (disk r) :=
    continuousOn_const.smul hF
  obtain ⟨C,hC⟩ := hK.bddAbove_image hc.norm
  have hlp : MemLp (fun q=>((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) 2 (volume.restrict (disk r)) := by
    apply MemLp.of_bound (hc.aestronglyMeasurable hm) C
    filter_upwards [ae_restrict_mem hm] with q hq
    exact hC ⟨q,hq,rfl⟩
  have hi : packet r F=(disk r).indicator (fun q=>((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) := by
    funext q
    by_cases hq:q∈disk r <;> simp [packet,aperture,hq]
  rw [hi,memLp_indicator_iff_restrict hm]
  exact hlp

theorem lp_integral_norm_sq {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f:Lp E 2 (volume:Measure Transverse)) : (∫q,‖f q‖^2)=‖f‖^2 := by
  have h := Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜:=ℂ) f f)
  have hs : (inner ℂ f f).re=‖f‖^2 := by
    simp [inner_self_eq_norm_sq_to_K,pow_two,Complex.mul_re]
  rw [L2.inner_def] at hs
  rw [←hs]
  change (∫q,‖f q‖^2)=Complex.reCLM (∫q,inner ℂ (f q) (f q))
  rw [←h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q=>by simp [inner_self_eq_norm_sq_to_K,pow_two,Complex.mul_re]

theorem toLp_norm_sq {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f:Transverse→E} (hf:MemLp f 2 volume) : ‖hf.toLp f‖^2=∫q,‖f q‖^2 := by
  rw [←lp_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with q hq
  rw [hq]

theorem packet_norm_sq {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r:ℝ) (hr:0<r) (F:Transverse→E) (hF:MemLp (packet r F) 2 volume) :
    ‖hF.toLp (packet r F)‖^2=diskAverage r (fun q=>‖F q‖^2) := by
  rw [toLp_norm_sq]
  have he : (fun q=>‖packet r F q‖^2)=fun q=>aperture volume (disk r) q^2*‖F q‖^2 := by
    funext q
    simp [packet,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [he,aperture_average volume (disk r) (isCompact_closedBall _ _).measurableSet (disk_mass_pos hr)]
  rfl

theorem toLp_real_inner {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f g:Transverse→E} (hf:MemLp f 2 volume) (hg:MemLp g 2 volume) :
    (inner ℂ (hf.toLp f) (hg.toLp g)).re=∫q,(inner ℂ (f q) (g q)).re := by
  have h := Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜:=ℂ) (hf.toLp f) (hg.toLp g))
  rw [L2.inner_def]
  change Complex.reCLM (∫q,inner ℂ ((hf.toLp f) q) ((hg.toLp g) q))=_
  rw [←h]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with q hfq hgq
  rw [hfq,hgq]
  rfl

theorem packet_real_inner {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r:ℝ) (hr:0<r) (F G:Transverse→E)
    (hF:MemLp (packet r F) 2 volume) (hG:MemLp (packet r G) 2 volume) :
    (inner ℂ (hF.toLp (packet r F)) (hG.toLp (packet r G))).re=
      diskAverage r (fun q=>(inner ℂ (F q) (G q)).re) := by
  rw [toLp_real_inner]
  have he : (fun q=>(inner ℂ (packet r F q) (packet r G q)).re)=
      fun q=>aperture volume (disk r) q^2*(inner ℂ (F q) (G q)).re := by
    funext q
    change (inner ℂ ((aperture volume (disk r) q:ℂ) • F q)
      ((aperture volume (disk r) q:ℂ) • G q)).re=_
    rw [inner_smul_left,inner_smul_right]
    simp [Complex.mul_re,pow_two]
    ring
  rw [he,aperture_average volume (disk r) (isCompact_closedBall _ _).measurableSet (disk_mass_pos hr)]
  rfl

def spatial {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f:Lp E 2 (volume:Measure Transverse)) : Lp E 2 (volume:Measure Transverse) :=
  (Lp.fourierTransformₗᵢ Transverse E).symm f

theorem spatial_norm {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f:Lp E 2 (volume:Measure Transverse)) : ‖spatial f‖=‖f‖ :=
  (Lp.fourierTransformₗᵢ Transverse E).symm.norm_map f

theorem spatial_inner {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f g:Lp E 2 (volume:Measure Transverse)) : inner ℂ (spatial f) (spatial g)=inner ℂ f g :=
  (Lp.fourierTransformₗᵢ Transverse E).symm.inner_map_map f g

end GeneralizedResearch.BeamPackets
