import PrescribedExtinction.PlanarCurrentSpace
import PrescribedExtinction.RotationContinuity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OQ7Prescribed
open Set MeasureTheory

def planarLayerAxisMap (L h a b : ℝ) : PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L :=
  twoPieceSupportedMap volume (Icc 0 L) (Iio h) measurableSet_Iio
    ((a : ℂ) • ContinuousLinearMap.id ℂ ℂ) ((b : ℂ) • ContinuousLinearMap.id ℂ ℂ)

theorem planarLayerAxisMap_coe (L h a b : ℝ) (q : PlanarCurrentL2 L) :
    (planarLayerAxisMap L h a b q : HeightL2) =ᵐ[volume]
      fun z => if z < h then (a : ℂ) * (q : HeightL2) z else (b : ℂ) * (q : HeightL2) z := by
  simpa only [planarLayerAxisMap, mem_Iio, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    using twoPieceSupportedMap_coe volume (Icc 0 L) (Iio h) measurableSet_Iio
      ((a : ℂ) • ContinuousLinearMap.id ℂ ℂ) ((b : ℂ) • ContinuousLinearMap.id ℂ ℂ) q

theorem planarLayerAxisMap_adjoint (L h a b : ℝ) :
    (planarLayerAxisMap L h a b).adjoint = planarLayerAxisMap L h a b := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro q r
  have he := twoPieceSupportedMap_adjoint_inner volume (Icc 0 L) (Iio h) measurableSet_Iio
    ((a : ℂ) • ContinuousLinearMap.id ℂ ℂ) ((b : ℂ) • ContinuousLinearMap.id ℂ ℂ) q r
  have hscalar (t : ℝ) : ((t : ℂ) • ContinuousLinearMap.id ℂ ℂ).adjoint =
      (t : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
    rw [map_smulₛₗ, ContinuousLinearMap.adjoint_id]
    apply ContinuousLinearMap.ext
    intro z
    change (starRingEnd ℂ) (t : ℂ) * z = (t : ℂ) * z
    rw [Complex.conj_ofReal]
  rw [hscalar a, hscalar b] at he
  exact he

def planarActiveOutgoing (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ) :
    PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L :=
  (planarLayerAxisMap L h 1 (Real.cos θ)).adjoint ∘L planarScalarOutgoing k hk L hL ∘L
    planarLayerAxisMap L h 1 (Real.cos θ) +
      (planarLayerAxisMap L h 0 (Real.sin θ)).adjoint ∘L planarScalarOutgoing k hk L hL ∘L
        planarLayerAxisMap L h 0 (Real.sin θ)

theorem planarLayerAxisMap_parameter_continuous (L h : ℝ) :
    Continuous (fun p : ℝ × ℝ => planarLayerAxisMap L h p.1 p.2) := by
  have hc := twoPieceSupportedMap_continuous (E := ℂ) (F := ℂ) (volume : Measure ℝ) (Icc 0 L) (Iio h) measurableSet_Iio
  have hp : Continuous (fun p : ℝ × ℝ =>
      ((p.1 : ℂ) • ContinuousLinearMap.id ℂ ℂ, (p.2 : ℂ) • ContinuousLinearMap.id ℂ ℂ)) := by
    exact ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const).prodMk
      ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)
  have he := hc.comp hp
  change Continuous (fun p : ℝ × ℝ => twoPieceSupportedMap volume (Icc 0 L) (Iio h) measurableSet_Iio
    ((p.1 : ℂ) • ContinuousLinearMap.id ℂ ℂ) ((p.2 : ℂ) • ContinuousLinearMap.id ℂ ℂ))
  exact he

theorem planarActiveOutgoing_rotation_continuous (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h : ℝ) :
    Continuous (fun θ => planarActiveOutgoing k hk L hL h θ) := by
  have hcp : Continuous (fun θ : ℝ => ((1 : ℝ), Real.cos θ)) := continuous_const.prodMk Real.continuous_cos
  have hsp : Continuous (fun θ : ℝ => ((0 : ℝ), Real.sin θ)) := continuous_const.prodMk Real.continuous_sin
  have hc0 := (planarLayerAxisMap_parameter_continuous L h).comp hcp
  have hs0 := (planarLayerAxisMap_parameter_continuous L h).comp hsp
  have hc : Continuous (fun θ : ℝ => planarLayerAxisMap L h 1 (Real.cos θ)) := by
    simpa only [Function.comp_def] using hc0
  have hs : Continuous (fun θ : ℝ => planarLayerAxisMap L h 0 (Real.sin θ)) := by
    simpa only [Function.comp_def] using hs0
  change Continuous (fun θ : ℝ =>
    (planarLayerAxisMap L h 1 (Real.cos θ)).adjoint ∘L planarScalarOutgoing k hk L hL ∘L planarLayerAxisMap L h 1 (Real.cos θ) +
    (planarLayerAxisMap L h 0 (Real.sin θ)).adjoint ∘L planarScalarOutgoing k hk L hL ∘L planarLayerAxisMap L h 0 (Real.sin θ))
  exact ((ContinuousLinearMap.adjoint.continuous.comp hc).clm_comp (continuous_const.clm_comp hc)).add
    ((ContinuousLinearMap.adjoint.continuous.comp hs).clm_comp (continuous_const.clm_comp hs))

end OQ7Prescribed
