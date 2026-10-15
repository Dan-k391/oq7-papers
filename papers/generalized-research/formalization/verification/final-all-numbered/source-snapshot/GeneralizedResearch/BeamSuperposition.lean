import GeneralizedResearch.FourierMaxwell
import GeneralizedResearch.BeamPackets
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of genuine compact angular-spectrum superpositions.
The hypotheses concern literal component functions and their derivatives. -/
noncomputable section
namespace GeneralizedResearch.BeamSuperposition
open MeasureTheory Set BeamPackets
open scoped Topology
abbrev Transverse := BeamAveraging.Transverse

theorem compact_parameter_derivative (r x0:ℝ) (F F':ℝ→Transverse→ℂ)
    (hF:ContinuousOn (fun p:ℝ×Transverse=>F p.1 p.2) (Icc (x0-1) (x0+1) ×ˢ disk r))
    (hF':ContinuousOn (fun p:ℝ×Transverse=>F' p.1 p.2) (Icc (x0-1) (x0+1) ×ˢ disk r))
    (hd:∀q∈disk r,∀x∈Icc (x0-1) (x0+1),HasDerivAt (fun z=>F z q) (F' x q) x) :
    HasDerivAt (fun x=>∫q in disk r,F x q) (∫q in disk r,F' x0 q) x0 := by
  have hK : IsCompact (disk r) := isCompact_closedBall _ _
  have hm : MeasurableSet (disk r) := hK.measurableSet
  let : IsFiniteMeasure (volume.restrict (disk r)) := ⟨by simpa using hK.measure_ne_top.lt_top⟩
  have hx0 : x0∈Icc (x0-1) (x0+1) := ⟨by linarith,by linarith⟩
  have hslice (x:ℝ) (hx:x∈Icc (x0-1) (x0+1)) : ContinuousOn (F x) (disk r) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun q hq=>⟨hx,hq⟩)
  have hslice' : ContinuousOn (F' x0) (disk r) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun q hq=>⟨hx0,hq⟩)
  have hmeas : ∀ᶠx in nhds x0,AEStronglyMeasurable (F x) (volume.restrict (disk r)) := by
    filter_upwards [Icc_mem_nhds (show x0-1<x0 by linarith) (show x0<x0+1 by linarith)] with x hx
    exact (hslice x hx).aestronglyMeasurable hm
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).bddAbove_image hF'.norm
  have hb : ∀ᵐq ∂volume.restrict (disk r),∀x∈Icc (x0-1) (x0+1),‖F' x q‖≤C := by
    filter_upwards [ae_restrict_mem hm] with q hq
    intro x hx
    exact hC ⟨(x,q),⟨hx,hq⟩,rfl⟩
  have hdiff : ∀ᵐq ∂volume.restrict (disk r),∀x∈Icc (x0-1) (x0+1),
      HasDerivAt (fun z=>F z q) (F' x q) x := by
    filter_upwards [ae_restrict_mem hm] with q hq
    exact hd q hq
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (show x0-1<x0 by linarith) (show x0<x0+1 by linarith))
    hmeas ((hslice x0 hx0).integrableOn_compact hK) (hslice'.aestronglyMeasurable hm)
    hb (integrable_const C) hdiff).2

end GeneralizedResearch.BeamSuperposition
