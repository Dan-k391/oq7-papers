import GeneralizedResearch.PhysicalFourierIntegral

/-! L¹∩L² and literal physical angular integrals for the actual normalized packets. -/
noncomputable section
namespace GeneralizedResearch.BeamPhysicalPackets
open MeasureTheory Set BeamPackets BeamAveraging
abbrev Transverse := BeamAveraging.Transverse
theorem packet_memLp_one {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopology E] (r:ℝ) (F:Transverse→E) (hF:ContinuousOn F (disk r)) :
    MemLp (packet r F) 1 volume := by
  have hK : IsCompact (disk r) := isCompact_closedBall _ _
  have hm : MeasurableSet (disk r) := hK.measurableSet
  let : IsFiniteMeasure (volume.restrict (disk r)) := ⟨by simpa using hK.measure_ne_top.lt_top⟩
  have hc : ContinuousOn (fun q=>((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) (disk r) :=
    continuousOn_const.smul hF
  obtain ⟨C,hC⟩ := hK.bddAbove_image hc.norm
  have hlp : MemLp (fun q=>((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) 1 (volume.restrict (disk r)) := by
    apply MemLp.of_bound (hc.aestronglyMeasurable hm) C
    filter_upwards [ae_restrict_mem hm] with q hq
    exact hC ⟨q,hq,rfl⟩
  have hi : packet r F=(disk r).indicator (fun q=>((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) := by
    funext q
    by_cases hq:q∈disk r <;> simp [packet,aperture,hq]
  rw [hi,memLp_indicator_iff_restrict hm]
  exact hlp


theorem packet_integralInverse {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r:ℝ) (F:Transverse→E) (x:Transverse) :
    PhysicalFourier.integralInverse (packet r F) x=
      (PhysicalFourier.factor:ℂ) • ∫q in disk r,
        Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ)) •
          (((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) := by
  unfold PhysicalFourier.integralInverse
  congr 1
  calc
    _ = ∫q,(disk r).indicator (fun q=>Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ)) •
      (((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q)) q := by
      apply integral_congr_ae
      exact ae_of_all _ fun q=>by
        by_cases hq:q∈disk r <;> simp [packet,aperture,Set.indicator,hq]
    _ = _ := integral_indicator (isCompact_closedBall (0:Transverse) r).measurableSet

theorem packet_inverse_integral_ae {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [SecondCountableTopology E] [CompleteSpace E] (r:ℝ) (F:Transverse→E) (hF:ContinuousOn F (disk r)) :
    (PhysicalFourier.inverse ((packet_memLp r F hF).toLp (packet r F)) : Transverse→E) =ᵐ[volume]
      fun x=>(PhysicalFourier.factor:ℂ) • ∫q in disk r,
        Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ)) •
          (((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q) := by
  exact (PhysicalFourier.inverse_integral_ae (packet_memLp_one r F hF) (packet_memLp r F hF)).trans
    (ae_of_all _ fun x=>packet_integralInverse r F x)


theorem packet_inverse_coordinates_ae {n:Type*} [Fintype n] [DecidableEq n]
    (r:ℝ) (F:Transverse→EuclideanSpace ℂ n) (hF:ContinuousOn F (disk r)) :
    ∀ᵐx:Transverse,∀i:n,
      (PhysicalFourier.inverse ((packet_memLp r F hF).toLp (packet r F)) x) i=
        (PhysicalFourier.factor:ℂ)*∫q in disk r,
          Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ))*
            (((Real.sqrt (volume.real (disk r)):ℂ)⁻¹)*F q i) := by
  filter_upwards [packet_inverse_integral_ae r F hF] with x hx
  intro i
  let pr : EuclideanSpace ℂ n→L[ℂ]ℂ := PiLp.proj 2 (fun _:n=>ℂ) i
  have hc : Continuous (fun q:Transverse=>Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ))) := by fun_prop
  have hconst := hF.const_smul (((Real.sqrt (volume.real (disk r)):ℂ)⁻¹))
  have hi : IntegrableOn (fun q:Transverse=>Complex.exp (Complex.I*((inner ℝ q x:ℝ):ℂ)) •
      (((Real.sqrt (volume.real (disk r)):ℂ)⁻¹) • F q)) (disk r) :=
    (hc.continuousOn.smul hconst).integrableOn_compact (isCompact_closedBall _ _)
  have hp := pr.integral_comp_comm hi
  change pr (PhysicalFourier.inverse ((packet_memLp r F hF).toLp (packet r F)) x)=_
  rw [hx,map_smul,←hp]
  rfl

end GeneralizedResearch.BeamPhysicalPackets
