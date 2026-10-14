import PrescribedExtinction.OutgoingSourceFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def tensorMap (T : Tensor) : Vector →L[ℂ] Vector :=
  (Matrix.toEuclideanLin T).toContinuousLinearMap

theorem tensorMap_apply (T : Tensor) (v : Vector) : tensorMap T v = tensorApply T v := rfl

theorem bodyDomain_isOpen (B : TwoLayerBody) : IsOpen B.domain := by
  unfold TwoLayerBody.domain bodyDomain squareAperture
  have hc (i : Fin 3) : Continuous (fun x : Position => x i) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : Position →L[ℝ] ℝ).continuous
  have hlo (c : ℝ) (i : Fin 3) : IsOpen {x : Position | c < x i} := isOpen_lt continuous_const (hc i)
  have hhi (c : ℝ) (i : Fin 3) : IsOpen {x : Position | x i < c} := isOpen_lt (hc i) continuous_const
  convert (((hlo (-B.aperture / 2) 0).inter (hhi (B.aperture / 2) 0)).inter
    ((hlo (-B.aperture / 2) 1).inter (hhi (B.aperture / 2) 1))).inter
    ((hlo 0 2).inter (hhi (B.absorberThickness + B.plateThickness) 2)) using 1
  ext x
  simp [and_assoc]

theorem physicalPolarization_indicator (B : TwoLayerBody) (E : Field) :
    polarization B E = B.domain.indicator
      (fun x => if x 2 < B.absorberThickness then tensorMap (B.absorberPermittivity - 1) (E x)
        else tensorMap (B.platePermittivity - 1) (E x)) := by
  classical
  funext x
  by_cases hx : x ∈ B.domain
  · rw [indicator_of_mem hx]
    simp only [polarization, TwoLayerBody.susceptibility, TwoLayerBody.permittivity, hx, ite_true,
      tensorMap_apply]
    split_ifs <;> rfl
  · simp [indicator_of_notMem hx, polarization, susceptibility_zero_outside B x hx, tensorApply]

theorem physicalPolarization_memLp (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) : MemLp (polarization B E) 2 volume := by
  classical
  have hD := (bodyDomain_isOpen B).measurableSet
  have hm : MeasurableSet {x : Position | x 2 < B.absorberThickness} :=
    (isOpen_lt (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Position →L[ℝ] ℝ).continuous continuous_const).measurableSet
  have hED : MemLp E 2 (volume.restrict B.domain) :=
    (hE (closure B.domain) (domain_compact_closure B)).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have h1 := hED.continuousLinearMap_comp (tensorMap (B.absorberPermittivity - 1))
  have h2 := hED.continuousLinearMap_comp (tensorMap (B.platePermittivity - 1))
  rw [physicalPolarization_indicator, memLp_indicator_iff_restrict hD]
  exact MemLp.piecewise hm (h1.restrict _) (h2.restrict _)

theorem physicalPolarization_vanish (B : TwoLayerBody) (E : Field) (x : Position)
    (hx : B.aperture + B.absorberThickness + B.plateThickness < ‖x‖) : polarization B E x = 0 := by
  have hnot : x ∉ B.domain := by
    intro hd
    have hb := domain_subset_closedBall B hd
    simp only [Metric.mem_closedBall, dist_zero_right] at hb
    linarith
  simp [polarization, susceptibility_zero_outside B x hnot, tensorApply]

/-- Every locally-L² physical electric field on a finite two-layer body has
a genuine compact L² polarization; no scattering state is assumed. -/
def physicalCompactPolarization (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) : CompactPolarization where
  current := polarization B E
  radius := B.aperture + B.absorberThickness + B.plateThickness
  radius_nonneg := by linarith [B.aperture_pos, B.absorberThickness_pos, B.plateThickness_pos]
  memLp := physicalPolarization_memLp B E hE
  vanish := physicalPolarization_vanish B E

end OQ7Prescribed
