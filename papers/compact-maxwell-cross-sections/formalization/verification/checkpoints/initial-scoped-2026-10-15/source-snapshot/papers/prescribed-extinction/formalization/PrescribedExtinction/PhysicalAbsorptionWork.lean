import PrescribedExtinction.PhysicalExtinctionWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem bodyField_memLp (B : TwoLayerBody) (E : Field) (hE : LocallySquareIntegrable E) :
    MemLp (B.domain.indicator E) 2 volume := by
  rw [memLp_indicator_iff_restrict (bodyDomain_isOpen B).measurableSet]
  exact (hE (closure B.domain) (domain_compact_closure B)).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)

def bodyFieldCurrent (B : TwoLayerBody) (E : Field) (hE : LocallySquareIntegrable E) : BodyCurrentL2 B :=
  ⟨(bodyField_memLp B E hE).toLp (B.domain.indicator E), by
    change ∀ᵐ x ∂volume, x ∉ B.domain → ((bodyField_memLp B E hE).toLp (B.domain.indicator E)) x = 0
    filter_upwards [(bodyField_memLp B E hE).coeFn_toLp] with x hx
    intro hxd
    rw [hx, indicator_of_notMem hxd]⟩

theorem bodyFieldCurrent_coe (B : TwoLayerBody) (E : Field) (hE : LocallySquareIntegrable E) :
    (bodyFieldCurrent B E hE : VectorL2) =ᵐ[volume] B.domain.indicator E :=
  (bodyField_memLp B E hE).coeFn_toLp

theorem physicalAbsorption_current_inner (k : ℝ) (B : TwoLayerBody) (E : Field)
    (hE : LocallySquareIntegrable E) (f : BodyCurrentL2 B)
    (hp : (f : VectorL2) =ᵐ[volume] polarization B E) :
    absorption k B E = k * (inner ℂ (bodyFieldCurrent B E hE) f).im := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (bodyFieldCurrent B E hE : VectorL2) (f : VectorL2)
  have him : (inner ℂ (bodyFieldCurrent B E hE) f).im =
      ∫ x : Position, (inner ℂ ((bodyFieldCurrent B E hE : VectorL2) x) ((f : VectorL2) x)).im := by
    change (inner ℂ (bodyFieldCurrent B E hE : VectorL2) (f : VectorL2)).im = _
    rw [L2.inner_def]
    exact (Complex.imCLM.integral_comp_comm hi).symm
  rw [him]
  unfold absorption
  rw [← integral_indicator (bodyDomain_isOpen B).measurableSet]
  congr 1
  apply integral_congr_ae
  filter_upwards [bodyFieldCurrent_coe B E hE, hp] with x hx hf
  rw [hx, hf]
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd]
    change (quadratic (B.permittivity x) (E x)).im =
      (inner ℂ (E x) (tensorMap (B.permittivity x - 1) (E x))).im
    exact (susceptibility_quadratic_im _ _).symm
  · rw [indicator_of_notMem hxd, indicator_of_notMem hxd, inner_zero_left]
    rfl

theorem bodyVolumeTotalElectricCurrent_eq (k : ℝ) (B : TwoLayerBody) (σ : Direction) (f : BodyCurrentL2 B) :
    bodyFieldCurrent B (volumeTotalElectric k σ (bodyCurrentPolarization B f))
      (volumeTotalElectric_locallySquareIntegrable k σ (bodyCurrentPolarization B f)) =
      bodyIncidentCurrent k B σ + bodyOutgoingOperator k B f := by
  let p := bodyCurrentPolarization B f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [bodyFieldCurrent_coe B (volumeTotalElectric k σ p)
    (volumeTotalElectric_locallySquareIntegrable k σ p), bodyIncidentCurrent_coe k B σ,
    bodyOutgoingOperator_coe k B f,
    Lp.coeFn_add (bodyIncidentCurrent k B σ : VectorL2) (bodyOutgoingOperator k B f : VectorL2),
    outgoingElectricField_eq_ae k p] with x hx hi ht ha hout
  change (bodyFieldCurrent B (volumeTotalElectric k σ p)
    (volumeTotalElectric_locallySquareIntegrable k σ p) : VectorL2) x =
    ((bodyIncidentCurrent k B σ : VectorL2) + (bodyOutgoingOperator k B f : VectorL2)) x
  rw [hx, ha]
  change _ = (bodyIncidentCurrent k B σ : VectorL2) x + (bodyOutgoingOperator k B f : VectorL2) x
  rw [hi, ht]
  by_cases hxd : x ∈ B.domain
  · simp only [indicator_of_mem hxd, volumeTotalElectric, hout]
    rfl
  · simp only [indicator_of_notMem hxd, add_zero]

theorem volumeAbsorption_body_inner (k : ℝ) (B : TwoLayerBody) (σ : Direction) (f : BodyCurrentL2 B)
    (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    absorption k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) =
      k * (inner ℂ (bodyIncidentCurrent k B σ + bodyOutgoingOperator k B f) f).im := by
  rw [physicalAbsorption_current_inner k B _
    (volumeTotalElectric_locallySquareIntegrable k σ (bodyCurrentPolarization B f)) f
      ((bodyCurrentPolarization_current_ae B f).symm.trans hp), bodyVolumeTotalElectricCurrent_eq]

/-- Exact physical work balance. The remaining radiation theorem must identify
the outgoing-volume work term with the original full angular scattering integral. -/
theorem physicalVolume_work_balance (k : ℝ) (B : TwoLayerBody) (σ : Direction) (f : BodyCurrentL2 B)
    (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    extinction k B σ (volumeTotalElectric k σ (bodyCurrentPolarization B f)) =
      absorption k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) +
        k * (inner ℂ f (bodyOutgoingOperator k B f)).im := by
  rw [volumeExtinction_current_work k B σ _ hp, bodyCurrent_incident_work, volumeAbsorption_body_inner k B σ f hp,
    inner_add_left, Complex.add_im]
  have hs : (inner ℂ (bodyOutgoingOperator k B f) f).im = -(inner ℂ f (bodyOutgoingOperator k B f)).im :=
    inner_im_symm (𝕜 := ℂ) _ _
  rw [hs]
  ring

theorem physicalVolume_absorption_le_extinction (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (f : BodyCurrentL2 B) (hp : MaterialVolumeEquation k B σ (bodyCurrentPolarization B f)) :
    absorption k B (volumeTotalElectric k σ (bodyCurrentPolarization B f)) ≤
      extinction k B σ (volumeTotalElectric k σ (bodyCurrentPolarization B f)) := by
  rw [physicalVolume_work_balance k B σ f hp]
  exact le_add_of_nonneg_right (mul_nonneg hk.le (bodyOutgoingOperator_im_nonneg k hk B f))

end OQ7Prescribed
