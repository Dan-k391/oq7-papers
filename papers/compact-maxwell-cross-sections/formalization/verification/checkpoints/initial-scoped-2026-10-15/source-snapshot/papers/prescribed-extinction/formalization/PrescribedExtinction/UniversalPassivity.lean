import PrescribedExtinction.OutgoingWeakEnergy
import PrescribedExtinction.UniversalStrictAbsorption
import PrescribedExtinction.WeakScatteringResidual
import PrescribedExtinction.ForwardOpticalTheorem

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem compactCurrent_inner_locallyL2_integrable (p : CompactPolarization)
    (E : Field) (hE : LocallySquareIntegrable E) :
    Integrable (fun x => pairing (p.current x) (E x)) volume := by
  have h := locallyL2_inner_compactL2_integrable E hE p.current p.memLp
    (compactPolarization_current_hasCompactSupport p)
  apply (Complex.conjCLE.toContinuousLinearMap.integrable_comp h).congr
  exact ae_of_all _ fun x => by
    change star (inner ℂ (E x) (p.current x)) = pairing (p.current x) (E x)
    rw [pairing_eq_inner]
    exact inner_conj_symm (𝕜 := ℂ) (p.current x) (E x)

/-- The scattered-field source work is exactly X-A for the original powers. -/
theorem physical_scattered_source_work (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (E : Field) (hE : LocallySquareIntegrable E) :
    k * (∫ x : Position, pairing (polarization B E x)
      (E x - incidentElectric k σ x)).im = extinction k B σ E - absorption k B E := by
  let p := physicalCompactPolarization B E hE
  have hEs : LocallySquareIntegrable (fun x => E x - incidentElectric k σ x) := by
    intro K hK
    exact (hE K hK).sub (incidentElectric_locallySquareIntegrable k σ K hK)
  have hi := compactCurrent_inner_locallyL2_integrable p _ hEs
  have hiInc := locallyL2_inner_compactL2_integrable (incidentElectric k σ)
    (incidentElectric_locallySquareIntegrable k σ) p.current p.memLp
    (compactPolarization_current_hasCompactSupport p)
  have hiX : IntegrableOn (fun x => (pairing (incidentElectric k σ x) (polarization B E x)).im)
      B.domain volume := by
        have h : IntegrableOn (fun x => (inner ℂ (incidentElectric k σ x) (p.current x)).im) B.domain volume :=
          hiInc.im.restrict
        simpa only [pairing_eq_inner, p, physicalCompactPolarization] using h
  have hiA := physicalAbsorption_integrable B E hE
  have he : (∫ x : Position, pairing (polarization B E x) (E x - incidentElectric k σ x)).im =
      ∫ x in B.domain, (pairing (polarization B E x) (E x - incidentElectric k σ x)).im := by
    change RCLike.im (∫ x : Position, pairing (p.current x) (E x - incidentElectric k σ x)) = _
    rw [← integral_im hi, ← integral_indicator (bodyDomain_isOpen B).measurableSet]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ B.domain
    · rw [indicator_of_mem hx]
      rfl
    · rw [indicator_of_notMem hx]
      have hz : polarization B E x = 0 := by rw [physicalPolarization_indicator, indicator_of_notMem hx]
      simp [p, physicalCompactPolarization, hz, pairing]
  have hp (x : Position) : (pairing (polarization B E x) (E x - incidentElectric k σ x)).im =
      (pairing (incidentElectric k σ x) (polarization B E x)).im -
        (quadratic (B.permittivity x) (E x)).im := by
    rw [pairing_eq_inner, inner_sub_right, Complex.sub_im]
    have h1 := inner_im_symm (𝕜 := ℂ) (polarization B E x) (E x)
    have h2 := inner_im_symm (𝕜 := ℂ) (polarization B E x) (incidentElectric k σ x)
    have h3 := susceptibility_quadratic_im (B.permittivity x) (E x)
    change (inner ℂ (E x) (polarization B E x)).im = (quadratic (B.permittivity x) (E x)).im at h3
    rw [pairing_eq_inner]
    change (inner ℂ (polarization B E x) (E x)).im -
      (inner ℂ (polarization B E x) (incidentElectric k σ x)).im = _
    change (inner ℂ (polarization B E x) (E x)).im = -(inner ℂ (E x) (polarization B E x)).im at h1
    change (inner ℂ (polarization B E x) (incidentElectric k σ x)).im =
      -(inner ℂ (incidentElectric k σ x) (polarization B E x)).im at h2
    linarith
  rw [he]
  simp_rw [hp]
  rw [integral_sub hiX hiA]
  unfold extinction absorption
  have hic : Integrable (fun x => pairing (incidentElectric k σ x) (polarization B E x))
      (volume.restrict B.domain) := by simpa only [pairing_eq_inner, p, physicalCompactPolarization] using hiInc.restrict
  have him : (∫ x in B.domain, pairing (incidentElectric k σ x) (polarization B E x)).im =
      ∫ x in B.domain, (pairing (incidentElectric k σ x) (polarization B E x)).im :=
    (Complex.imCLM.integral_comp_comm hic).symm
  rw [him]
  ring

theorem scatteringState_scattered_source (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (s : ScatteringState k B σ) :
    let E := fun x => s.electric x - incidentElectric k σ x
    let H := fun x => s.magnetic x - incidentMagnetic k σ x
    LocallySquareIntegrable E ∧ LocallySquareIntegrable H ∧
      HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x) ∧
      HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • (E x + polarization B s.electric x)) := by
  have hEi := locallySquareIntegrable_locallyIntegrable _ (incidentElectric_locallySquareIntegrable k σ)
  have hHi := locallySquareIntegrable_locallyIntegrable _ (incidentMagnetic_locallySquareIntegrable k σ)
  have hE := locallySquareIntegrable_locallyIntegrable _ s.maxwell.1
  have hH := locallySquareIntegrable_locallyIntegrable _ s.maxwell.2.1
  have hp := (compactPolarization_current_integrable (physicalCompactPolarization B s.electric s.maxwell.1)).locallyIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact (s.maxwell.1 K hK).sub (incidentElectric_locallySquareIntegrable k σ K hK)
  · intro K hK
    exact (s.maxwell.2.1 K hK).sub (incidentMagnetic_locallySquareIntegrable k σ K hK)
  · have h := s.maxwell.2.2.1.sub_fields (incidentElectric_first_weakCurl k σ) hE hEi
      (hH.smul (Complex.I * (k : ℂ))) (hHi.smul (Complex.I * (k : ℂ)))
    convert h using 1 <;> funext x <;> simp [Pi.sub_apply, smul_sub]
  · have hs : HasWeakCurl s.magnetic (fun x => (-Complex.I * (k : ℂ)) •
        (s.electric x + polarization B s.electric x)) := by
      apply s.maxwell.2.2.2.congr_ae (ae_of_all _ fun _ => rfl)
      exact ae_of_all _ (fun x => by
        change (-Complex.I * (k : ℂ)) • tensorApply (B.permittivity x) (s.electric x) =
          (-Complex.I * (k : ℂ)) • (s.electric x + polarization B s.electric x)
        rw [electric_add_polarization])
    have h := hs.sub_fields (incidentMagnetic_second_weakCurl k σ) hH hHi
      ((hE.add hp).smul (-Complex.I * (k : ℂ))) (hEi.smul (-Complex.I * (k : ℂ)))
    convert h using 1
    funext x
    simp only [Pi.sub_apply, ← smul_sub]
    congr 1
    abel

/-- Universal passivity for every original outgoing weak Maxwell scattering state. -/
theorem scatteringState_absorption_le_extinction (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (s : ScatteringState k B σ) : absorption k B s.electric ≤ extinction k B σ s.electric := by
  obtain ⟨hE, hH, he, hh⟩ := scatteringState_scattered_source k B σ s
  have h := outgoing_weak_source_work_nonneg k _ _ (physicalCompactPolarization B s.electric s.maxwell.1)
    hE hH he hh s.outgoing
  change 0 ≤ k * (∫ x : Position, pairing (polarization B s.electric x)
    (s.electric x - incidentElectric k σ x)).im at h
  rw [physical_scattered_source_work k B σ _ s.maxwell.1] at h
  linarith

theorem scatteringState_extinction_nonneg (k : ℝ) (hk : 0 ≤ k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q) (σ : Direction) (s : ScatteringState k B σ) :
    0 ≤ extinction k B σ s.electric :=
  (physicalAbsorption_nonneg k hk P Q B hB _).trans (scatteringState_absorption_le_extinction k B σ s)

end OQ7Prescribed
