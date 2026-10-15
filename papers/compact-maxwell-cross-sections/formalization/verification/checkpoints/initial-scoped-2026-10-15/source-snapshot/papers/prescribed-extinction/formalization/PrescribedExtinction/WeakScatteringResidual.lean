import PrescribedExtinction.WeakCurlProducts
import PrescribedExtinction.FarFieldKernel

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem Outgoing.sub_fields {E1 E2 H1 H2 : Field}
    (h1 : Outgoing E1 H1) (h2 : Outgoing E2 H2) : Outgoing (E1 - E2) (H1 - H2) := by
  intro ε hε
  obtain ⟨r1, hr1, hbound1⟩ := h1 (ε / 2) (by positivity)
  obtain ⟨r2, _, hbound2⟩ := h2 (ε / 2) (by positivity)
  refine ⟨max r1 r2, hr1.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  have hb1 := hbound1 x ((le_max_left _ _).trans hx)
  have hb2 := hbound2 x ((le_max_right _ _).trans hx)
  let n := complexify (‖x‖⁻¹ • x)
  have he : cross ((H1 - H2) x) n - (E1 - E2) x =
      (cross (H1 x) n - E1 x) - (cross (H2 x) n - E2 x) := by
    rw [Pi.sub_apply, Pi.sub_apply, cross_sub_left]
    abel
  rw [he]
  have hn := mul_le_mul_of_nonneg_left (norm_sub_le (cross (H1 x) n - E1 x)
    (cross (H2 x) n - E2 x)) (norm_nonneg x)
  dsimp [n] at hn
  nlinarith

theorem volumeTotalElectric_weakCurl (k : ℝ) (σ : Direction) (p : CompactPolarization) :
    HasWeakCurl (volumeTotalElectric k σ p)
      (fun x => (Complex.I * (k : ℂ)) • volumeTotalMagnetic k σ p x) := by
  have hei := locallySquareIntegrable_locallyIntegrable _ (incidentElectric_locallySquareIntegrable k σ)
  have hhi := locallySquareIntegrable_locallyIntegrable _ (incidentMagnetic_locallySquareIntegrable k σ)
  have hes := locallySquareIntegrable_locallyIntegrable _ (outgoingElectricField_locallySquareIntegrable k p)
  have hhs := locallySquareIntegrable_locallyIntegrable _ (outgoingMagneticField_locallySquareIntegrable k p)
  have h := (incidentElectric_first_weakCurl k σ).add_fields (outgoingSourceFields_first_weakCurl k p)
    hei hes (hhi.smul (Complex.I * (k : ℂ))) (hhs.smul (Complex.I * (k : ℂ)))
  convert h using 1 <;> funext x <;> simp [volumeTotalElectric, volumeTotalMagnetic, smul_add]

theorem volumeTotalMagnetic_weakCurl (k : ℝ) (σ : Direction) (p : CompactPolarization) :
    HasWeakCurl (volumeTotalMagnetic k σ p)
      (fun x => (-Complex.I * (k : ℂ)) • (volumeTotalElectric k σ p x + p.current x)) := by
  have hei := locallySquareIntegrable_locallyIntegrable _ (incidentElectric_locallySquareIntegrable k σ)
  have hhi := locallySquareIntegrable_locallyIntegrable _ (incidentMagnetic_locallySquareIntegrable k σ)
  have hes := locallySquareIntegrable_locallyIntegrable _ (outgoingElectricField_locallySquareIntegrable k p)
  have hhs := locallySquareIntegrable_locallyIntegrable _ (outgoingMagneticField_locallySquareIntegrable k p)
  have hp := (compactPolarization_current_integrable p).locallyIntegrable
  have h := (incidentMagnetic_second_weakCurl k σ).add_fields (outgoingSourceFields_second_weakCurl k p)
    hhi hhs (hei.smul (-Complex.I * (k : ℂ))) ((hes.add hp).smul (-Complex.I * (k : ℂ)))
  convert h using 1 <;> funext x <;> simp [volumeTotalElectric, volumeTotalMagnetic, smul_add, add_assoc]

/-- Subtracting the actual compact-source reconstruction from any original
weak scattering state leaves a genuine global source-free outgoing Maxwell pair.
The converse volume equation is not assumed. -/
theorem scatteringState_vacuum_residual (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (s : ScatteringState k B σ) :
    let p := physicalCompactPolarization B s.electric s.maxwell.1
    let E := s.electric - volumeTotalElectric k σ p
    let H := s.magnetic - volumeTotalMagnetic k σ p
    LocallySquareIntegrable E ∧ LocallySquareIntegrable H ∧
      HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x) ∧
      HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x) ∧ Outgoing E H := by
  let p := physicalCompactPolarization B s.electric s.maxwell.1
  have hEs := locallySquareIntegrable_locallyIntegrable _ s.maxwell.1
  have hHs := locallySquareIntegrable_locallyIntegrable _ s.maxwell.2.1
  have hEv := locallySquareIntegrable_locallyIntegrable _ (volumeTotalElectric_locallySquareIntegrable k σ p)
  have hHv := locallySquareIntegrable_locallyIntegrable _ (volumeTotalMagnetic_locallySquareIntegrable k σ p)
  have hp := (compactPolarization_current_integrable p).locallyIntegrable
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact (s.maxwell.1 K hK).sub (volumeTotalElectric_locallySquareIntegrable k σ p K hK)
  · intro K hK
    exact (s.maxwell.2.1 K hK).sub (volumeTotalMagnetic_locallySquareIntegrable k σ p K hK)
  · have h := s.maxwell.2.2.1.sub_fields (volumeTotalElectric_weakCurl k σ p) hEs hEv
      (hHs.smul (Complex.I * (k : ℂ))) (hHv.smul (Complex.I * (k : ℂ)))
    convert h using 1 <;> funext x <;> simp [Pi.sub_apply, smul_sub] <;> rfl
  · have hs : HasWeakCurl s.magnetic (fun x => (-Complex.I * (k : ℂ)) • (s.electric x + p.current x)) := by
      apply s.maxwell.2.2.2.congr_ae (ae_of_all _ fun _ => rfl)
      exact ae_of_all _ (fun x => by
        change (-Complex.I * (k : ℂ)) • tensorApply (B.permittivity x) (s.electric x) =
          (-Complex.I * (k : ℂ)) • (s.electric x + polarization B s.electric x)
        rw [electric_add_polarization])
    have h := hs.sub_fields (volumeTotalMagnetic_weakCurl k σ p) hHs hHv
      ((hEs.add hp).smul (-Complex.I * (k : ℂ))) ((hEv.add hp).smul (-Complex.I * (k : ℂ)))
    convert h using 1
    funext x
    change (-Complex.I * (k : ℂ)) • (s.electric x - volumeTotalElectric k σ p x) =
      (-Complex.I * (k : ℂ)) • (s.electric x + p.current x) -
        (-Complex.I * (k : ℂ)) • (volumeTotalElectric k σ p x + p.current x)
    rw [← smul_sub]
    congr 1
    abel
  · have h := s.outgoing.sub_fields (outgoingSourceFields_outgoing k p)
    have he : (fun x => s.electric x - incidentElectric k σ x) - outgoingElectricField k p =
        s.electric - volumeTotalElectric k σ p := by
      funext x
      simp only [Pi.sub_apply, volumeTotalElectric]
      abel
    have hh : (fun x => s.magnetic x - incidentMagnetic k σ x) - outgoingMagneticField k p =
        s.magnetic - volumeTotalMagnetic k σ p := by
      funext x
      simp only [Pi.sub_apply, volumeTotalMagnetic]
      abel
    rw [he, hh] at h
    exact h

end OQ7Prescribed
