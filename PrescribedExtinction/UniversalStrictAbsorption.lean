import PrescribedExtinction.UniversalFieldPowers

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

theorem admissible_zeroAbsorption_zeroExtinction (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q) (E : Field) (hE : LocallySquareIntegrable E)
    (hA : absorption k B E = 0) (σ : Direction) : extinction k B σ E = 0 := by
  have hi := physicalAbsorption_integrable B E hE
  have hn : ∀ᵐ x ∂(volume.restrict B.domain), 0 ≤ (quadratic (B.permittivity x) (E x)).im := by
    filter_upwards [ae_restrict_mem (bodyDomain_isOpen B).measurableSet] with x hx
    exact material_quadratic_im_nonneg P Q _ (bodyPermittivity_admissible_on_domain P Q B hB x hx) _
  have hz : (∫ x in B.domain, (quadratic (B.permittivity x) (E x)).im) = 0 := by
    exact (mul_eq_zero.mp hA).resolve_left hk.ne'
  have hq := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  have hzero : E =ᵐ[volume.restrict B.domain] 0 := by
    filter_upwards [ae_restrict_mem (bodyDomain_isOpen B).measurableSet, hq] with x hx hqx
    by_contra he
    have ht := (bodyPermittivity_admissible_on_domain P Q B hB x hx).2.2.1 (E x) he
    change (quadratic (B.permittivity x) (E x)).im = 0 at hqx
    rw [hqx] at ht
    exact (lt_irrefl 0) ht
  unfold extinction
  have hpair : (fun x => pairing (incidentElectric k σ x) (polarization B E x)) =ᵐ[volume.restrict B.domain] 0 := by
    filter_upwards [hzero] with x hx
    simp [polarization, hx, tensorApply, pairing]
  rw [integral_congr_ae hpair]
  simp

theorem admissible_positiveExtinction_absorption_pos (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q) (E : Field) (hE : LocallySquareIntegrable E)
    (σ : Direction) (hX : 0 < extinction k B σ E) : 0 < absorption k B E := by
  refine lt_of_le_of_ne (physicalAbsorption_nonneg k hk.le P Q B hB E) ?_
  intro hz
  have h := admissible_zeroAbsorption_zeroExtinction k hk P Q B hB E hE hz.symm σ
  linarith

theorem scatteringState_positiveExtinction_absorption_pos (k : ℝ) (hk : 0 < k) (P Q : ℝ)
    (B : TwoLayerBody) (hB : B.admissible P Q) (σ : Direction) (s : ScatteringState k B σ)
    (hX : 0 < extinction k B σ s.electric) : 0 < absorption k B s.electric :=
  admissible_positiveExtinction_absorption_pos k hk P Q B hB _ s.maxwell.1 σ hX

end OQ7Prescribed
