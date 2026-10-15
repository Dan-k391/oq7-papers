import FixedResource.MaxwellCore

/-! Exact source, weak-field and physical-power correspondences for Section 4.
The pointwise far field is the canonical smooth exterior representative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CompactMaxwell.MaxwellCore
open MeasureTheory Set OQ7Prescribed QuarticMaxwell WeakMaterial PhysicalPowers

theorem green_bounded (B : Medium) {k : ℝ} (hk : 0 ≤ k)
    (hV : 0 < volume.real B.domain) :
    ‖domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball‖ ≤
      1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real B.domain) ^ 2 := by
  have h := (FixedResource.bounded_volume_operator B hk hV).2
  have h0 := (FixedResource.bounded_volume_operator B hk hV).1
  have hn := norm_add_le (domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball -
      domainStaticOperator B.domain B.measurable) (domainStaticOperator B.domain B.measurable)
  have he : domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball -
      domainStaticOperator B.domain B.measurable + domainStaticOperator B.domain B.measurable =
      domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball := by abel
  rw [he] at hn
  linarith

theorem green_radiation (B : Medium) {k : ℝ} (hk : 0 < k) (p : DomainL2 B.domain) :
    0 ≤ (inner ℂ p (domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball p)).im ∧
    k * (inner ℂ p (domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball p)).im =
      ∫ n : UnitSphere,
        ‖compactCurrentFarField k (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p) n‖ ^ 2
        ∂sphereArea := by
  refine ⟨domainOutgoingOperator_im_nonneg hk B.domain B.measurable B.finite
    B.radius_nonneg B.subset_ball p, ?_⟩
  rw [domainOutgoingOperator_radiation_work]
  exact (domainPolarization_farField_power k B.domain B.measurable B.finite
    B.radius_nonneg B.subset_ball p).symm

theorem far_field_continuous (k : ℝ) (p : CompactPolarization) :
    Continuous (compactCurrentFarField k p) := compactCurrentFarField_continuous k p

theorem entire_outgoing_vacuum_unique {k : ℝ} (hk : 0 < k) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (hout : Outgoing E H) : E =ᵐ[volume] 0 ∧ H =ᵐ[volume] 0 :=
  vacuum_outgoing_weak_unique_zero k hk E H hE hH he hh hout

theorem physical_problem (B : Medium) {k : ℝ} (hk : 0 < k)
    (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1)
    (hV : 0 < volume.real B.domain)
    (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0) :
    (∃ s : State B k n e, ∀ t : State B k n e,
      t.electric =ᵐ[volume] s.electric ∧ t.magnetic =ᵐ[volume] s.magnetic) ∧
    ‖(VolumeInverse.equiv B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos
      B.finite B.radius_nonneg B.subset_ball).symm.toContinuousLinearMap‖ ≤ B.M ^ 2 / B.m ∧
    ∀ s : State B k n e,
      0 < PhysicalPowers.extinction B k n e s.electric ∧
      PhysicalPowers.extinction B k n e s.electric =
        PhysicalPowers.absorption B k s.electric + PhysicalPowers.scattering B k s.electric s.electric_L2 ∧
      Filter.Tendsto (exteriorSphereFlux k (polarization B s.electric s.electric_L2)) Filter.atTop
        (nhds (PhysicalPowers.scattering B k s.electric s.electric_L2)) := by
  refine ⟨FixedResource.weak_maxwell_wellposed B hk n e htr,
    FixedResource.inverse_bound B hk, ?_⟩
  intro s
  exact ⟨FixedResource.positive_extinction B hk hV n e he htr s,
    state_power_balance B hk n e htr s, scattering_physical_flux B k s.electric s.electric_L2⟩

end CompactMaxwell.MaxwellCore
