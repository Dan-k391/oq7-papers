import QuarticMaxwell.PhysicalPowers

/-! Reuse of the exact continuum volume problem, with a new complex-polarization
reciprocity bridge. No inverse, optical law or unique state is assumed in Medium. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FixedResource
open MeasureTheory Set OQ7Prescribed QuarticMaxwell
open WeakMaterial PhysicalPowers

theorem bounded_volume_operator (B : Medium) {k : ℝ} (hk : 0 ≤ k)
    (hV : 0 < volume.real B.domain) :
    ‖domainStaticOperator B.domain B.measurable‖ ≤ 1 ∧
    ‖domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball -
      domainStaticOperator B.domain B.measurable‖ ≤
        3 / 4 * k ^ 2 * volumeRadius (volume.real B.domain) ^ 2 :=
  ⟨domainStaticOperator_norm_le _ _,
    domainOutgoingOperator_difference_norm_le hk _ _ _ _ hV⟩

theorem null_support_zero (B : Medium) (hV : volume.real B.domain = 0)
    (p : DomainL2 B.domain) : p = 0 := by
  have hz : volume B.domain = 0 :=
    (ENNReal.toReal_eq_zero_iff (volume B.domain)).mp hV |>.resolve_right B.finite
  have ha : ∀ᵐ x ∂volume, x ∉ B.domain := measure_eq_zero_iff_ae_notMem.mp hz
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [p.property, ha, Lp.coeFn_zero (E := Vector) (p := 2) (μ := volume)] with x hp hx h0
  change (p : VectorL2) x = (0 : VectorL2) x
  rw [h0]
  exact hp hx

theorem bounded_volume_operator_all (B : Medium) {k : ℝ} (hk : 0 ≤ k) :
    ‖domainStaticOperator B.domain B.measurable‖ ≤ 1 ∧
    ‖domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball -
      domainStaticOperator B.domain B.measurable‖ ≤
        3 / 4 * k ^ 2 * volumeRadius (volume.real B.domain) ^ 2 := by
  rcases eq_or_lt_of_le (show 0 ≤ volume.real B.domain by positivity) with hz | hp
  · refine ⟨domainStaticOperator_norm_le _ _, ?_⟩
    have he : domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball -
        domainStaticOperator B.domain B.measurable = 0 := by
      ext p
      rw [null_support_zero B hz.symm p]
      simp
    have hn : ‖(0 : DomainL2 B.domain →L[ℂ] DomainL2 B.domain)‖ = 0 :=
      ContinuousLinearMap.opNorm_zero
    rw [he, hn]
    positivity
  · exact bounded_volume_operator B hk hp

theorem inverse_bound (B : Medium) {k : ℝ} (hk : 0 < k) :
    ‖(VolumeInverse.equiv B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos
      B.finite B.radius_nonneg B.subset_ball).symm.toContinuousLinearMap‖ ≤ B.M ^ 2 / B.m :=
  VolumeInverse.inverse_norm_le _ _ _ _ _ _ _ _ hk B.M_pos _ _ _

theorem weak_maxwell_wellposed (B : Medium) {k : ℝ} (hk : 0 < k)
    (n : UnitSphere) (e : Vector) (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0) :
    ∃ s : State B k n e, ∀ t : State B k n e,
      t.electric =ᵐ[volume] s.electric ∧ t.magnetic =ᵐ[volume] s.magnetic :=
  wellposed B hk n e htr

theorem conjugate_incident_source (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set QuarticMaxwell.Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    domainConjugate D (domainIncidentSource k n e D hD hfin) =
      domainIncidentSource (-k) n (vectorConjugate e) D hD hfin := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [conjugateL2_coe (incidentSource k n e D hD hfin),
    incidentSource_coe k n e D hD hfin,
    incidentSource_coe (-k) n (vectorConjugate e) D hD hfin] with x hc hp hm
  change conjugateL2 (incidentSource k n e D hD hfin) x =
    incidentSource (-k) n (vectorConjugate e) D hD hfin x
  rw [hc, hp, hm]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx, incidentWave, vectorConjugate_smul,
      radiationPhase_conjugate]
  · simp only [indicator_of_notMem hx]
    ext i
    simp [vectorConjugate_apply]

theorem conjugate_polarization_transverse (n : UnitSphere) (e : Vector)
    (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0) :
    bilinear (complexify (opposite n : QuarticMaxwell.Position)) (vectorConjugate e) = 0 := by
  apply opposite_transverse
  have hc := congrArg star htr
  simpa [bilinear, complexify, vectorConjugate_apply, map_sum, map_mul] using hc

theorem complex_pair_volume_work (B : Medium) {k : ℝ} (hk : 0 < k)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) :
    let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos
      B.finite B.radius_nonneg B.subset_ball
    UniformBound.extinctionPower k A (domainIncidentSource k n e B.domain B.measurable B.finite) =
    UniformBound.extinctionPower k A
      (domainIncidentSource (-k) n (vectorConjugate e) B.domain B.measurable B.finite) := by
  let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility
    B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos
    B.finite B.radius_nonneg B.subset_ball
  have h := domain_conjugate_pair_common_work B.domain A
    (VolumeInverse.operator_reciprocity B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk hsym
      B.radius_nonneg B.subset_ball)
    (domainIncidentSource k n e B.domain B.measurable B.finite)
  rw [conjugate_incident_source] at h
  have hi := congrArg Complex.im h
  let f := domainIncidentSource k n e B.domain B.measurable B.finite
  let g := domainIncidentSource (-k) n (vectorConjugate e) B.domain B.measurable B.finite
  have hp := inner_im_symm (𝕜 := ℂ) (A.symm f) f
  have hq := inner_im_symm (𝕜 := ℂ) (A.symm g) g
  change (inner ℂ (A.symm f) f).im = -(inner ℂ f (A.symm f)).im at hp
  change (inner ℂ (A.symm g) g).im = -(inner ℂ g (A.symm g)).im at hq
  change -k * (inner ℂ (A.symm f) f).im = -k * (inner ℂ (A.symm g) g).im
  rw [hp, hq]
  exact congrArg (fun z : ℝ => -k * -z) hi

theorem complex_pair_extinction (B : Medium) {k : ℝ} (hk : 0 < k)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0)
    (s : State B k n e) (t : State B k (opposite n) (vectorConjugate e)) :
    extinction B k n e s.electric =
      extinction B k (opposite n) (vectorConjugate e) t.electric := by
  rw [state_extinction B hk n e htr s,
    state_extinction B hk _ _ (conjugate_polarization_transverse n e htr) t,
    source_opposite]
  exact complex_pair_volume_work B hk hsym n e

theorem positive_extinction (B : Medium) {k : ℝ} (hk : 0 < k)
    (hV : 0 < volume.real B.domain) (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1)
    (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0) (s : State B k n e) :
    0 < extinction B k n e s.electric := by
  rw [state_extinction B hk n e htr s]
  have hM := B.M_pos
  have hm := B.m_pos
  apply UniformBound.extinction_pos _ hk (by positivity : 0 < B.M ^ 2 / B.m)
  · intro p
    have h := VolumeInverse.negative_coercive B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos
      B.finite B.radius_nonneg B.subset_ball p
    convert h using 1 <;> first | rfl | field_simp
  · intro hz
    have h := domainIncidentSource_norm_sq k n e B.domain B.measurable B.finite
    rw [hz, norm_zero, he] at h
    norm_num at h
    linarith

end FixedResource
