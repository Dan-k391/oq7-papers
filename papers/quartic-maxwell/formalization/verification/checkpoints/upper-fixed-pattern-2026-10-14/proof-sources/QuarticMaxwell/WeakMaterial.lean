import QuarticMaxwell.PlaneWaves
import QuarticMaxwell.VolumeInverse
import PrescribedExtinction.VacuumOutgoingWeakUniqueness
import PrescribedExtinction.WeakScatteringResidual

/-! Actual outgoing weak Maxwell fields for arbitrary bounded measurable
tensor media. The data record contains only support and material hypotheses.
The weak scattering state does not assume a volume equation or optical law. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
namespace WeakMaterial
open MeasureTheory Set OQ7Prescribed

structure Medium where
  domain : Set Position
  measurable : MeasurableSet domain
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  subset_ball : domain ⊆ Metric.closedBall 0 radius
  finite : volume domain ≠ ⊤
  susceptibility : Position → Vector →L[ℂ] Vector
  measurable_susceptibility : AEStronglyMeasurable susceptibility volume
  M : ℝ
  M_pos : 0 < M
  cap : ∀ᵐ x ∂volume, x ∈ domain → ‖susceptibility x‖ ≤ M
  m : ℝ
  m_pos : 0 < m
  loss : ∀ᵐ x ∂volume, x ∈ domain → ∀ v : Vector,
    m * ‖v‖ ^ 2 ≤ (inner ℂ v (susceptibility x v)).im

def currentField (B : Medium) (E : Field) : Field :=
  B.domain.indicator (fun x => B.susceptibility x (E x))

theorem currentField_memLp (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    MemLp (currentField B E) 2 volume := by
  have hED : MemLp E 2 (volume.restrict B.domain) :=
    (hE (Metric.closedBall 0 B.radius) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono B.subset_ball le_rfl)
  have hf : MemLp (B.domain.indicator E) 2 volume :=
    (memLp_indicator_iff_restrict B.measurable).mpr hED
  have hh : MemLp (fun x => B.susceptibility x (B.domain.indicator E x)) 2 volume := by
    apply hf.of_le_mul ((ContinuousLinearMap.apply ℂ Vector).aestronglyMeasurable_comp₂
      hf.aestronglyMeasurable B.measurable_susceptibility)
    filter_upwards [B.cap] with x hx
    by_cases hxd : x ∈ B.domain
    · rw [indicator_of_mem hxd]
      exact ((B.susceptibility x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hx hxd) (norm_nonneg _))
    · simp [hxd]
  convert hh using 1
  funext x
  by_cases hx : x ∈ B.domain <;> simp [currentField, hx]

def polarization (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) : CompactPolarization where
  current := currentField B E
  radius := B.radius
  radius_nonneg := B.radius_nonneg
  memLp := currentField_memLp B E hE
  vanish x hx := by
    have hxd : x ∉ B.domain := by
      intro hd
      have hb := B.subset_ball hd
      simp only [Metric.mem_closedBall, dist_zero_right] at hb
      linarith
    simp [currentField, hxd]

def currentL2 (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) : DomainL2 B.domain :=
  ⟨(currentField_memLp B E hE).toLp (currentField B E), by
    change ∀ᵐ x ∂volume, x ∉ B.domain →
      ((currentField_memLp B E hE).toLp (currentField B E)) x = 0
    filter_upwards [(currentField_memLp B E hE).coeFn_toLp] with x hx
    intro hd
    rw [hx]
    simp [currentField, hd]⟩

theorem currentL2_coe (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    (currentL2 B E hE : VectorL2) =ᵐ[volume] currentField B E :=
  (currentField_memLp B E hE).coeFn_toLp

def totalElectric (k : ℝ) (n : UnitSphere) (e : Vector) (p : CompactPolarization) : Field :=
  fun x => incidentWave k n e x + outgoingElectricField k p x

def totalMagnetic (k : ℝ) (n : UnitSphere) (e : Vector) (p : CompactPolarization) : Field :=
  fun x => incidentMagneticWave k n e x + outgoingMagneticField k p x

theorem totalElectric_locallySquareIntegrable (k : ℝ) (n : UnitSphere) (e : Vector)
    (p : CompactPolarization) : LocallySquareIntegrable (totalElectric k n e p) := by
  intro K hK
  exact (incidentWave_locallySquareIntegrable k n e K hK).add
    (outgoingElectricField_locallySquareIntegrable k p K hK)

theorem totalMagnetic_locallySquareIntegrable (k : ℝ) (n : UnitSphere) (e : Vector)
    (p : CompactPolarization) : LocallySquareIntegrable (totalMagnetic k n e p) := by
  intro K hK
  exact (incidentMagneticWave_locallySquareIntegrable k n e K hK).add
    (outgoingMagneticField_locallySquareIntegrable k p K hK)

theorem totalElectric_weakCurl (k : ℝ) (n : UnitSphere) (e : Vector) (p : CompactPolarization) :
    HasWeakCurl (totalElectric k n e p)
      (fun x => (Complex.I * (k : ℂ)) • totalMagnetic k n e p x) := by
  have hei : LocallyIntegrable (incidentWave k n e) volume := (incidentWave_contDiff k n e).continuous.locallyIntegrable
  have hhi : LocallyIntegrable (incidentMagneticWave k n e) volume := (incidentMagneticWave_contDiff k n e).continuous.locallyIntegrable
  have hes := locallySquareIntegrable_locallyIntegrable _ (outgoingElectricField_locallySquareIntegrable k p)
  have hhs := locallySquareIntegrable_locallyIntegrable _ (outgoingMagneticField_locallySquareIntegrable k p)
  have h := (incidentWave_first_weakCurl k n e).add_fields (outgoingSourceFields_first_weakCurl k p)
    hei hes (hhi.smul (Complex.I * (k : ℂ))) (hhs.smul (Complex.I * (k : ℂ)))
  convert h using 1 <;> funext x <;> simp [totalElectric, totalMagnetic, smul_add]

theorem totalMagnetic_weakCurl (k : ℝ) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (p : CompactPolarization) :
    HasWeakCurl (totalMagnetic k n e p)
      (fun x => (-Complex.I * (k : ℂ)) • (totalElectric k n e p x + p.current x)) := by
  have hei : LocallyIntegrable (incidentWave k n e) volume := (incidentWave_contDiff k n e).continuous.locallyIntegrable
  have hhi : LocallyIntegrable (incidentMagneticWave k n e) volume := (incidentMagneticWave_contDiff k n e).continuous.locallyIntegrable
  have hes := locallySquareIntegrable_locallyIntegrable _ (outgoingElectricField_locallySquareIntegrable k p)
  have hhs := locallySquareIntegrable_locallyIntegrable _ (outgoingMagneticField_locallySquareIntegrable k p)
  have hp := (compactPolarization_current_integrable p).locallyIntegrable
  have h := (incidentMagneticWave_second_weakCurl k n e he).add_fields (outgoingSourceFields_second_weakCurl k p)
    hhi hhs (hei.smul (-Complex.I * (k : ℂ))) ((hes.add hp).smul (-Complex.I * (k : ℂ)))
  convert h using 1 <;> funext x <;> simp [totalElectric, totalMagnetic, smul_add, add_assoc]

structure State (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector) where
  electric : Field
  magnetic : Field
  electric_L2 : LocallySquareIntegrable electric
  magnetic_L2 : LocallySquareIntegrable magnetic
  first_curl : HasWeakCurl electric (fun x => (Complex.I * (k : ℂ)) • magnetic x)
  second_curl : HasWeakCurl magnetic
    (fun x => (-Complex.I * (k : ℂ)) • (electric x + currentField B electric x))
  outgoing : Outgoing (electric - incidentWave k n e) (magnetic - incidentMagneticWave k n e)

def stateOfVolumeEquation (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (p : CompactPolarization)
    (hvol : p.current =ᵐ[volume] currentField B (totalElectric k n e p)) : State B k n e where
  electric := totalElectric k n e p
  magnetic := totalMagnetic k n e p
  electric_L2 := totalElectric_locallySquareIntegrable k n e p
  magnetic_L2 := totalMagnetic_locallySquareIntegrable k n e p
  first_curl := totalElectric_weakCurl k n e p
  second_curl := by
    apply (totalMagnetic_weakCurl k n e he p).congr_ae (ae_of_all _ fun _ => rfl)
    filter_upwards [hvol] with x hx
    rw [hx]
  outgoing := by
    convert outgoingSourceFields_outgoing k p using 1 <;> funext x <;>
      simp [totalElectric, totalMagnetic]

theorem volumeEquation_of_operator (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector)
    (p : DomainL2 B.domain)
    (heq : VolumeInverse.operator B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss k B.radius_nonneg B.subset_ball p =
        domainIncidentSource k n e B.domain B.measurable B.finite) :
    (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p).current =ᵐ[volume]
      currentField B (totalElectric k n e
        (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p)) := by
  let f := domainIncidentSource k n e B.domain B.measurable B.finite
  let K := domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball
  let q := domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p
  have he : TensorMultiplier.inverse volume B.domain B.susceptibility B.measurable_susceptibility
      B.M B.cap B.measurable B.m_pos B.loss p = f + K p := by
    change TensorMultiplier.inverse volume B.domain B.susceptibility B.measurable_susceptibility
      B.M B.cap B.measurable B.m_pos B.loss p - K p = f at heq
    exact sub_eq_iff_eq_add.mp heq
  have hc := TensorMultiplier.inverse_constitutive volume B.domain B.susceptibility
    B.measurable_susceptibility B.M B.cap B.measurable B.m_pos B.loss p
  rw [he] at hc
  filter_upwards [hc, domainPolarization_current_ae B.domain B.measurable B.radius_nonneg B.subset_ball p,
    incidentSource_coe k n e B.domain B.measurable B.finite,
    domainOutgoingOperator_electricVolumeField_ae k B.domain B.measurable B.radius_nonneg B.subset_ball p,
    outgoingElectricField_eq_ae k q, Lp.coeFn_add (f : VectorL2) (K p : VectorL2), p.property]
      with x hχ hp hf hK hout hadd hpd
  change (f : VectorL2) x = B.domain.indicator (incidentWave k n e) x at hf
  change x ∈ B.domain → (K p : VectorL2) x = electricVolumeField k q x at hK
  change q.current x = B.domain.indicator (fun y => B.susceptibility y (totalElectric k n e q y)) x
  rw [hp]
  by_cases hx : x ∈ B.domain
  · rw [indicator_of_mem hx, ← hχ]
    congr 1
    change ((f : VectorL2) + (K p : VectorL2)) x = _
    rw [hadd]
    change (f : VectorL2) x + (K p : VectorL2) x = _
    rw [hf, indicator_of_mem hx, hK hx]
    simp only [totalElectric, hout]
  · rw [indicator_of_notMem hx, hpd hx]

def response (B : Medium) (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector) : DomainL2 B.domain :=
  (VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball).symm
      (domainIncidentSource k n e B.domain B.measurable B.finite)

theorem response_equation (B : Medium) (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector) :
    VolumeInverse.operator B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss k B.radius_nonneg B.subset_ball (response B k hk n e) =
        domainIncidentSource k n e B.domain B.measurable B.finite :=
  (VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball).apply_symm_apply _

theorem operator_of_volumeEquation (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector)
    (p : DomainL2 B.domain)
    (hvol : (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p).current =ᵐ[volume]
      currentField B (totalElectric k n e
        (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p))) :
    VolumeInverse.operator B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss k B.radius_nonneg B.subset_ball p =
        domainIncidentSource k n e B.domain B.measurable B.finite := by
  let f := domainIncidentSource k n e B.domain B.measurable B.finite
  let K := domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball
  let q := domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball p
  have hv : TensorMultiplier.operator volume B.domain B.susceptibility B.measurable_susceptibility
      B.M B.cap (f + K p) = p := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [TensorMultiplier.operator_coe volume B.domain B.susceptibility
        B.measurable_susceptibility B.M B.cap (f + K p), hvol,
      domainPolarization_current_ae B.domain B.measurable B.radius_nonneg B.subset_ball p,
      incidentSource_coe k n e B.domain B.measurable B.finite,
      domainOutgoingOperator_electricVolumeField_ae k B.domain B.measurable B.radius_nonneg B.subset_ball p,
      outgoingElectricField_eq_ae k q, Lp.coeFn_add (f : VectorL2) (K p : VectorL2),
      (f + K p).property, p.property] with x hχ hvolx hpx hfx hKx hout hadd hvs hps
    change (f : VectorL2) x = B.domain.indicator (incidentWave k n e) x at hfx
    change x ∈ B.domain → (K p : VectorL2) x = electricVolumeField k q x at hKx
    rw [hχ]
    by_cases hx : x ∈ B.domain
    · rw [← hpx, hvolx]
      change B.susceptibility x (((f : VectorL2) + (K p : VectorL2)) x) =
        B.domain.indicator (fun y => B.susceptibility y (totalElectric k n e q y)) x
      rw [indicator_of_mem hx, hadd]
      change B.susceptibility x ((f : VectorL2) x + (K p : VectorL2) x) = _
      rw [hfx, indicator_of_mem hx, hKx hx]
      simp only [totalElectric, hout]
    · rw [hvs hx, hps hx, map_zero]
  have he := congrArg (TensorMultiplier.inverse volume B.domain B.susceptibility
    B.measurable_susceptibility B.M B.cap B.measurable B.m_pos B.loss) hv
  rw [TensorMultiplier.inverse_operator] at he
  change TensorMultiplier.inverse volume B.domain B.susceptibility B.measurable_susceptibility
    B.M B.cap B.measurable B.m_pos B.loss p - K p = f
  rw [← he]
  abel

def solution (B : Medium) (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) : State B k n e :=
  stateOfVolumeEquation B k n e he
    (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball (response B k hk n e))
    (volumeEquation_of_operator B k n e (response B k hk n e) (response_equation B k hk n e))

/-- Every independently supplied weak state has the actual outgoing volume representation. -/
theorem state_representation (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (s : State B k n e) :
    let p := polarization B s.electric s.electric_L2
    s.electric =ᵐ[volume] totalElectric k n e p ∧
      s.magnetic =ᵐ[volume] totalMagnetic k n e p := by
  let p := polarization B s.electric s.electric_L2
  let E := s.electric - totalElectric k n e p
  let H := s.magnetic - totalMagnetic k n e p
  have hEs := locallySquareIntegrable_locallyIntegrable _ s.electric_L2
  have hHs := locallySquareIntegrable_locallyIntegrable _ s.magnetic_L2
  have hEv := locallySquareIntegrable_locallyIntegrable _ (totalElectric_locallySquareIntegrable k n e p)
  have hHv := locallySquareIntegrable_locallyIntegrable _ (totalMagnetic_locallySquareIntegrable k n e p)
  have hp := (compactPolarization_current_integrable p).locallyIntegrable
  have hEL : LocallySquareIntegrable E := fun K hK =>
    (s.electric_L2 K hK).sub (totalElectric_locallySquareIntegrable k n e p K hK)
  have hHL : LocallySquareIntegrable H := fun K hK =>
    (s.magnetic_L2 K hK).sub (totalMagnetic_locallySquareIntegrable k n e p K hK)
  have hEcurl : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x) := by
    have h := s.first_curl.sub_fields (totalElectric_weakCurl k n e p) hEs hEv
      (hHs.smul (Complex.I * (k : ℂ))) (hHv.smul (Complex.I * (k : ℂ)))
    convert h using 1
    funext x
    simp [H, smul_sub]
  have hHcurl : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x) := by
    have h := s.second_curl.sub_fields (totalMagnetic_weakCurl k n e he p) hHs hHv
      ((hEs.add hp).smul (-Complex.I * (k : ℂ))) ((hEv.add hp).smul (-Complex.I * (k : ℂ)))
    convert h using 1
    funext x
    change (-Complex.I * (k : ℂ)) • (s.electric x - totalElectric k n e p x) =
      (-Complex.I * (k : ℂ)) • (s.electric x + p.current x) -
        (-Complex.I * (k : ℂ)) • (totalElectric k n e p x + p.current x)
    rw [← smul_sub]
    congr 1
    abel
  have hout : Outgoing E H := by
    have h := s.outgoing.sub_fields (outgoingSourceFields_outgoing k p)
    convert h using 1 <;> funext x <;> simp only [E, H, totalElectric, totalMagnetic, Pi.sub_apply] <;> abel
  have hz := vacuum_outgoing_weak_unique_zero k hk E H hEL hHL hEcurl hHcurl hout
  constructor
  · filter_upwards [hz.1] with x hx
    exact sub_eq_zero.mp hx
  · filter_upwards [hz.2] with x hx
    exact sub_eq_zero.mp hx

theorem outgoingElectric_congr (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) :
    outgoingElectricField k p =ᵐ[volume] outgoingElectricField k q := by
  have he := electricVolumeField_congr_current k p q h
  have hmid : electricVolumeField k p =ᵐ[volume] electricVolumeField k q :=
    ae_of_all _ fun x => congrFun he x
  exact (outgoingElectricField_eq_ae k p).trans
    (hmid.trans (outgoingElectricField_eq_ae k q).symm)

theorem outgoingMagnetic_congr (k : ℝ) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : outgoingMagneticField k p = outgoingMagneticField k q := by
  have hg (j : Fin 3) : gradientPotential k p j = gradientPotential k q j := by
    funext x
    apply integral_congr_ae
    filter_upwards [h] with y hy
    rw [hy]
  funext x
  simp only [outgoingMagneticField, magneticVolumeField, potentialCurlField, hg]

theorem totalElectric_congr (k : ℝ) (n : UnitSphere) (e : Vector) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : totalElectric k n e p =ᵐ[volume] totalElectric k n e q := by
  filter_upwards [outgoingElectric_congr k p q h] with x hx
  simp only [totalElectric, hx]

theorem totalMagnetic_congr (k : ℝ) (n : UnitSphere) (e : Vector) (p q : CompactPolarization)
    (h : p.current =ᵐ[volume] q.current) : totalMagnetic k n e p = totalMagnetic k n e q := by
  funext x
  simp only [totalMagnetic, outgoingMagnetic_congr k p q h]

theorem state_current_response (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (s : State B k n e) :
    currentL2 B s.electric s.electric_L2 = response B k hk n e := by
  let p := polarization B s.electric s.electric_L2
  let r := currentL2 B s.electric s.electric_L2
  let q := domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball r
  have hc : p.current =ᵐ[volume] q.current :=
    (currentL2_coe B s.electric s.electric_L2).symm.trans
      (domainPolarization_current_ae B.domain B.measurable B.radius_nonneg B.subset_ball r).symm
  have hE := (state_representation B hk n e he s).1
  have hEq : s.electric =ᵐ[volume] totalElectric k n e q :=
    hE.trans (totalElectric_congr k n e p q hc)
  have hvol : q.current =ᵐ[volume] currentField B (totalElectric k n e q) := by
    filter_upwards [hc, hEq] with x hpx hEx
    rw [← hpx]
    change currentField B s.electric x = currentField B (totalElectric k n e q) x
    by_cases hx : x ∈ B.domain <;> simp [currentField, hx, hEx]
  let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball
  apply A.injective
  change VolumeInverse.operator B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss k B.radius_nonneg B.subset_ball r =
      A (response B k hk n e)
  rw [show A (response B k hk n e) = domainIncidentSource k n e B.domain B.measurable B.finite by
    exact response_equation B k hk n e]
  exact operator_of_volumeEquation B k n e r hvol

/-- Existence and uniqueness quantify over every original locally finite-energy
weak state, with the full outgoing condition, rather than a selected inverse. -/
theorem wellposed (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) :
    ∃ s : State B k n e, ∀ t : State B k n e,
      t.electric =ᵐ[volume] s.electric ∧ t.magnetic =ᵐ[volume] s.magnetic := by
  refine ⟨solution B k hk n e he, ?_⟩
  intro t
  let p := polarization B t.electric t.electric_L2
  let q := domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball (response B k hk n e)
  have hr := state_current_response B hk n e he t
  have hc : p.current =ᵐ[volume] q.current := by
    have hc := (currentL2_coe B t.electric t.electric_L2).symm
    rw [hr] at hc
    exact hc.trans (domainPolarization_current_ae B.domain B.measurable B.radius_nonneg B.subset_ball _).symm
  have ht := state_representation B hk n e he t
  constructor
  · exact ht.1.trans (totalElectric_congr k n e p q hc)
  · exact ht.2.trans (ae_of_all _ fun x => congrFun (totalMagnetic_congr k n e p q hc) x)

end WeakMaterial
end QuarticMaxwell
