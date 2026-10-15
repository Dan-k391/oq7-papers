import QuarticMaxwell.WeakMaterial
import QuarticMaxwell.UniformBound
import QuarticMaxwell.BallBound
import PrescribedExtinction.PhysicalSphereFlux

/-! The volume powers coincide with the original local material-loss,
incident-work and complete outgoing Poynting cross sections of every weak
Maxwell state. This supplies physical observables for the uniform theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
namespace PhysicalPowers
open MeasureTheory Set OQ7Prescribed WeakMaterial

theorem field_memLp (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    MemLp (B.domain.indicator E) 2 volume :=
  (memLp_indicator_iff_restrict B.measurable).mpr
    ((hE (Metric.closedBall 0 B.radius) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono B.subset_ball le_rfl))

def fieldRestriction (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) : DomainL2 B.domain :=
  ⟨(field_memLp B E hE).toLp (B.domain.indicator E), by
    change ∀ᵐ x ∂volume, x ∉ B.domain →
      ((field_memLp B E hE).toLp (B.domain.indicator E)) x = 0
    filter_upwards [(field_memLp B E hE).coeFn_toLp] with x hx
    intro hd
    rw [hx, indicator_of_notMem hd]⟩

theorem fieldRestriction_coe (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    (fieldRestriction B E hE : VectorL2) =ᵐ[volume] B.domain.indicator E :=
  (field_memLp B E hE).coeFn_toLp

theorem currentL2_multiplier (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    currentL2 B E hE = TensorMultiplier.operator volume B.domain B.susceptibility
      B.measurable_susceptibility B.M B.cap (fieldRestriction B E hE) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [currentL2_coe B E hE, fieldRestriction_coe B E hE,
    TensorMultiplier.operator_coe volume B.domain B.susceptibility
      B.measurable_susceptibility B.M B.cap (fieldRestriction B E hE)] with x hp hf hχ
  rw [hp, hχ, hf]
  by_cases hx : x ∈ B.domain <;> simp [currentField, hx]

theorem inverse_currentL2 (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    VolumeInverse.inverseSusceptibility B.domain B.measurable B.susceptibility
      B.measurable_susceptibility B.M B.cap B.m_pos B.loss (currentL2 B E hE) =
        fieldRestriction B E hE := by
  rw [currentL2_multiplier]
  exact TensorMultiplier.inverse_operator volume B.domain B.susceptibility
    B.measurable_susceptibility B.M B.cap B.measurable B.m_pos B.loss _

theorem field_inner_current (B : Medium) (E : Field) (hE : LocallySquareIntegrable E) :
    inner ℂ (fieldRestriction B E hE) (currentL2 B E hE) =
      ∫ x in B.domain, inner ℂ (E x) (B.susceptibility x (E x)) := by
  change inner ℂ (fieldRestriction B E hE : VectorL2) (currentL2 B E hE : VectorL2) = _
  rw [L2.inner_def, ← integral_indicator B.measurable]
  apply integral_congr_ae
  filter_upwards [fieldRestriction_coe B E hE, currentL2_coe B E hE] with x hf hp
  rw [hf, hp]
  by_cases hx : x ∈ B.domain <;> simp [currentField, hx]

theorem source_inner_current (B : Medium) (E : Field) (hE : LocallySquareIntegrable E)
    (k : ℝ) (n : UnitSphere) (e : Vector) :
    inner ℂ (domainIncidentSource k n e B.domain B.measurable B.finite) (currentL2 B E hE) =
      ∫ x in B.domain, inner ℂ (incidentWave k n e x) (B.susceptibility x (E x)) := by
  change inner ℂ (incidentSource k n e B.domain B.measurable B.finite) (currentL2 B E hE : VectorL2) = _
  rw [L2.inner_def, ← integral_indicator B.measurable]
  apply integral_congr_ae
  filter_upwards [incidentSource_coe k n e B.domain B.measurable B.finite,
    currentL2_coe B E hE] with x hf hp
  rw [hf, hp]
  by_cases hx : x ∈ B.domain <;> simp [currentField, hx]

def absorption (B : Medium) (k : ℝ) (E : Field) : ℝ :=
  k * (∫ x in B.domain, inner ℂ (E x) (B.susceptibility x (E x))).im

def extinction (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector) (E : Field) : ℝ :=
  k * (∫ x in B.domain, inner ℂ (incidentWave k n e x) (B.susceptibility x (E x))).im

def scattering (B : Medium) (k : ℝ) (E : Field) (hE : LocallySquareIntegrable E) : ℝ :=
  ∫ n : UnitSphere, ‖compactCurrentFarField k (polarization B E hE) n‖ ^ 2 ∂sphereArea

theorem absorption_eq_volume (B : Medium) (k : ℝ) (E : Field) (hE : LocallySquareIntegrable E) :
    absorption B k E = UniformBound.absorptionPower k
      (VolumeInverse.inverseSusceptibility B.domain B.measurable B.susceptibility
        B.measurable_susceptibility B.M B.cap B.m_pos B.loss) (currentL2 B E hE) := by
  unfold absorption UniformBound.absorptionPower
  rw [inverse_currentL2 B E hE, ← field_inner_current B E hE]
  have hi := inner_im_symm (𝕜 := ℂ) (fieldRestriction B E hE) (currentL2 B E hE)
  change (inner ℂ (fieldRestriction B E hE) (currentL2 B E hE)).im =
    -(inner ℂ (currentL2 B E hE) (fieldRestriction B E hE)).im at hi
  rw [hi]
  ring

theorem state_absorption (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (s : State B k n e) :
    absorption B k s.electric = UniformBound.absorptionPower k
      (VolumeInverse.inverseSusceptibility B.domain B.measurable B.susceptibility
        B.measurable_susceptibility B.M B.cap B.m_pos B.loss) (response B k hk n e) := by
  rw [absorption_eq_volume B k s.electric s.electric_L2, state_current_response B hk n e he s]

theorem state_extinction (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (s : State B k n e) :
    extinction B k n e s.electric = UniformBound.extinctionPower k
      (VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
        B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball)
      (domainIncidentSource k n e B.domain B.measurable B.finite) := by
  unfold extinction UniformBound.extinctionPower
  rw [← source_inner_current B s.electric s.electric_L2 k n e, state_current_response B hk n e he s]
  have hi := inner_im_symm (𝕜 := ℂ) (domainIncidentSource k n e B.domain B.measurable B.finite)
    (response B k hk n e)
  change (inner ℂ (domainIncidentSource k n e B.domain B.measurable B.finite) (response B k hk n e)).im =
    -(inner ℂ (response B k hk n e) (domainIncidentSource k n e B.domain B.measurable B.finite)).im at hi
  rw [hi]
  unfold response
  ring

theorem scattering_eq_volume (B : Medium) (k : ℝ) (E : Field) (hE : LocallySquareIntegrable E) :
    scattering B k E hE = UniformBound.scatteringPower k
      (domainRadiationMap k B.domain B.measurable B.finite) (currentL2 B E hE) := by
  have hc : (polarization B E hE).current =ᵐ[volume]
      (domainPolarization B.domain B.measurable B.radius_nonneg B.subset_ball (currentL2 B E hE)).current :=
    (currentL2_coe B E hE).symm.trans
      (domainPolarization_current_ae B.domain B.measurable B.radius_nonneg B.subset_ball _).symm
  unfold scattering UniformBound.scatteringPower
  rw [compactCurrentFarField_congr_current k _ _ hc]
  exact domainPolarization_farField_power k B.domain B.measurable B.finite
    B.radius_nonneg B.subset_ball _

theorem scattering_physical_flux (B : Medium) (k : ℝ) (E : Field) (hE : LocallySquareIntegrable E) :
    Filter.Tendsto (exteriorSphereFlux k (polarization B E hE)) Filter.atTop
      (nhds (scattering B k E hE)) := exteriorSphereFlux_tendsto k (polarization B E hE)

def opposite (n : UnitSphere) : UnitSphere :=
  ⟨-(n : Position), by simpa only [mem_sphere_zero_iff_norm, norm_neg] using n.property⟩

theorem opposite_transverse (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) :
    bilinear (complexify (opposite n : Position)) e = 0 := by
  have hh : bilinear (complexify (opposite n : Position)) e =
      -bilinear (complexify (n : Position)) e := by
    simp [opposite, bilinear, complexify, PiLp.neg_apply, Finset.sum_neg_distrib]
  rw [hh, he, neg_zero]

theorem incidentWave_opposite (k : ℝ) (n : UnitSphere) (e : Vector) :
    incidentWave k (opposite n) e = incidentWave (-k) n e := by
  funext x
  unfold incidentWave radiationPhase
  congr 2
  simp only [opposite, Subtype.coe_mk, inner_neg_left, neg_mul, mul_neg]

theorem source_opposite (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector) :
    domainIncidentSource k (opposite n) e B.domain B.measurable B.finite =
      domainIncidentSource (-k) n e B.domain B.measurable B.finite := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [incidentSource_coe k (opposite n) e B.domain B.measurable B.finite,
    incidentSource_coe (-k) n e B.domain B.measurable B.finite] with x hp hm
  change (incidentSource k (opposite n) e B.domain B.measurable B.finite) x =
    (incidentSource (-k) n e B.domain B.measurable B.finite) x
  rw [hp, hm, incidentWave_opposite]

theorem response_opposite (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector) :
    response B k hk (opposite n) e =
      (VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
        B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball).symm
        (domainIncidentSource (-k) n e B.domain B.measurable B.finite) := by
  unfold response
  rw [source_opposite]

/-- The actual local-loss cross sections of every pair of original outgoing
weak states satisfy the full uniform coefficient, with no analytic assumptions. -/
theorem theorem11 (B : Medium) {k : ℝ} (hk : 0 < k)
    (hV : 0 < volume.real B.domain)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (s : State B k n e) (t : State B k (opposite n) e) :
    0 < extinction B k n e s.electric ∧
      |absorption B k s.electric - absorption B k t.electric| / extinction B k n e s.electric ≤
        min 1 (2 / (3 * Real.pi) * (B.M ^ 2 / B.m) ^ 2 *
          (1 / B.m + 1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real B.domain) ^ 2) *
          k ^ 4 * B.radius * volume.real B.domain) := by
  rw [state_absorption B hk n e htr s,
    state_absorption B hk (opposite n) e (opposite_transverse n e htr) t,
    state_extinction B hk n e htr s, response_opposite B hk n e]
  exact UniformBound.uniform_quartic_contrast B.domain B.measurable B.susceptibility
    B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos hsym B.finite hV
    B.radius_nonneg B.subset_ball n e he hen

theorem theorem11_ball (B : Medium) {k : ℝ} (hk : 0 < k)
    (hV : 0 < volume.real B.domain)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (s : State B k n e) (t : State B k (opposite n) e) :
    0 < extinction B k n e s.electric ∧
      |absorption B k s.electric - absorption B k t.electric| / extinction B k n e s.electric ≤
        min 1 (8 / 9 * (B.M ^ 2 / B.m) ^ 2 *
          (1 / B.m + 1 + 3 / 4 * (k * B.radius) ^ 2) * (k * B.radius) ^ 4) := by
  rw [state_absorption B hk n e htr s,
    state_absorption B hk (opposite n) e (opposite_transverse n e htr) t,
    state_extinction B hk n e htr s, response_opposite B hk n e]
  exact UniformBound.uniform_ball_contrast B.domain B.measurable B.susceptibility
    B.measurable_susceptibility B.M B.cap B.m_pos B.loss hk B.M_pos hsym B.finite hV
    B.radius_nonneg B.subset_ball n e he hen

theorem volume_extinction_reciprocal (B : Medium) {k : ℝ} (hk : 0 < k)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) :
    let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball
    UniformBound.extinctionPower k A (domainIncidentSource k n e B.domain B.measurable B.finite) =
      UniformBound.extinctionPower k A (domainIncidentSource (-k) n e B.domain B.measurable B.finite) := by
  let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball
  let f := domainIncidentSource k n e B.domain B.measurable B.finite
  let g := domainIncidentSource (-k) n e B.domain B.measurable B.finite
  have hcw := domain_conjugate_pair_common_work B.domain A
    (VolumeInverse.operator_reciprocity B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss hk hsym B.radius_nonneg B.subset_ball) f
  have hfg : domainConjugate B.domain f = g :=
    domainIncidentSource_conjugate k n e he B.domain B.measurable B.finite
  rw [hfg] at hcw
  have hi := congrArg Complex.im hcw
  have hp := inner_im_symm (𝕜 := ℂ) (A.symm f) f
  have hq := inner_im_symm (𝕜 := ℂ) (A.symm g) g
  change (inner ℂ (A.symm f) f).im = -(inner ℂ f (A.symm f)).im at hp
  change (inner ℂ (A.symm g) g).im = -(inner ℂ g (A.symm g)).im at hq
  change -k * (inner ℂ (A.symm f) f).im = -k * (inner ℂ (A.symm g) g).im
  rw [hp, hq, hi]

theorem state_extinction_reciprocal (B : Medium) {k : ℝ} (hk : 0 < k)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (s : State B k n e) (t : State B k (opposite n) e) :
    extinction B k n e s.electric = extinction B k (opposite n) e t.electric := by
  rw [state_extinction B hk n e htr s,
    state_extinction B hk (opposite n) e (opposite_transverse n e htr) t, source_opposite]
  exact volume_extinction_reciprocal B hk hsym n e he

theorem state_power_balance (B : Medium) {k : ℝ} (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (htr : bilinear (complexify (n : Position)) e = 0) (s : State B k n e) :
    extinction B k n e s.electric = absorption B k s.electric + scattering B k s.electric s.electric_L2 := by
  rw [state_extinction B hk n e htr s, state_absorption B hk n e htr s,
    scattering_eq_volume B k s.electric s.electric_L2, state_current_response B hk n e htr s]
  let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss hk B.M_pos B.finite B.radius_nonneg B.subset_ball
  let W := VolumeInverse.inverseSusceptibility B.domain B.measurable B.susceptibility
    B.measurable_susceptibility B.M B.cap B.m_pos B.loss
  let K := domainOutgoingOperator k B.domain B.measurable B.radius_nonneg B.subset_ball
  let F := domainRadiationMap k B.domain B.measurable B.finite
  let f := domainIncidentSource k n e B.domain B.measurable B.finite
  let p := response B k hk n e
  have heq : W p - K p = f := response_equation B k hk n e
  have hi := congrArg (fun v : DomainL2 B.domain => (inner ℂ p v).im) heq
  simp only [inner_sub_right, Complex.sub_im] at hi
  have hw := domainOutgoingOperator_radiation_work k B.domain B.measurable B.finite
    B.radius_nonneg B.subset_ball p
  change k * (inner ℂ p (K p)).im = k ^ 4 / (16 * Real.pi ^ 2) * ‖F p‖ ^ 2 at hw
  change -k * (inner ℂ p f).im = -k * (inner ℂ p (W p)).im +
    k ^ 4 / (16 * Real.pi ^ 2) * ‖F p‖ ^ 2
  nlinarith

theorem absorption_nonneg (B : Medium) (k : ℝ) (hk : 0 ≤ k) (E : Field)
    (hE : LocallySquareIntegrable E) : 0 ≤ absorption B k E := by
  rw [absorption_eq_volume B k E hE]
  have h := TensorMultiplier.inverse_loss_bound volume B.domain B.susceptibility
    B.measurable_susceptibility B.M B.cap B.measurable B.m_pos B.loss B.M_pos (currentL2 B E hE)
  unfold UniformBound.absorptionPower
  change B.m / B.M ^ 2 * ‖currentL2 B E hE‖ ^ 2 ≤
    -(inner ℂ (currentL2 B E hE) (VolumeInverse.inverseSusceptibility B.domain B.measurable
      B.susceptibility B.measurable_susceptibility B.M B.cap B.m_pos B.loss (currentL2 B E hE))).im at h
  have hh : 0 ≤ -(inner ℂ (currentL2 B E hE) (VolumeInverse.inverseSusceptibility B.domain B.measurable
      B.susceptibility B.measurable_susceptibility B.M B.cap B.m_pos B.loss (currentL2 B E hE))).im :=
    (mul_nonneg (div_nonneg B.m_pos.le (sq_nonneg B.M)) (sq_nonneg _)).trans h
  nlinarith [mul_nonneg hk hh]

theorem scattering_nonneg (B : Medium) (k : ℝ) (E : Field) (hE : LocallySquareIntegrable E) :
    0 ≤ scattering B k E hE := integral_nonneg fun _ => sq_nonneg _

end PhysicalPowers
end QuarticMaxwell
