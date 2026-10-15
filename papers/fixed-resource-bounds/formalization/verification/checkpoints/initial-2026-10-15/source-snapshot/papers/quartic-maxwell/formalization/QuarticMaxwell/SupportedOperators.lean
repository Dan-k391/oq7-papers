import QuarticMaxwell.Reciprocity

/-! The actual support-restricted Hilbert space used by the arbitrary tensor
multiplier. All operators are restrictions of the genuine masked operators;
their sharp estimates and optical/reciprocal identities are inherited by
proved equality of their zero extensions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

abbrev DomainL2 (D : Set Position) := SetSupportedL2 (E := Vector) volume D

theorem domainCompleteSpace (D : Set Position) (hD : MeasurableSet D) : CompleteSpace (DomainL2 D) :=
  (setSupportedL2_isClosed volume D hD).completeSpace_coe

theorem supportRestrictionCLM_eq_self (D : Set Position) (hD : MeasurableSet D)
    (f : DomainL2 D) : supportRestrictionCLM D hD (f : VectorL2) = (f : VectorL2) :=
  (indicatorL2_eq_self_iff volume D hD (f : VectorL2)).mpr f.property

theorem supportRestrictionCLM_idempotent (D : Set Position) (hD : MeasurableSet D)
    (f : VectorL2) : supportRestrictionCLM D hD (supportRestrictionCLM D hD f) =
      supportRestrictionCLM D hD f :=
  (indicatorL2_eq_self_iff volume D hD _).mpr (indicatorL2_supported volume D hD f)

theorem supportRestrictionCLM_maskedStatic (D : Set Position) (hD : MeasurableSet D)
    (f : VectorL2) : supportRestrictionCLM D hD (maskedStaticOperator D hD f) =
      maskedStaticOperator D hD f :=
  supportRestrictionCLM_idempotent D hD _

theorem supportRestrictionCLM_maskedOutgoing (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    supportRestrictionCLM D hD (maskedOutgoingOperator k D hD hR hsub f) =
      maskedOutgoingOperator k D hD hR hsub f := by
  change supportRestrictionCLM D hD
      (maskedStaticOperator D hD f + maskedRemainderOperator k D hD hR hsub f) = _
  rw [map_add, supportRestrictionCLM_maskedStatic]
  change maskedStaticOperator D hD f +
      supportRestrictionCLM D hD (supportRestrictionCLM D hD
        (compactRemainderOperator k R hR (supportInputCLM D hD hsub f) : VectorL2)) = _
  rw [supportRestrictionCLM_idempotent]
  rfl

def domainStaticOperator (D : Set Position) (hD : MeasurableSet D) :
    DomainL2 D →L[ℂ] DomainL2 D :=
  setRestrictionCLM volume D hD ∘L maskedStaticOperator D hD ∘L
    (setSupportedL2 (E := Vector) volume D).subtypeL

theorem domainStaticOperator_coe (D : Set Position) (hD : MeasurableSet D) (f : DomainL2 D) :
    (domainStaticOperator D hD f : VectorL2) = maskedStaticOperator D hD (f : VectorL2) :=
  supportRestrictionCLM_maskedStatic D hD _

def domainOutgoingOperator (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    DomainL2 D →L[ℂ] DomainL2 D :=
  setRestrictionCLM volume D hD ∘L maskedOutgoingOperator k D hD hR hsub ∘L
    (setSupportedL2 (E := Vector) volume D).subtypeL

theorem domainOutgoingOperator_coe (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    (domainOutgoingOperator k D hD hR hsub f : VectorL2) =
      maskedOutgoingOperator k D hD hR hsub (f : VectorL2) :=
  supportRestrictionCLM_maskedOutgoing k D hD hR hsub _

theorem domainStaticOperator_norm_le (D : Set Position) (hD : MeasurableSet D) :
    ‖domainStaticOperator D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖(domainStaticOperator D hD f : VectorL2)‖ ≤ 1 * ‖(f : VectorL2)‖
  rw [domainStaticOperator_coe]
  exact ((maskedStaticOperator D hD).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (maskedStaticOperator_norm_le D hD) (norm_nonneg _))

theorem domainOutgoingOperator_difference_norm_le {k : ℝ} (hk : 0 ≤ k)
    (D : Set Position) (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (hV : 0 < volume.real D) :
    ‖domainOutgoingOperator k D hD hR hsub - domainStaticOperator D hD‖ ≤
      3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖((domainOutgoingOperator k D hD hR hsub f : VectorL2) -
      (domainStaticOperator D hD f : VectorL2))‖ ≤ _
  rw [domainOutgoingOperator_coe, domainStaticOperator_coe, ← sub_apply]
  exact ((maskedOutgoingOperator k D hD hR hsub - maskedStaticOperator D hD).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right
      (maskedOutgoingOperator_difference_norm_le_volume hk D hD hR hsub hV) (norm_nonneg _))

def domainRadiationMap (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) : DomainL2 D →L[ℂ] Lp Vector 2 sphereArea :=
  radiationMap k D hD hfin ∘L (setSupportedL2 (E := Vector) volume D).subtypeL

theorem domainRadiationMap_norm_sq_le (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) : ‖domainRadiationMap k D hD hfin‖ ^ 2 ≤ 8 * Real.pi * volume.real D / 3 := by
  have hnorm : ‖domainRadiationMap k D hD hfin‖ ≤ ‖radiationMap k D hD hfin‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    exact (radiationMap k D hD hfin).le_opNorm (f : VectorL2)
  have hbound := radiationMap_norm_sq_le k D hD hfin
  nlinarith [norm_nonneg (domainRadiationMap k D hD hfin), norm_nonneg (radiationMap k D hD hfin)]

theorem domainOutgoingOperator_radiation_work (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    k * (inner ℂ f (domainOutgoingOperator k D hD hR hsub f)).im =
      k ^ 4 / (16 * Real.pi ^ 2) * ‖domainRadiationMap k D hD hfin f‖ ^ 2 := by
  have h := maskedOutgoingOperator_radiation_work k D hD hfin hR hsub (f : VectorL2)
  rw [supportRestrictionCLM_eq_self D hD f] at h
  change k * (inner ℂ (f : VectorL2) (domainOutgoingOperator k D hD hR hsub f : VectorL2)).im = _
  rw [domainOutgoingOperator_coe]
  exact h

theorem domainOutgoingOperator_im_nonneg {k : ℝ} (hk : 0 < k) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    0 ≤ (inner ℂ f (domainOutgoingOperator k D hD hR hsub f)).im := by
  have h := maskedOutgoingOperator_im_nonneg hk D hD hfin hR hsub (f : VectorL2)
  rw [supportRestrictionCLM_eq_self D hD f] at h
  change 0 ≤ (inner ℂ (f : VectorL2) (domainOutgoingOperator k D hD hR hsub f : VectorL2)).im
  rw [domainOutgoingOperator_coe]
  exact h

theorem domainStaticOperator_quadratic_im (D : Set Position) (hD : MeasurableSet D)
    (f : DomainL2 D) : (inner ℂ f (domainStaticOperator D hD f)).im = 0 := by
  have h := maskedStaticOperator_quadratic_im D hD (f : VectorL2)
  rw [supportRestrictionCLM_eq_self D hD f] at h
  change (inner ℂ (f : VectorL2) (domainStaticOperator D hD f : VectorL2)).im = 0
  rw [domainStaticOperator_coe]
  exact h

theorem conjugateL2_norm_le (f : VectorL2) : ‖conjugateL2 f‖ ≤ ‖f‖ := by
  apply (vectorConjugateCLM.norm_compLp_le f).trans
  exact (mul_le_mul_of_nonneg_right vectorConjugateCLM_norm_le (norm_nonneg _)).trans_eq (one_mul _)

def domainConjugateLinear (D : Set Position) : DomainL2 D →ₗ[ℝ] DomainL2 D where
  toFun f := ⟨conjugateL2 (f : VectorL2), by
    change ∀ᵐ x ∂volume, x ∉ D → (conjugateL2 (f : VectorL2)) x = 0
    filter_upwards [conjugateL2_coe (f : VectorL2), f.property] with x hx hf
    intro hxd
    rw [hx, hf hxd]
    ext i
    simp [vectorConjugate_apply]⟩
  map_add' f g := Subtype.ext (map_add conjugateL2 _ _)
  map_smul' r f := Subtype.ext (map_smul conjugateL2 r _)

def domainConjugate (D : Set Position) : DomainL2 D →L[ℝ] DomainL2 D :=
  (domainConjugateLinear D).mkContinuous 1 fun f => by
    change ‖conjugateL2 (f : VectorL2)‖ ≤ 1 * ‖(f : VectorL2)‖
    simpa using conjugateL2_norm_le (f : VectorL2)

theorem domainConjugate_coe (D : Set Position) (f : DomainL2 D) :
    (domainConjugate D f : VectorL2) = conjugateL2 (f : VectorL2) := rfl

theorem domainConjugate_involutive (D : Set Position) (f : DomainL2 D) :
    domainConjugate D (domainConjugate D f) = f :=
  Subtype.ext (conjugateL2_involutive (f : VectorL2))

theorem domainConjugate_pairing_comm (D : Set Position) (f g : DomainL2 D) :
    inner ℂ (domainConjugate D f) g = inner ℂ (domainConjugate D g) f :=
  conjugateL2_pairing_comm (f : VectorL2) (g : VectorL2)

theorem domainOutgoingOperator_reciprocity {k : ℝ} (hk : 0 < k) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f g : DomainL2 D) :
    inner ℂ (domainConjugate D f) (domainOutgoingOperator k D hD hR hsub g) =
      inner ℂ (domainConjugate D g) (domainOutgoingOperator k D hD hR hsub f) := by
  have h := maskedOutgoingOperator_reciprocity hk D hD hR hsub (f : VectorL2) (g : VectorL2)
  rw [supportRestrictionCLM_eq_self D hD f, supportRestrictionCLM_eq_self D hD g] at h
  change inner ℂ (conjugateL2 (f : VectorL2)) (domainOutgoingOperator k D hD hR hsub g : VectorL2) =
    inner ℂ (conjugateL2 (g : VectorL2)) (domainOutgoingOperator k D hD hR hsub f : VectorL2)
  rw [domainOutgoingOperator_coe, domainOutgoingOperator_coe]
  exact h

theorem incidentSource_supported (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    incidentSource k n e D hD hfin ∈ setSupportedL2 (E := Vector) volume D := by
  filter_upwards [incidentSource_coe k n e D hD hfin] with x hx
  intro hxd
  rw [hx, indicator_of_notMem hxd]

def domainIncidentSource (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) : DomainL2 D :=
  ⟨incidentSource k n e D hD hfin, incidentSource_supported k n e D hD hfin⟩

theorem domainIncidentSource_norm_sq (k : ℝ) (n : UnitSphere) (e : Vector)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    ‖domainIncidentSource k n e D hD hfin‖ ^ 2 = volume.real D * ‖e‖ ^ 2 :=
  incidentSource_norm_sq k n e D hD hfin

theorem domainIncidentSource_opposite_norm_sq (k : ℝ) (hk : 0 ≤ k) (n : UnitSphere)
    (e : Vector) (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖domainIncidentSource k n e D hD hfin - domainIncidentSource (-k) n e D hD hfin‖ ^ 2 ≤
      4 * k ^ 2 * R ^ 2 * volume.real D * ‖e‖ ^ 2 :=
  incidentSource_opposite_norm_sq k hk n e D hD hfin hR hsub

theorem domainIncidentSource_conjugate (k : ℝ) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) :
    domainConjugate D (domainIncidentSource k n e D hD hfin) = domainIncidentSource (-k) n e D hD hfin :=
  Subtype.ext (incidentSource_conjugate k n e he D hD hfin)

theorem domain_inverse_bilinear_reciprocity (D : Set Position) (A : DomainL2 D ≃L[ℂ] DomainL2 D)
    (hA : ∀ p q, inner ℂ (domainConjugate D p) (A q) = inner ℂ (domainConjugate D q) (A p))
    (f g : DomainL2 D) :
    inner ℂ (domainConjugate D f) (A.symm g) = inner ℂ (domainConjugate D g) (A.symm f) := by
  have h := hA (A.symm f) (A.symm g)
  rw [A.apply_symm_apply, A.apply_symm_apply] at h
  rw [domainConjugate_pairing_comm D f, domainConjugate_pairing_comm D g]
  exact h.symm

theorem domain_conjugate_pair_common_work (D : Set Position) (A : DomainL2 D ≃L[ℂ] DomainL2 D)
    (hA : ∀ p q, inner ℂ (domainConjugate D p) (A q) = inner ℂ (domainConjugate D q) (A p))
    (f : DomainL2 D) :
    inner ℂ f (A.symm f) = inner ℂ (domainConjugate D f) (A.symm (domainConjugate D f)) := by
  have h := domain_inverse_bilinear_reciprocity D A hA f (domainConjugate D f)
  rw [domainConjugate_involutive] at h
  exact h.symm

def domainPolarization (D : Set Position) (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) : CompactPolarization :=
  supportedPolarization R hR (supportInputCLM D hD hsub (f : VectorL2))

theorem domainPolarization_current_ae (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    (domainPolarization D hD hR hsub f).current =ᵐ[volume] (f : VectorL2) := by
  have h := supportedPolarization_current_ae R hR (supportInputCLM D hD hsub (f : VectorL2))
  have he : (supportInputCLM D hD hsub (f : VectorL2) : VectorL2) = (f : VectorL2) :=
    supportRestrictionCLM_eq_self D hD f
  simpa only [domainPolarization, he] using h

theorem domainPolarization_toLp (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    (domainPolarization D hD hR hsub f).memLp.toLp (domainPolarization D hD hR hsub f).current =
      (f : VectorL2) := by
  rw [domainPolarization, supportedPolarization_toLp]
  exact supportRestrictionCLM_eq_self D hD f

theorem domainOutgoingOperator_electricVolumeField_ae (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    ∀ᵐ x ∂volume, x ∈ D → (domainOutgoingOperator k D hD hR hsub f : VectorL2) x =
      electricVolumeField k (domainPolarization D hD hR hsub f) x := by
  let p := domainPolarization D hD hR hsub f
  let q := (compactOutgoingOperator k R hR (supportInputCLM D hD hsub (f : VectorL2)) : VectorL2)
  have hp : p.toSupportedLp R (by rfl) = supportInputCLM D hD hsub (f : VectorL2) := by
    apply Subtype.ext
    exact supportedPolarization_toLp R hR _
  have hc := compactCurrent_outgoingOperator_coe k R hR p (by rfl)
  rw [hp] at hc
  have heq : (domainOutgoingOperator k D hD hR hsub f : VectorL2) =
      supportRestrictionCLM D hD q :=
    (domainOutgoingOperator_coe k D hD hR hsub f).trans
      (maskedOutgoingOperator_eq_restriction k D hD hR hsub (f : VectorL2))
  filter_upwards [hc, indicatorL2_coe volume D hD q] with x hcompact hmask
  intro hxD
  rw [heq]
  change indicatorL2 volume D hD q x = _
  rw [hmask, indicator_of_mem hxD]
  change (compactOutgoingOperator k R hR (supportInputCLM D hD hsub (f : VectorL2)) : VectorL2) x = _
  rw [hcompact, indicator_of_mem (hsub hxD)]

theorem domainPolarization_farField_power (k : ℝ) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    (∫ n : UnitSphere, ‖compactCurrentFarField k (domainPolarization D hD hR hsub f) n‖ ^ 2 ∂sphereArea) =
      k ^ 4 / (16 * Real.pi ^ 2) * ‖domainRadiationMap k D hD hfin f‖ ^ 2 :=
  compactCurrentFarField_power_eq k D hD hfin hR hsub (f : VectorL2)

end QuarticMaxwell
