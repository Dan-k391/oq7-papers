import QuarticMaxwell.RadiationIdentity
import QuarticMaxwell.IncidentSources
import PrescribedExtinction.ReciprocityL2

/-! Genuine measurable-support Green reciprocity and its common-inverse
consequence. Material transpose symmetry must separately be supplied for the
assembled volume operator; it is not inferred from passivity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

def conjugateL2 : VectorL2 →L[ℝ] VectorL2 := vectorConjugateCLM.compLpL 2 volume

theorem conjugateL2_coe (f : VectorL2) :
    conjugateL2 f =ᵐ[volume] fun x => vectorConjugate (f x) :=
  vectorConjugateCLM.coeFn_compLp _

theorem conjugateL2_involutive (f : VectorL2) : conjugateL2 (conjugateL2 f) = f := by
  apply Lp.ext
  filter_upwards [conjugateL2_coe (conjugateL2 f), conjugateL2_coe f] with x ho hi
  rw [ho, hi]
  ext i
  simp [vectorConjugate_apply]

theorem conjugateL2_restriction (D : Set Position) (hD : MeasurableSet D) (f : VectorL2) :
    conjugateL2 (supportRestrictionCLM D hD f) = supportRestrictionCLM D hD (conjugateL2 f) := by
  apply Lp.ext
  filter_upwards [conjugateL2_coe (supportRestrictionCLM D hD f),
    indicatorL2_coe volume D hD f, indicatorL2_coe volume D hD (conjugateL2 f),
    conjugateL2_coe f] with x hc hm hr hf
  change (conjugateL2 (supportRestrictionCLM D hD f)) x = indicatorL2 volume D hD (conjugateL2 f) x
  rw [hc, hr]
  change vectorConjugate (indicatorL2 volume D hD f x) = _
  rw [hm]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx, hf]
  · simp only [indicator_of_notMem hx]
    ext i
    simp [vectorConjugate_apply]

theorem supportedConjugate_input (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    (supportedVectorConjugate R (supportInputCLM D hD hsub f) : VectorL2) =
      conjugateL2 (supportRestrictionCLM D hD f) := by
  apply Lp.ext
  filter_upwards [supportedVectorConjugate_coe R (supportInputCLM D hD hsub f),
    conjugateL2_coe (supportRestrictionCLM D hD f)] with x hs hc
  rw [hs, hc]
  rfl

theorem maskedOutgoingOperator_bilinear_eq_compact (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f g : VectorL2) :
    inner ℂ (conjugateL2 (supportRestrictionCLM D hD f)) (maskedOutgoingOperator k D hD hR hsub g) =
      inner ℂ (supportedVectorConjugate R (supportInputCLM D hD hsub f))
        (compactOutgoingOperator k R hR (supportInputCLM D hD hsub g)) := by
  rw [maskedOutgoingOperator_eq_restriction, conjugateL2_restriction,
    supportRestrictionCLM_inner]
  rw [← conjugateL2_restriction, ← supportedConjugate_input D hD hsub]
  rfl

theorem maskedOutgoingOperator_reciprocity {k : ℝ} (hk : 0 < k) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f g : VectorL2) :
    inner ℂ (conjugateL2 (supportRestrictionCLM D hD f)) (maskedOutgoingOperator k D hD hR hsub g) =
      inner ℂ (conjugateL2 (supportRestrictionCLM D hD g)) (maskedOutgoingOperator k D hD hR hsub f) := by
  let p := supportedPolarization R hR (supportInputCLM D hD hsub f)
  let q := supportedPolarization R hR (supportInputCLM D hD hsub g)
  have hp : p.toSupportedLp R (by rfl) = supportInputCLM D hD hsub f := by
    apply Subtype.ext
    exact supportedPolarization_toLp R hR _
  have hq : q.toSupportedLp R (by rfl) = supportInputCLM D hD hsub g := by
    apply Subtype.ext
    exact supportedPolarization_toLp R hR _
  have h := physicalOutgoingVolume_reciprocity k hk p q
  rw [← compactCurrents_outgoingOperator_bilinear k R hR p q (by rfl) (by rfl),
    ← compactCurrents_outgoingOperator_bilinear k R hR q p (by rfl) (by rfl), hp, hq] at h
  rw [maskedOutgoingOperator_bilinear_eq_compact, maskedOutgoingOperator_bilinear_eq_compact]
  exact h

theorem conjugateL2_pairing_comm (f g : VectorL2) :
    inner ℂ (conjugateL2 f) g = inner ℂ (conjugateL2 g) f := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [conjugateL2_coe f, conjugateL2_coe g] with x hf hg
  rw [hf, hg, ← bilinear_eq_conjugate_inner, ← bilinear_eq_conjugate_inner]
  exact bilinear_comm _ _

theorem inverse_bilinear_reciprocity (A : VectorL2 ≃L[ℂ] VectorL2)
    (hA : ∀ p q, inner ℂ (conjugateL2 p) (A q) = inner ℂ (conjugateL2 q) (A p))
    (f g : VectorL2) :
    inner ℂ (conjugateL2 f) (A.symm g) = inner ℂ (conjugateL2 g) (A.symm f) := by
  have h := hA (A.symm f) (A.symm g)
  rw [A.apply_symm_apply, A.apply_symm_apply] at h
  rw [conjugateL2_pairing_comm f, conjugateL2_pairing_comm g]
  exact h.symm

theorem conjugate_pair_common_work (A : VectorL2 ≃L[ℂ] VectorL2)
    (hA : ∀ p q, inner ℂ (conjugateL2 p) (A q) = inner ℂ (conjugateL2 q) (A p))
    (f : VectorL2) :
    inner ℂ f (A.symm f) = inner ℂ (conjugateL2 f) (A.symm (conjugateL2 f)) := by
  have h := inverse_bilinear_reciprocity A hA f (conjugateL2 f)
  rw [conjugateL2_involutive] at h
  exact h.symm

theorem radiationPhase_conjugate (k : ℝ) (n : UnitSphere) (x : Position) :
    star (radiationPhase k n x) = radiationPhase (-k) n x := by
  unfold radiationPhase
  rw [show star (Complex.exp (-Complex.I * ((k * inner ℝ (n : Position) x : ℝ) : ℂ))) =
    Complex.exp (star (-Complex.I * ((k * inner ℝ (n : Position) x : ℝ) : ℂ))) by
      exact (Complex.exp_conj _).symm]
  congr 1
  simp

theorem incidentSource_conjugate (k : ℝ) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (D : Set Position) (hD : MeasurableSet D)
    (hfin : volume D ≠ ⊤) :
    conjugateL2 (incidentSource k n e D hD hfin) = incidentSource (-k) n e D hD hfin := by
  apply Lp.ext
  filter_upwards [conjugateL2_coe (incidentSource k n e D hD hfin),
    incidentSource_coe k n e D hD hfin,
    incidentSource_coe (-k) n e D hD hfin] with x hc hp hm
  rw [hc, hp, hm]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx, incidentWave, vectorConjugate_smul, he, radiationPhase_conjugate]
  · simp only [indicator_of_notMem hx]
    ext i
    simp [vectorConjugate_apply]

end QuarticMaxwell
