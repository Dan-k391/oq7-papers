import QuarticMaxwell.RadiationPhysical
import PrescribedExtinction.FarFieldWorkL2

/-! The imaginary-Green radiation identity for every bounded measurable
support. The actual compact-current optical-work theorem is instantiated
after proving equality with the D-masked outgoing operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem supportRestrictionCLM_inner (D : Set Position) (hD : MeasurableSet D)
    (f g : VectorL2) :
    inner ℂ (supportRestrictionCLM D hD f) (supportRestrictionCLM D hD g) =
      inner ℂ (supportRestrictionCLM D hD f) g :=
  setRestrictionCLM_inner volume D hD (setRestrictionCLM volume D hD f) g

theorem supportRestrictionCLM_compactRestrictionLp (D : Set Position) (hD : MeasurableSet D)
    {R : ℝ} (hsub : D ⊆ Metric.closedBall (0 : Position) R) (g : VectorL2) :
    supportRestrictionCLM D hD (compactRestrictionLp R g) = supportRestrictionCLM D hD g := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe volume D hD (compactRestrictionLp R g),
    indicatorL2_coe volume D hD g, compactRestrictionLp_coe R g] with x hl hr hb
  change indicatorL2 volume D hD (compactRestrictionLp R g) x = indicatorL2 volume D hD g x
  rw [hl, hr]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx]
    rw [hb, indicator_of_mem (hsub hx)]
  · simp [hx]

theorem maskedOutgoingOperator_eq_restriction (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    maskedOutgoingOperator k D hD hR hsub f =
      supportRestrictionCLM D hD
        (compactOutgoingOperator k R hR (supportInputCLM D hD hsub f) : VectorL2) := by
  change supportRestrictionCLM D hD (staticFourierOperator (supportRestrictionCLM D hD f)) +
      supportRestrictionCLM D hD
        (compactRemainderOperator k R hR (supportInputCLM D hD hsub f) : VectorL2) =
    supportRestrictionCLM D hD
      ((compactStaticOperator R (supportInputCLM D hD hsub f) : VectorL2) +
       (compactRemainderOperator k R hR (supportInputCLM D hD hsub f) : VectorL2))
  rw [map_add]
  congr 1
  exact (supportRestrictionCLM_compactRestrictionLp D hD hsub
    (staticFourierOperator (supportRestrictionCLM D hD f))).symm

theorem maskedOutgoingOperator_inner_eq_compact (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    inner ℂ (supportRestrictionCLM D hD f) (maskedOutgoingOperator k D hD hR hsub f) =
      inner ℂ (supportInputCLM D hD hsub f)
        (compactOutgoingOperator k R hR (supportInputCLM D hD hsub f)) := by
  rw [maskedOutgoingOperator_eq_restriction, supportRestrictionCLM_inner]
  rfl

theorem maskedOutgoingOperator_radiation_work (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    k * (inner ℂ (supportRestrictionCLM D hD f)
      (maskedOutgoingOperator k D hD hR hsub f)).im =
        k ^ 4 / (16 * Real.pi ^ 2) * ‖radiationMap k D hD hfin f‖ ^ 2 := by
  let p := supportedPolarization R hR (supportInputCLM D hD hsub f)
  have hp : p.toSupportedLp R (by rfl) = supportInputCLM D hD hsub f := by
    apply Subtype.ext
    exact supportedPolarization_toLp R hR _
  have h := physicalOutgoingVolume_farField_work k p
  rw [← compactCurrent_outgoingOperator_inner k R hR p (by rfl), hp] at h
  rw [maskedOutgoingOperator_inner_eq_compact]
  exact h.trans (compactCurrentFarField_power_eq k D hD hfin hR hsub f)

theorem maskedOutgoingOperator_imaginary_radiation {k : ℝ} (hk : 0 < k)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    (inner ℂ (supportRestrictionCLM D hD f) (maskedOutgoingOperator k D hD hR hsub f)).im =
      k ^ 3 / (16 * Real.pi ^ 2) * ‖radiationMap k D hD hfin f‖ ^ 2 := by
  have h := maskedOutgoingOperator_radiation_work k D hD hfin hR hsub f
  apply (mul_left_cancel₀ hk.ne')
  rw [h]
  ring

theorem maskedOutgoingOperator_im_nonneg {k : ℝ} (hk : 0 < k)
    (D : Set Position) (hD : MeasurableSet D) (hfin : volume D ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : VectorL2) :
    0 ≤ (inner ℂ (supportRestrictionCLM D hD f)
      (maskedOutgoingOperator k D hD hR hsub f)).im := by
  rw [maskedOutgoingOperator_imaginary_radiation hk D hD hfin hR hsub]
  positivity

theorem maskedStaticOperator_quadratic_im (D : Set Position) (hD : MeasurableSet D)
    (f : VectorL2) :
    (inner ℂ (supportRestrictionCLM D hD f) (maskedStaticOperator D hD f)).im = 0 := by
  change (inner ℂ (supportRestrictionCLM D hD f)
    (supportRestrictionCLM D hD (staticFourierOperator (supportRestrictionCLM D hD f)))).im = 0
  rw [supportRestrictionCLM_inner]
  exact staticFourierOperator_quadratic_im _

end QuarticMaxwell
