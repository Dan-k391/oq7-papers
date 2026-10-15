import QuarticMaxwell.TwoSupportStatic
import QuarticMaxwell.BlockResolvent

/-! Quantitative resolvent bounds for the actual two-support scalar medium.
All cross norms and the common-inverse interaction identity are derived from
literal measurable susceptibility and the physical static Fourier operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell.TwoSupportBounds
open OQ7Prescribed TwoSupportStatic SupportBlocks StaticCrossIdentification MeasureTheory Set

def crossBound (D E : Set OQ7Prescribed.Position) (d : ℝ) : ℝ :=
  Real.sqrt (volume.real D * volume.real E) / (2 * Real.pi * d ^ 3)

theorem crossBound_nonneg (D E : Set OQ7Prescribed.Position) {d : ℝ} (hd : 0 < d) :
    0 ≤ crossBound D E d := by unfold crossBound; positivity

theorem gap_disjoint (D E : Set OQ7Prescribed.Position) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ D, ∀ y ∈ E, d ≤ ‖x - y‖) : Disjoint D E := by
  apply Set.disjoint_left.mpr
  intro x hx he
  have h := hgap x hx x he
  simp only [sub_self, norm_zero] at h
  exact (not_le_of_gt hd) h

variable (D E : Set OQ7Prescribed.Position) (hD : IsOpen D) (hE : IsOpen E)
  (hfinD : volume D ≠ ⊤) (hfinE : volume E ≠ ⊤)
  {R1 R2 : ℝ} (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2)
  (hsubD : D ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R1)
  (hsubE : E ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R2)
  (d : ℝ) (hd : 0 < d) (hgap : ∀ x ∈ D, ∀ y ∈ E, d ≤ ‖x - y‖)

include hfinD hfinE hR1 hR2 hsubD hsubE hd hgap in
theorem interaction_norm_le :
    ‖interaction D E hD.measurableSet hE.measurableSet‖ ≤ crossBound D E d := by
  apply offDiagonal_norm_le D E hD.measurableSet hE.measurableSet
    (gap_disjoint D E hd hgap) _ _ (crossBound_nonneg D E hd)
  · exact staticCrossBlock_norm_le D E hD hE.measurableSet hfinD hfinE hR2 hsubE d hd hgap
  · have hrev : ∀ x ∈ E, ∀ y ∈ D, d ≤ ‖x - y‖ := by
      intro x hx y hy
      simpa only [norm_sub_rev] using hgap y hy x hx
    have h := staticCrossBlock_norm_le E D hE hD.measurableSet hfinE hfinD hR1 hsubD d hd hrev
    simpa only [crossBound, mul_comm] using h

def isolatedRho (P : ScalarPair) : ℝ :=
  max (‖P.left‖ ^ 2 / P.left.im) (‖P.right‖ ^ 2 / P.right.im)

theorem isolatedRho_pos (P : ScalarPair) : 0 < isolatedRho P := by
  have hp : 0 < ‖P.left‖ ^ 2 / P.left.im := div_pos (sq_pos_of_pos (SphereResponse.scalar_norm_pos P.left_loss)) P.left_loss
  exact lt_of_lt_of_le hp (le_max_left _ _)

theorem isolatedEquiv_inverse_norm_le (U : Set OQ7Prescribed.Position) (hU : MeasurableSet U)
    (χ : ℂ) (hχ : 0 < χ.im) :
    ‖(isolatedEquiv U hU χ hχ).symm.toContinuousLinearMap‖ ≤ ‖χ‖ ^ 2 / χ.im :=
  StaticInverse.inverse_norm_le U hU (SphereResponse.scalarSusceptibility χ)
    (SphereResponse.scalar_measurable χ) ‖χ‖ (SphereResponse.scalar_cap χ U) hχ
    (SphereResponse.scalar_loss χ U) (SphereResponse.scalar_norm_pos hχ)

include hd hgap in
theorem blockInverse_norm_le (P : ScalarPair) :
    ‖blockInverse D E hD.measurableSet hE.measurableSet P‖ ≤ isolatedRho P := by
  apply diagonal_norm_le D E hD.measurableSet hE.measurableSet (gap_disjoint D E hd hgap)
    _ _ (isolatedRho_pos P).le
  · exact (isolatedEquiv_inverse_norm_le D hD.measurableSet P.left P.left_loss).trans (le_max_left _ _)
  · exact (isolatedEquiv_inverse_norm_le E hE.measurableSet P.right P.right_loss).trans (le_max_right _ _)

def response (P : ScalarPair) : DomainL2 (D ∪ E) →L[ℂ] DomainL2 (D ∪ E) :=
  (equiv D E hD.measurableSet hE.measurableSet P).symm.toContinuousLinearMap

include hd hgap in
theorem response_identity (P : ScalarPair) :
    response D E hD hE P = blockInverse D E hD.measurableSet hE.measurableSet P +
      blockInverse D E hD.measurableSet hE.measurableSet P ∘L
        interaction D E hD.measurableSet hE.measurableSet ∘L response D E hD hE P := by
  apply BlockResolvent.identity_of_apply
  exact inverse_interaction_identity D E hD.measurableSet hE.measurableSet (gap_disjoint D E hd hgap) P

include hfinD hfinE hR1 hR2 hsubD hsubE hd hgap in
theorem response_norm_le (P : ScalarPair) (hsmall : isolatedRho P * crossBound D E d < 1) :
    ‖response D E hD hE P‖ ≤ isolatedRho P / (1 - isolatedRho P * crossBound D E d) :=
  BlockResolvent.inverse_norm_le _ _ _ (isolatedRho_pos P).le (crossBound_nonneg D E hd)
    (blockInverse_norm_le D E hD hE d hd hgap P)
    (interaction_norm_le D E hD hE hfinD hfinE hR1 hR2 hsubD hsubE d hd hgap) hsmall
    (response_identity D E hD hE d hd hgap P)

include hfinD hfinE hR1 hR2 hsubD hsubE hd hgap in
theorem response_difference_norm_le (P : ScalarPair) (hsmall : isolatedRho P * crossBound D E d < 1) :
    ‖response D E hD hE P - blockInverse D E hD.measurableSet hE.measurableSet P‖ ≤
      (isolatedRho P) ^ 2 * crossBound D E d / (1 - isolatedRho P * crossBound D E d) :=
  BlockResolvent.inverse_difference_norm_le _ _ _ (isolatedRho_pos P).le (crossBound_nonneg D E hd)
    (blockInverse_norm_le D E hD hE d hd hgap P)
    (interaction_norm_le D E hD hE hfinD hfinE hR1 hR2 hsubD hsubE d hd hgap) hsmall
    (response_identity D E hD hE d hd hgap P)

theorem response_resource_norm_le (P : ScalarPair) :
    ‖response D E hD hE P‖ ≤ P.cap ^ 2 / P.loss :=
  StaticInverse.inverse_norm_le (D ∪ E) (hD.measurableSet.union hE.measurableSet)
    (susceptibility D P) (susceptibility_measurable D hD.measurableSet P) P.cap
    (susceptibility_cap D E P) P.loss_pos (susceptibility_loss D E P) P.cap_pos

end QuarticMaxwell.TwoSupportBounds

namespace QuarticMaxwell.TwoSupportBounds
open OQ7Prescribed TwoSupportStatic SupportBlocks StaticCrossIdentification MeasureTheory Set

def homogeneousPair (μ : ℝ) (hμ : 0 < μ) : ScalarPair where
  left := Complex.I * (μ : ℂ)
  right := Complex.I * (μ : ℂ)
  left_loss := by simpa using hμ
  right_loss := by simpa using hμ

theorem homogeneous_cap (μ : ℝ) (hμ : 0 < μ) : (homogeneousPair μ hμ).cap = μ := by
  simp [ScalarPair.cap, homogeneousPair, Complex.norm_real, abs_of_pos hμ]

theorem homogeneous_loss (μ : ℝ) (hμ : 0 < μ) : (homogeneousPair μ hμ).loss = μ := by
  simp [ScalarPair.loss, homogeneousPair]

theorem homogeneous_isolatedRho (μ : ℝ) (hμ : 0 < μ) : isolatedRho (homogeneousPair μ hμ) = μ := by
  simp only [isolatedRho, homogeneousPair, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hμ, one_mul, Complex.mul_im, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, zero_add, max_self]
  field_simp

theorem homogeneous_remainder (D E : Set OQ7Prescribed.Position) (hD : IsOpen D) (hE : IsOpen E)
    (hfinD : volume D ≠ ⊤) (hfinE : volume E ≠ ⊤)
    {R1 R2 : ℝ} (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2)
    (hsubD : D ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R1)
    (hsubE : E ⊆ Metric.closedBall (0 : OQ7Prescribed.Position) R2)
    (d : ℝ) (hd : 0 < d) (hgap : ∀ x ∈ D, ∀ y ∈ E, d ≤ ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) :
    ‖response D E hD hE (homogeneousPair μ hμ) -
      blockInverse D E hD.measurableSet hE.measurableSet (homogeneousPair μ hμ) -
      blockInverse D E hD.measurableSet hE.measurableSet (homogeneousPair μ hμ) ∘L
        interaction D E hD.measurableSet hE.measurableSet ∘L
          blockInverse D E hD.measurableSet hE.measurableSet (homogeneousPair μ hμ)‖ ≤
      μ ^ 3 * (crossBound D E d) ^ 2 := by
  have hA := blockInverse_norm_le D E hD hE d hd hgap (homogeneousPair μ hμ)
  rw [homogeneous_isolatedRho] at hA
  have hT := response_resource_norm_le D E hD hE (homogeneousPair μ hμ)
  rw [homogeneous_cap, homogeneous_loss, sq, mul_div_cancel_right₀ μ (ne_of_gt hμ)] at hT
  exact BlockResolvent.second_order_remainder_norm_le _ _ _ hμ.le (crossBound_nonneg D E hd) hA
    (interaction_norm_le D E hD hE hfinD hfinE hR1 hR2 hsubD hsubE d hd hgap) hT
    (response_identity D E hD hE d hd hgap (homogeneousPair μ hμ))

end QuarticMaxwell.TwoSupportBounds
