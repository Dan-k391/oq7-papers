import QuarticMaxwell.SupportedOperators
import QuarticMaxwell.TensorMultiplier

/-! A common inverse for the actual arbitrary-support tensor volume operator.
Only pointwise measurable material bounds enter the hypotheses. The norm,
loss, Green dissipativity and inverse estimates are derived below. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
namespace VolumeInverse
open MeasureTheory Set OQ7Prescribed

variable (D : Set Position) (hD : MeasurableSet D)
  (χ : Position → Vector →L[ℂ] Vector) (hχ : AEStronglyMeasurable χ volume)
  (M : ℝ) (hcap : ∀ᵐ x ∂volume, x ∈ D → ‖χ x‖ ≤ M)
  {m : ℝ} (hm : 0 < m)
  (hloss : ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector, m * ‖v‖ ^ 2 ≤ (inner ℂ v (χ x v)).im)

def inverseSusceptibility : DomainL2 D →L[ℂ] DomainL2 D :=
  TensorMultiplier.inverse volume D χ hχ M hcap hD hm hloss

def operator (k : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) : DomainL2 D →L[ℂ] DomainL2 D :=
  inverseSusceptibility D hD χ hχ M hcap hm hloss - domainOutgoingOperator k D hD hR hsub

theorem negative_coercive {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (p : DomainL2 D) :
    m / M ^ 2 * ‖p‖ ^ 2 ≤ -(inner ℂ p (operator D hD χ hχ M hcap hm hloss k hR hsub p)).im := by
  have hmat := TensorMultiplier.inverse_loss_bound volume D χ hχ M hcap hD hm hloss hM p
  change m / M ^ 2 * ‖p‖ ^ 2 ≤
    -(inner ℂ p (inverseSusceptibility D hD χ hχ M hcap hm hloss p)).im at hmat
  have hgreen := domainOutgoingOperator_im_nonneg hk D hD hfin hR hsub p
  change m / M ^ 2 * ‖p‖ ^ 2 ≤
    -(inner ℂ p (inverseSusceptibility D hD χ hχ M hcap hm hloss p -
      domainOutgoingOperator k D hD hR hsub p)).im
  rw [inner_sub_right, Complex.sub_im]
  exact hmat.trans (by linarith)

theorem operator_norm_le {k : ℝ} (hk : 0 ≤ k) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (hV : 0 < volume.real D) :
    ‖operator D hD χ hχ M hcap hm hloss k hR hsub‖ ≤
      1 / m + 1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2 := by
  have hK : ‖domainOutgoingOperator k D hD hR hsub‖ ≤
      1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2 := by
    have he : domainOutgoingOperator k D hD hR hsub =
        (domainOutgoingOperator k D hD hR hsub - domainStaticOperator D hD) + domainStaticOperator D hD := by abel
    conv_lhs => rw [he]
    apply (norm_add_le
      (domainOutgoingOperator k D hD hR hsub - domainStaticOperator D hD)
      (domainStaticOperator D hD)).trans
    have h := add_le_add (domainOutgoingOperator_difference_norm_le hk D hD hR hsub hV)
      (domainStaticOperator_norm_le D hD)
    exact h.trans_eq (by ring)
  unfold operator
  apply (norm_sub_le (inverseSusceptibility D hD χ hχ M hcap hm hloss)
    (domainOutgoingOperator k D hD hR hsub)).trans
  have hi := TensorMultiplier.inverse_norm_le volume D χ hχ M hcap hD hm hloss
  exact (add_le_add hi hK).trans_eq (by ring)

theorem negative_coercive_bijective {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    Function.Bijective (operator D hD χ hχ M hcap hm hloss k hR hsub) := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  let A := operator D hD χ hχ M hcap hm hloss k hR hsub
  have hc : ∀ p, m / M ^ 2 * ‖p‖ ^ 2 ≤ (inner ℂ p ((-A) p)).im := by
    intro p
    simpa only [neg_apply, inner_neg_right, Complex.neg_im] using
      negative_coercive D hD χ hχ M hcap hm hloss hk hM hfin hR hsub p
  have hb := imaginary_coercive_bijective (-A) (by positivity : 0 < m / M ^ 2) hc
  constructor
  · intro p q hpq
    apply hb.injective
    change -(A p) = -(A q)
    rw [hpq]
  · intro f
    obtain ⟨p, hp⟩ := hb.surjective (-f)
    refine ⟨p, ?_⟩
    exact neg_injective hp

def equiv {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) : DomainL2 D ≃L[ℂ] DomainL2 D := by
  letI := domainCompleteSpace D hD
  exact ContinuousLinearEquiv.ofBijective (operator D hD χ hχ M hcap hm hloss k hR hsub)
    (LinearMap.ker_eq_bot.mpr (negative_coercive_bijective D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).injective)
    (LinearMap.range_eq_top.mpr (negative_coercive_bijective D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).surjective)

theorem equiv_apply {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (p : DomainL2 D) :
    equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub p =
      operator D hD χ hχ M hcap hm hloss k hR hsub p := rfl

theorem inverse_norm_le {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖(equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).symm.toContinuousLinearMap‖ ≤ M ^ 2 / m := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  let A := operator D hD χ hχ M hcap hm hloss k hR hsub
  let E := equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub
  have hc : ∀ p, m / M ^ 2 * ‖p‖ ^ 2 ≤ (inner ℂ p ((-A) p)).im := by
    intro p
    simpa only [neg_apply, inner_neg_right, Complex.neg_im] using
      negative_coercive D hD χ hχ M hcap hm hloss hk hM hfin hR hsub p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have h := imaginary_coercive_norm_bound (-A) (by positivity : 0 < m / M ^ 2) hc (E.symm f)
  have he : A (E.symm f) = f := E.apply_symm_apply f
  change m / M ^ 2 * ‖E.symm f‖ ≤ ‖-(A (E.symm f))‖ at h
  rw [norm_neg, he] at h
  change ‖E.symm f‖ ≤ M ^ 2 / m * ‖f‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).mpr
  have hh := (mul_le_mul_of_nonneg_left h (sq_nonneg M))
  have heq : M ^ 2 * (m / M ^ 2 * ‖E.symm f‖) = m * ‖E.symm f‖ := by
    field_simp
  rw [heq] at hh
  nlinarith

theorem susceptibility_reciprocity
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    (p q : DomainL2 D) :
    inner ℂ (domainConjugate D p) (TensorMultiplier.operator volume D χ hχ M hcap q) =
      inner ℂ (domainConjugate D q) (TensorMultiplier.operator volume D χ hχ M hcap p) := by
  change inner ℂ (conjugateL2 (p : VectorL2)) (TensorMultiplier.operator volume D χ hχ M hcap q : VectorL2) =
    inner ℂ (conjugateL2 (q : VectorL2)) (TensorMultiplier.operator volume D χ hχ M hcap p : VectorL2)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [conjugateL2_coe (p : VectorL2), conjugateL2_coe (q : VectorL2),
    TensorMultiplier.operator_coe volume D χ hχ M hcap p,
    TensorMultiplier.operator_coe volume D χ hχ M hcap q, hsym, p.property] with x hp hq hχp hχq hs hpd
  rw [hp, hq, hχp, hχq, ← bilinear_eq_conjugate_inner, ← bilinear_eq_conjugate_inner]
  by_cases hx : x ∈ D
  · exact hs hx _ _
  · simp [hpd hx, map_zero, bilinear]

theorem inverseSusceptibility_reciprocity
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    (p q : DomainL2 D) :
    inner ℂ (domainConjugate D p) (inverseSusceptibility D hD χ hχ M hcap hm hloss q) =
      inner ℂ (domainConjugate D q) (inverseSusceptibility D hD χ hχ M hcap hm hloss p) := by
  have h := susceptibility_reciprocity D χ hχ M hcap hsym
    (inverseSusceptibility D hD χ hχ M hcap hm hloss p)
    (inverseSusceptibility D hD χ hχ M hcap hm hloss q)
  simp only [inverseSusceptibility, TensorMultiplier.operator_inverse] at h
  rw [domainConjugate_pairing_comm D p, domainConjugate_pairing_comm D q]
  exact h.symm

theorem operator_reciprocity {k : ℝ} (hk : 0 < k)
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) (p q : DomainL2 D) :
    inner ℂ (domainConjugate D p) (operator D hD χ hχ M hcap hm hloss k hR hsub q) =
      inner ℂ (domainConjugate D q) (operator D hD χ hχ M hcap hm hloss k hR hsub p) := by
  simp only [operator, sub_apply, inner_sub_right]
  rw [inverseSusceptibility_reciprocity D hD χ hχ M hcap hm hloss hsym p q,
    domainOutgoingOperator_reciprocity hk D hD hR hsub p q]

theorem solution_inverseSusceptibility_eq {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    inverseSusceptibility D hD χ hχ M hcap hm hloss
      ((equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).symm f) =
        f + domainOutgoingOperator k D hD hR hsub
          ((equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).symm f) := by
  have h := (equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).apply_symm_apply f
  change inverseSusceptibility D hD χ hχ M hcap hm hloss _ - domainOutgoingOperator k D hD hR hsub _ = f at h
  exact eq_add_of_sub_eq h

theorem solution_constitutive {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f : DomainL2 D) :
    let p := (equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).symm f
    (fun x => χ x ((f : VectorL2) x + (domainOutgoingOperator k D hD hR hsub p : VectorL2) x)) =ᵐ[volume]
      (p : VectorL2) := by
  let p := (equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).symm f
  have h := TensorMultiplier.inverse_constitutive volume D χ hχ M hcap hD hm hloss p
  have he := congrArg (fun u : DomainL2 D => (u : VectorL2))
    (solution_inverseSusceptibility_eq D hD χ hχ M hcap hm hloss hk hM hfin hR hsub f)
  change (inverseSusceptibility D hD χ hχ M hcap hm hloss p : VectorL2) =
    (f : VectorL2) + (domainOutgoingOperator k D hD hR hsub p : VectorL2) at he
  change (fun x => χ x ((inverseSusceptibility D hD χ hχ M hcap hm hloss p : VectorL2) x)) =ᵐ[volume] _ at h
  rw [he] at h
  filter_upwards [h, Lp.coeFn_add (f : VectorL2) (domainOutgoingOperator k D hD hR hsub p : VectorL2)] with x hx ha
  simpa only [ha, Pi.add_apply] using hx

end VolumeInverse
end QuarticMaxwell
