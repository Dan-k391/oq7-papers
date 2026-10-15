import QuarticMaxwell.StaticInverse

/-! Static bilinear reciprocity follows from the actual sharp dynamic/static
norm convergence and genuine dynamic Green reciprocity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem nonpositive_of_le_mul_sq {x C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 < t → x ≤ C * t ^ 2) : x ≤ 0 := by
  by_contra hx
  have hx : 0 < x := lt_of_not_ge hx
  let t := Real.sqrt (x / (C + 1))
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = x / (C + 1) := Real.sq_sqrt (by positivity)
  have hb := h t ht
  rw [ht2] at hb
  have hs := mul_le_mul_of_nonneg_right hb (show 0 ≤ C + 1 by positivity)
  have heq : C * (x / (C + 1)) * (C + 1) = C * x := by field_simp
  rw [heq] at hs
  nlinarith only [hs, hx]

theorem domainStaticOperator_reciprocity (D : Set Position) (hD : MeasurableSet D)
    (hV : 0 < volume.real D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (p q : DomainL2 D) :
    inner ℂ (domainConjugate D p) (domainStaticOperator D hD q) =
      inner ℂ (domainConjugate D q) (domainStaticOperator D hD p) := by
  let z := inner ℂ (domainConjugate D p) (domainStaticOperator D hD q) -
      inner ℂ (domainConjugate D q) (domainStaticOperator D hD p)
  let C := 3 / 2 * volumeRadius (volume.real D) ^ 2 * ‖p‖ * ‖q‖
  have hJp : ‖domainConjugate D p‖ ≤ ‖p‖ := conjugateL2_norm_le (p : VectorL2)
  have hJq : ‖domainConjugate D q‖ ≤ ‖q‖ := conjugateL2_norm_le (q : VectorL2)
  have hz0 : ‖z‖ ≤ 0 := by
    apply nonpositive_of_le_mul_sq (show 0 ≤ C by dsimp [C]; positivity)
    intro k hk
    let δ := 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2
    have hdiff (u : DomainL2 D) :
        ‖domainStaticOperator D hD u - domainOutgoingOperator k D hD hR hsub u‖ ≤ δ * ‖u‖ := by
      have h := ((domainOutgoingOperator k D hD hR hsub - domainStaticOperator D hD).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (domainOutgoingOperator_difference_norm_le hk.le D hD hR hsub hV) (norm_nonneg u))
      simpa only [sub_apply, norm_sub_rev] using h
    have hrec := domainOutgoingOperator_reciprocity hk D hD hR hsub p q
    have hrec' : inner ℂ (domainConjugate D p : VectorL2)
        (domainOutgoingOperator k D hD hR hsub q : VectorL2) =
      inner ℂ (domainConjugate D q : VectorL2)
        (domainOutgoingOperator k D hD hR hsub p : VectorL2) := hrec
    have heq : z =
        inner ℂ (domainConjugate D p) (domainStaticOperator D hD q - domainOutgoingOperator k D hD hR hsub q) -
          inner ℂ (domainConjugate D q) (domainStaticOperator D hD p - domainOutgoingOperator k D hD hR hsub p) := by
      dsimp [z]
      rw [inner_sub_right, inner_sub_right, hrec']
      ring
    rw [heq]
    calc
      _ ≤ ‖inner ℂ (domainConjugate D p)
          (domainStaticOperator D hD q - domainOutgoingOperator k D hD hR hsub q)‖ +
        ‖inner ℂ (domainConjugate D q)
          (domainStaticOperator D hD p - domainOutgoingOperator k D hD hR hsub p)‖ := norm_sub_le _ _
      _ ≤ ‖domainConjugate D p‖ * ‖domainStaticOperator D hD q - domainOutgoingOperator k D hD hR hsub q‖ +
        ‖domainConjugate D q‖ * ‖domainStaticOperator D hD p - domainOutgoingOperator k D hD hR hsub p‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖p‖ * (δ * ‖q‖) + ‖q‖ * (δ * ‖p‖) :=
        add_le_add (mul_le_mul hJp (hdiff q) (norm_nonneg _) (norm_nonneg p))
          (mul_le_mul hJq (hdiff p) (norm_nonneg _) (norm_nonneg q))
      _ = C * k ^ 2 := by dsimp [δ, C]; ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz0 (norm_nonneg z)))

namespace StaticInverse
variable (D : Set Position) (hD : MeasurableSet D)
  (χ : Position → Vector →L[ℂ] Vector) (hχ : AEStronglyMeasurable χ volume)
  (M : ℝ) (hcap : ∀ᵐ x ∂volume, x ∈ D → ‖χ x‖ ≤ M)
  {m : ℝ} (hm : 0 < m)
  (hloss : ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector, m * ‖v‖ ^ 2 ≤ (inner ℂ v (χ x v)).im)

theorem operator_reciprocity
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    (hV : 0 < volume.real D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (p q : DomainL2 D) :
    inner ℂ (domainConjugate D p) (operator D hD χ hχ M hcap hm hloss q) =
      inner ℂ (domainConjugate D q) (operator D hD χ hχ M hcap hm hloss p) := by
  simp only [operator, sub_apply, inner_sub_right]
  rw [VolumeInverse.inverseSusceptibility_reciprocity D hD χ hχ M hcap hm hloss hsym p q,
    domainStaticOperator_reciprocity D hD hV hR hsub p q]

theorem inverse_reciprocity (hM : 0 < M)
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    (hV : 0 < volume.real D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (f g : DomainL2 D) :
    inner ℂ (domainConjugate D f) ((equiv D hD χ hχ M hcap hm hloss hM).symm g) =
      inner ℂ (domainConjugate D g) ((equiv D hD χ hχ M hcap hm hloss hM).symm f) := by
  apply domain_inverse_bilinear_reciprocity
  intro p q
  rw [equiv_apply, equiv_apply]
  exact operator_reciprocity D hD χ hχ M hcap hm hloss hsym hV hR hsub p q

end StaticInverse
end QuarticMaxwell
