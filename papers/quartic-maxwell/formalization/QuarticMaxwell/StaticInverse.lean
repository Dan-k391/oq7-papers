import QuarticMaxwell.VolumeInverse
import QuarticMaxwell.UniformBound

/-! The actual static inverse and the dynamic/static resolvent estimate.
Both inverses are constructed from the same measurable tensor multiplier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem inverse_difference_eq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A B : H ≃L[ℂ] H) :
    A.symm.toContinuousLinearMap - B.symm.toContinuousLinearMap =
      A.symm.toContinuousLinearMap ∘L (B.toContinuousLinearMap - A.toContinuousLinearMap) ∘L
        B.symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  change A.symm f - B.symm f = A.symm (B (B.symm f) - A (B.symm f))
  rw [B.apply_symm_apply, map_sub, A.symm_apply_apply]

theorem inverse_difference_norm_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A B : H ≃L[ℂ] H) {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ ρ) (hB : ‖B.symm.toContinuousLinearMap‖ ≤ ρ)
    (hAB : ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ ≤ δ) :
    ‖A.symm.toContinuousLinearMap - B.symm.toContinuousLinearMap‖ ≤ ρ ^ 2 * δ := by
  rw [inverse_difference_eq]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  calc
    _ ≤ ‖A.symm.toContinuousLinearMap‖ *
        ‖(B.toContinuousLinearMap - A.toContinuousLinearMap) (B.symm f)‖ :=
      A.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ρ * (δ * (ρ * ‖f‖)) := by
      apply mul_le_mul hA
      · apply ((B.toContinuousLinearMap - A.toContinuousLinearMap).le_opNorm _).trans
        apply (mul_le_mul_of_nonneg_right hAB (norm_nonneg _)).trans
        exact mul_le_mul_of_nonneg_left
          ((B.symm.toContinuousLinearMap.le_opNorm f).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg f))) hδ
      · exact norm_nonneg _
      · exact hρ
    _ = _ := by ring

namespace StaticInverse
variable (D : Set Position) (hD : MeasurableSet D)
  (χ : Position → Vector →L[ℂ] Vector) (hχ : AEStronglyMeasurable χ volume)
  (M : ℝ) (hcap : ∀ᵐ x ∂volume, x ∈ D → ‖χ x‖ ≤ M)
  {m : ℝ} (hm : 0 < m)
  (hloss : ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector, m * ‖v‖ ^ 2 ≤ (inner ℂ v (χ x v)).im)

def operator : DomainL2 D →L[ℂ] DomainL2 D :=
  VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss - domainStaticOperator D hD

theorem negative_coercive (hM : 0 < M) (p : DomainL2 D) :
    m / M ^ 2 * ‖p‖ ^ 2 ≤ -(inner ℂ p (operator D hD χ hχ M hcap hm hloss p)).im := by
  have h := TensorMultiplier.inverse_loss_bound volume D χ hχ M hcap hD hm hloss hM p
  change m / M ^ 2 * ‖p‖ ^ 2 ≤
    -(inner ℂ p (VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss p - domainStaticOperator D hD p)).im
  rw [inner_sub_right, Complex.sub_im, domainStaticOperator_quadratic_im, sub_zero]
  exact h

def equiv (hM : 0 < M) : DomainL2 D ≃L[ℂ] DomainL2 D := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  let A := operator D hD χ hχ M hcap hm hloss
  have hc : ∀ p, m / M ^ 2 * ‖p‖ ^ 2 ≤ (inner ℂ p ((-A) p)).im := by
    intro p
    simpa only [neg_apply, inner_neg_right, Complex.neg_im] using
      negative_coercive D hD χ hχ M hcap hm hloss hM p
  exact (materialInverseEquiv (-A) (by positivity : 0 < m / M ^ 2) hc).trans
    (ContinuousLinearEquiv.neg ℂ)

theorem equiv_apply (hM : 0 < M) (p : DomainL2 D) :
    equiv D hD χ hχ M hcap hm hloss hM p = operator D hD χ hχ M hcap hm hloss p := by
  change -(-(operator D hD χ hχ M hcap hm hloss p)) = _
  exact neg_neg _

theorem inverse_norm_le (hM : 0 < M) :
    ‖(equiv D hD χ hχ M hcap hm hloss hM).symm.toContinuousLinearMap‖ ≤ M ^ 2 / m := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  let A := operator D hD χ hχ M hcap hm hloss
  let E := equiv D hD χ hχ M hcap hm hloss hM
  have hc : ∀ p, m / M ^ 2 * ‖p‖ ^ 2 ≤ (inner ℂ p ((-A) p)).im := by
    intro p
    simpa only [neg_apply, inner_neg_right, Complex.neg_im] using
      negative_coercive D hD χ hχ M hcap hm hloss hM p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have h := imaginary_coercive_norm_bound (-A) (by positivity : 0 < m / M ^ 2) hc (E.symm f)
  have he : A (E.symm f) = f := by
    rw [← equiv_apply D hD χ hχ M hcap hm hloss hM]
    exact E.apply_symm_apply f
  change m / M ^ 2 * ‖E.symm f‖ ≤ ‖-(A (E.symm f))‖ at h
  rw [norm_neg, he] at h
  change ‖E.symm f‖ ≤ M ^ 2 / m * ‖f‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).mpr
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg M)
  have heq : M ^ 2 * (m / M ^ 2 * ‖E.symm f‖) = m * ‖E.symm f‖ := by field_simp
  rw [heq] at hh
  nlinarith only [hh]

theorem dynamic_static_resolvent_norm_le {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hfin : volume D ≠ ⊤) (hV : 0 < volume.real D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖(VolumeInverse.equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub).symm.toContinuousLinearMap -
      (equiv D hD χ hχ M hcap hm hloss hM).symm.toContinuousLinearMap‖ ≤
        3 / 4 * (M ^ 2 / m) ^ 2 * volumeRadius (volume.real D) ^ 2 * k ^ 2 := by
  apply (inverse_difference_norm_le
    (VolumeInverse.equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub)
    (equiv D hD χ hχ M hcap hm hloss hM) (by positivity : 0 ≤ M ^ 2 / m)
    (by positivity : 0 ≤ 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2)
    (VolumeInverse.inverse_norm_le D hD χ hχ M hcap hm hloss hk hM hfin hR hsub)
    (inverse_norm_le D hD χ hχ M hcap hm hloss hM) ?_).trans_eq (by ring)
  have he : (equiv D hD χ hχ M hcap hm hloss hM).toContinuousLinearMap =
      operator D hD χ hχ M hcap hm hloss := by
    apply ContinuousLinearMap.ext
    exact equiv_apply D hD χ hχ M hcap hm hloss hM
  rw [he]
  change ‖(VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss - domainStaticOperator D hD) -
    (VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss - domainOutgoingOperator k D hD hR hsub)‖ ≤ _
  have heq : (VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss - domainStaticOperator D hD) -
      (VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss - domainOutgoingOperator k D hD hR hsub) =
        domainOutgoingOperator k D hD hR hsub - domainStaticOperator D hD := by abel
  rw [heq]
  exact domainOutgoingOperator_difference_norm_le hk.le D hD hR hsub hV

theorem forward_work_pos (hM : 0 < M) (f : DomainL2 D) (hf : f ≠ 0) :
    0 < (inner ℂ f ((equiv D hD χ hχ M hcap hm hloss hM).symm f)).im := by
  let E := equiv D hD χ hχ M hcap hm hloss hM
  have hc (p : DomainL2 D) : ‖p‖ ^ 2 / (M ^ 2 / m) ≤ -(inner ℂ p (E p)).im := by
    rw [show ‖p‖ ^ 2 / (M ^ 2 / m) = m / M ^ 2 * ‖p‖ ^ 2 by field_simp]
    rw [equiv_apply]
    exact negative_coercive D hD χ hχ M hcap hm hloss hM p
  have h := UniformBound.extinction_pos E (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < M ^ 2 / m) hc f hf
  have hi := inner_im_symm (𝕜 := ℂ) (E.symm f) f
  change (inner ℂ (E.symm f) f).im = -(inner ℂ f (E.symm f)).im at hi
  unfold UniformBound.extinctionPower at h
  rw [hi] at h
  simpa using h

end StaticInverse
end QuarticMaxwell
