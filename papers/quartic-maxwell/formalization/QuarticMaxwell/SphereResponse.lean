import QuarticMaxwell.SphereStatic
import QuarticMaxwell.StaticReciprocity

/-! Isolated homogeneous spheres: actual susceptibility inverse, static response
and moment identities, using the derived ball Fourier-operator eigenvalue. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.SphereResponse
open OQ7Prescribed SphereStatic MeasureTheory Set

def scalarSusceptibility (χ : ℂ) : Position → Vector →L[ℂ] Vector :=
  fun _ => χ • ContinuousLinearMap.id ℂ Vector

theorem scalar_measurable (χ : ℂ) : AEStronglyMeasurable (scalarSusceptibility χ) volume :=
  aestronglyMeasurable_const

theorem scalar_cap (χ : ℂ) (D : Set Position) :
    ∀ᵐ x ∂volume, x ∈ D → ‖scalarSusceptibility χ x‖ ≤ ‖χ‖ := by
  exact ae_of_all _ (fun _ _ => by simp [scalarSusceptibility, norm_smul])

theorem scalar_loss (χ : ℂ) (D : Set Position) :
    ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector,
      χ.im * ‖v‖ ^ 2 ≤ (inner ℂ v (scalarSusceptibility χ x v)).im := by
  exact ae_of_all _ (fun _ _ v => by
    simp [scalarSusceptibility, inner_smul_right, inner_self_eq_norm_sq_to_K,
      pow_two, Complex.mul_re, Complex.mul_im])

theorem scalar_nonzero {χ : ℂ} (hχ : 0 < χ.im) : χ ≠ 0 := by
  intro he
  simp only [he, Complex.zero_im, lt_self_iff_false] at hχ

theorem scalar_norm_pos {χ : ℂ} (hχ : 0 < χ.im) : 0 < ‖χ‖ :=
  norm_pos_iff.mpr (scalar_nonzero hχ)

theorem scalar_operator (χ : ℂ) (D : Set Position) (p : DomainL2 D) :
    TensorMultiplier.operator volume D (scalarSusceptibility χ) (scalar_measurable χ)
      ‖χ‖ (scalar_cap χ D) p = χ • p := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [TensorMultiplier.operator_coe volume D (scalarSusceptibility χ)
      (scalar_measurable χ) ‖χ‖ (scalar_cap χ D) p,
    Lp.coeFn_smul χ (p : VectorL2)] with x hx hs
  change _ = (χ • (p : VectorL2)) x
  rw [hs, hx]
  rfl

theorem scalar_inverse (χ : ℂ) (hχ : 0 < χ.im) (D : Set Position) (hD : MeasurableSet D)
    (p : DomainL2 D) :
    VolumeInverse.inverseSusceptibility D hD (scalarSusceptibility χ) (scalar_measurable χ)
      ‖χ‖ (scalar_cap χ D) hχ (scalar_loss χ D) p = χ⁻¹ • p := by
  have h := TensorMultiplier.operator_inverse volume D (scalarSusceptibility χ)
    (scalar_measurable χ) ‖χ‖ (scalar_cap χ D) hD hχ (scalar_loss χ D) p
  rw [scalar_operator] at h
  calc
    _ = χ⁻¹ • (χ • VolumeInverse.inverseSusceptibility D hD (scalarSusceptibility χ)
        (scalar_measurable χ) ‖χ‖ (scalar_cap χ D) hχ (scalar_loss χ D) p) := by
      rw [smul_smul, inv_mul_cancel₀ (scalar_nonzero hχ), one_smul]
    _ = _ := congrArg (fun q => χ⁻¹ • q) h

def beta (χ : ℂ) : ℂ := 3 * χ / (3 + χ)

theorem three_add_nonzero {χ : ℂ} (hχ : 0 < χ.im) : (3 + χ) ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  norm_num at hi
  linarith

theorem beta_inverse_identity {χ : ℂ} (hχ : 0 < χ.im) :
    beta χ * (χ⁻¹ + 1 / 3) = 1 := by
  unfold beta
  field_simp [three_add_nonzero hχ, scalar_nonzero hχ]

def ballEquiv (c : Position) (a : ℝ) (χ : ℂ) (hχ : 0 < χ.im) :
    DomainL2 (Metric.ball c a) ≃L[ℂ] DomainL2 (Metric.ball c a) :=
  StaticInverse.equiv (Metric.ball c a) measurableSet_ball (scalarSusceptibility χ)
    (scalar_measurable χ) ‖χ‖ (scalar_cap χ _) hχ (scalar_loss χ _) (scalar_norm_pos hχ)

theorem ballEquiv_source (c : Position) {a : ℝ} (ha : 0 < a) (χ : ℂ) (hχ : 0 < χ.im)
    (v : Vector) :
    ballEquiv c a χ hχ (ballSource c a v) = (χ⁻¹ + 1 / 3 : ℂ) • ballSource c a v := by
  rw [ballEquiv, StaticInverse.equiv_apply]
  change VolumeInverse.inverseSusceptibility _ _ _ _ _ _ _ _ _ -
    domainStaticOperator _ _ _ = _
  rw [scalar_inverse, domainStatic_ballSource c ha]
  module

theorem ball_inverse_source (c : Position) {a : ℝ} (ha : 0 < a) (χ : ℂ) (hχ : 0 < χ.im)
    (v : Vector) :
    (ballEquiv c a χ hχ).symm (ballSource c a v) = beta χ • ballSource c a v := by
  apply (ballEquiv c a χ hχ).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, ballEquiv_source c ha,
    smul_smul, beta_inverse_identity hχ, one_smul]

end QuarticMaxwell.SphereResponse

namespace QuarticMaxwell.SphereResponse
open OQ7Prescribed SphereStatic MeasureTheory Set

theorem ball_volume_real (c : Position) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (Metric.ball c a) = 4 * Real.pi * a ^ 3 / 3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem ball_volume_pos (c : Position) {a : ℝ} (ha : 0 < a) :
    0 < volume.real (Metric.ball c a) := by
  rw [ball_volume_real c ha.le]
  positivity

theorem ball_integrable (c : Position) (a : ℝ) (p : DomainL2 (Metric.ball c a)) :
    Integrable (fun x : Position => (p : VectorL2) x) volume := by
  have hi : IntegrableOn (fun x : Position => (p : VectorL2) x) (Metric.ball c a) volume :=
    integrableOn_Lp_of_measure_ne_top (p : VectorL2) (by norm_num) (ball_measure_ne_top c a)
  apply (hi.integrable_indicator measurableSet_ball).congr
  filter_upwards [p.property] with x hx
  by_cases hm : x ∈ Metric.ball c a
  · simp [Set.indicator, hm]
  · simp [Set.indicator, hm, hx hm]

theorem ballSource_pairing (c : Position) (a : ℝ) (p : DomainL2 (Metric.ball c a)) (i : Fin 3) :
    inner ℂ (domainConjugate (Metric.ball c a) (ballSource c a (basisC i))) p =
      (∫ x : Position, (p : VectorL2) x) i := by
  have hi := ball_integrable c a p
  have hc := (PiLp.proj 2 (fun _ : Fin 3 => ℂ) i : Vector →L[ℝ] ℂ).integral_comp_comm hi
  change (∫ x : Position, (p : VectorL2) x i) = (∫ x : Position, (p : VectorL2) x) i at hc
  rw [← hc]
  change inner ℂ (conjugateL2 (ballSource c a (basisC i) : VectorL2)) (p : VectorL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [conjugateL2_coe (ballSource c a (basisC i) : VectorL2),
    ballSource_coe c a (basisC i), p.property] with x hj hb hp
  rw [hj, hb, ← bilinear_eq_conjugate_inner]
  by_cases hx : x ∈ Metric.ball c a
  · simp [Set.indicator, hx, bilinear, basisC]
  · simp [Set.indicator, hx, hp hx, bilinear]

theorem scalar_reciprocal (χ : ℂ) (D : Set Position) :
    ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector,
      bilinear u (scalarSusceptibility χ x v) = bilinear v (scalarSusceptibility χ x u) := by
  exact ae_of_all _ (fun _ _ u v => by
    simp only [scalarSusceptibility, smul_apply, ContinuousLinearMap.id_apply,
      bilinear, PiLp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring)

theorem ball_inverse_mean (c : Position) {a : ℝ} (ha : 0 < a) (χ : ℂ) (hχ : 0 < χ.im)
    (f : DomainL2 (Metric.ball c a)) :
    (∫ x : Position, ((ballEquiv c a χ hχ).symm f : VectorL2) x) =
      beta χ • (∫ x : Position, (f : VectorL2) x) := by
  apply PiLp.ext
  intro i
  rw [← ballSource_pairing, PiLp.smul_apply, smul_eq_mul]
  have h := StaticInverse.inverse_reciprocity (Metric.ball c a) measurableSet_ball
    (scalarSusceptibility χ) (scalar_measurable χ) ‖χ‖ (scalar_cap χ _) hχ
    (scalar_loss χ _) (scalar_norm_pos hχ) (scalar_reciprocal χ _)
    (ball_volume_pos c ha) (by positivity : 0 ≤ ‖c‖ + a) (ball_support_bound c a)
    (ballSource c a (basisC i)) f
  change inner ℂ (domainConjugate (Metric.ball c a) (ballSource c a (basisC i)))
      ((ballEquiv c a χ hχ).symm f) =
    inner ℂ (domainConjugate (Metric.ball c a) f)
      ((ballEquiv c a χ hχ).symm (ballSource c a (basisC i))) at h
  rw [h, ball_inverse_source c ha]
  change inner ℂ (conjugateL2 (f : VectorL2))
      (beta χ • (ballSource c a (basisC i) : VectorL2)) = _
  rw [inner_smul_right]
  congr 1
  exact (domainConjugate_pairing_comm _ f (ballSource c a (basisC i))).trans
    (ballSource_pairing c a f i)

end QuarticMaxwell.SphereResponse
