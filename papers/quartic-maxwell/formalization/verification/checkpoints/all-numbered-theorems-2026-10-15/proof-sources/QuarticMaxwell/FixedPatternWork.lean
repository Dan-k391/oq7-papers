import QuarticMaxwell.SourceTaylor
import QuarticMaxwell.StaticInverse
import QuarticMaxwell.WeakMaterial

/-! Quantitative expansions of the actual dynamic volume solutions and
their common forward work for one fixed measurable material pattern. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell
namespace FixedPatternWork
open MeasureTheory Set OQ7Prescribed WeakMaterial SourceTaylor

def rho (B : Medium) : ℝ := B.M ^ 2 / B.m
def correction (B : Medium) : ℝ := 3 / 4 * rho B ^ 2 * volumeRadius (volume.real B.domain) ^ 2

theorem rho_pos (B : Medium) : 0 < rho B :=
  div_pos (sq_pos_of_pos B.M_pos) B.m_pos

theorem correction_nonneg (B : Medium) : 0 ≤ correction B := by unfold correction; positivity

def staticResponse (B : Medium) : DomainL2 B.domain →L[ℂ] DomainL2 B.domain :=
  (StaticInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss B.M_pos).symm.toContinuousLinearMap

def dynamicResponse (B : Medium) (t : ℝ) (ht : 0 < t) : DomainL2 B.domain →L[ℂ] DomainL2 B.domain :=
  (VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss ht B.M_pos B.finite B.radius_nonneg B.subset_ball).symm.toContinuousLinearMap

def constantInput (B : Medium) (e : Vector) : DomainL2 B.domain :=
  constantSource B.domain B.measurable B.finite e

def linearInput (B : Medium) (n : UnitSphere) (e : Vector) : DomainL2 B.domain :=
  momentSource B.domain B.measurable B.finite n e B.radius B.subset_ball

def cosineInput (B : Medium) (t : ℝ) (n : UnitSphere) (e : Vector) : DomainL2 B.domain :=
  cosSource B.domain B.measurable B.finite t n e

def sineInput (B : Medium) (t : ℝ) (n : UnitSphere) (e : Vector) : DomainL2 B.domain :=
  sinSource B.domain B.measurable B.finite t n e

def q0 (B : Medium) (e : Vector) : DomainL2 B.domain := staticResponse B (constantInput B e)
def q1 (B : Medium) (n : UnitSphere) (e : Vector) : DomainL2 B.domain := staticResponse B (linearInput B n e)
def u (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) : DomainL2 B.domain :=
  dynamicResponse B t ht (cosineInput B t n e)
def v (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) : DomainL2 B.domain :=
  dynamicResponse B t ht (sineInput B t n e)
def D0 (B : Medium) (e : Vector) : ℝ := (inner ℂ (constantInput B e) (q0 B e)).im

theorem static_norm_le (B : Medium) : ‖staticResponse B‖ ≤ rho B :=
  StaticInverse.inverse_norm_le B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss B.M_pos

theorem dynamic_norm_le (B : Medium) (t : ℝ) (ht : 0 < t) : ‖dynamicResponse B t ht‖ ≤ rho B :=
  VolumeInverse.inverse_norm_le B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss ht B.M_pos B.finite B.radius_nonneg B.subset_ball

theorem resolvent_norm_le (B : Medium) (hV : 0 < volume.real B.domain) (t : ℝ) (ht : 0 < t) :
    ‖dynamicResponse B t ht - staticResponse B‖ ≤ correction B * t ^ 2 :=
  StaticInverse.dynamic_static_resolvent_norm_le B.domain B.measurable B.susceptibility
    B.measurable_susceptibility B.M B.cap B.m_pos B.loss ht B.M_pos B.finite hV
    B.radius_nonneg B.subset_ball

theorem u_norm (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) :
    ‖u B t ht n e‖ ≤ rho B * ‖constantInput B e‖ := by
  exact ((dynamicResponse B t ht).le_opNorm _).trans
    (mul_le_mul (dynamic_norm_le B t ht)
      (cosine_norm B.domain B.measurable B.finite t n e) (norm_nonneg _) (rho_pos B).le)

theorem v_norm (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) :
    ‖v B t ht n e‖ ≤ rho B * (t * B.radius * ‖constantInput B e‖) := by
  have hs := sine_norm B.domain B.measurable B.finite t n e B.subset_ball
  rw [abs_of_pos ht] at hs
  exact ((dynamicResponse B t ht).le_opNorm _).trans
    (mul_le_mul (dynamic_norm_le B t ht) hs (norm_nonneg _) (rho_pos B).le)

theorem q0_norm (B : Medium) (e : Vector) : ‖q0 B e‖ ≤ rho B * ‖constantInput B e‖ :=
  ((staticResponse B).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (static_norm_le B) (norm_nonneg _))

theorem q1_norm (B : Medium) (n : UnitSphere) (e : Vector) :
    ‖q1 B n e‖ ≤ rho B * (B.radius * ‖constantInput B e‖) := by
  exact ((staticResponse B).le_opNorm _).trans
    (mul_le_mul (static_norm_le B) (moment_norm B.domain B.measurable B.finite n e B.subset_ball)
      (norm_nonneg _) (rho_pos B).le)

theorem u_error (B : Medium) (hV : 0 < volume.real B.domain) (t : ℝ) (ht : 0 < t)
    (n : UnitSphere) (e : Vector) :
    ‖u B t ht n e - q0 B e‖ ≤
      (rho B * B.radius ^ 2 / 2 + correction B) * ‖constantInput B e‖ * t ^ 2 := by
  let T := dynamicResponse B t ht
  let T0 := staticResponse B
  let c := cosineInput B t n e
  let c0 := constantInput B e
  have he : T c - T0 c0 = T (c - c0) + (T - T0) c0 := by simp only [map_sub, sub_apply]; abel
  change ‖T c - T0 c0‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖T (c - c0)‖ + ‖(T - T0) c0‖ := norm_add_le _ _
    _ ≤ rho B * ‖c - c0‖ + (correction B * t ^ 2) * ‖c0‖ := by
      apply add_le_add
      · exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right (dynamic_norm_le B t ht) (norm_nonneg _))
      · exact ((T - T0).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (resolvent_norm_le B hV t ht) (norm_nonneg _))
    _ ≤ rho B * ((t ^ 2 * B.radius ^ 2 / 2) * ‖c0‖) + (correction B * t ^ 2) * ‖c0‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (cosine_remainder B.domain B.measurable B.finite t n e B.radius_nonneg B.subset_ball)
        (rho_pos B).le) le_rfl
    _ = _ := by ring

theorem v_error (B : Medium) (hV : 0 < volume.real B.domain) (t : ℝ) (ht : 0 < t)
    (n : UnitSphere) (e : Vector) :
    ‖v B t ht n e - (t : ℂ) • q1 B n e‖ ≤
      (rho B * B.radius ^ 3 / 6 + correction B * B.radius) * ‖constantInput B e‖ * t ^ 3 := by
  let T := dynamicResponse B t ht
  let T0 := staticResponse B
  let s := sineInput B t n e
  let a := linearInput B n e
  let c0 := constantInput B e
  have he : T s - (t : ℂ) • T0 a = T (s - (t : ℂ) • a) + (T - T0) ((t : ℂ) • a) := by
    simp only [map_sub, map_smul, sub_apply, smul_sub]
    abel
  change ‖T s - (t : ℂ) • T0 a‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖T (s - (t : ℂ) • a)‖ + ‖(T - T0) ((t : ℂ) • a)‖ := norm_add_le _ _
    _ ≤ rho B * ‖s - (t : ℂ) • a‖ + (correction B * t ^ 2) * ‖(t : ℂ) • a‖ := by
      apply add_le_add
      · exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right (dynamic_norm_le B t ht) (norm_nonneg _))
      · exact ((T - T0).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (resolvent_norm_le B hV t ht) (norm_nonneg _))
    _ ≤ rho B * ((t ^ 3 * B.radius ^ 3 / 6) * ‖c0‖) +
        (correction B * t ^ 2) * (t * (B.radius * ‖c0‖)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (rho_pos B).le
        have hs := sine_remainder B.domain B.measurable B.finite t n e B.radius_nonneg B.subset_ball
        rw [abs_of_pos ht] at hs
        change ‖sinSource B.domain B.measurable B.finite t n e -
          (t : ℂ) • momentSource B.domain B.measurable B.finite n e B.radius B.subset_ball‖ ≤
          (t ^ 3 * B.radius ^ 3 / 6) * ‖constantSource B.domain B.measurable B.finite e‖
        exact hs
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (correction_nonneg B) (sq_nonneg t))
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
        exact mul_le_mul_of_nonneg_left
          (moment_norm B.domain B.measurable B.finite n e B.subset_ball) ht.le
    _ = _ := by ring

theorem D0_pos (B : Medium) (hV : 0 < volume.real B.domain) (n : UnitSphere)
    (e : Vector) (he : ‖e‖ = 1) : 0 < D0 B e := by
  apply StaticInverse.forward_work_pos B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss B.M_pos (constantInput B e)
  intro hz
  have hh := constant_norm_sq B.domain B.measurable B.finite n e
  change ‖constantInput B e‖ ^ 2 = volume.real B.domain * ‖e‖ ^ 2 at hh
  rw [hz, norm_zero, he] at hh
  norm_num at hh
  linarith

theorem inner_im_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b c d : H) :
    |(inner ℂ a b).im - (inner ℂ c d).im| ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by
  rw [← Complex.sub_im]
  have he : inner ℂ a b - inner ℂ c d = inner ℂ (a - c) b + inner ℂ c (b - d) := by
    rw [inner_sub_left, inner_sub_right]
    ring
  apply (Complex.abs_im_le_norm _).trans
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))

def forwardWork (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) : ℝ :=
  (inner ℂ (cosineInput B t n e) (u B t ht n e)).im +
    (inner ℂ (sineInput B t n e) (v B t ht n e)).im

theorem forward_work_error (B : Medium) (hV : 0 < volume.real B.domain) (t : ℝ) (ht : 0 < t)
    (n : UnitSphere) (e : Vector) :
    |forwardWork B t ht n e - D0 B e| ≤
      ‖constantInput B e‖ ^ 2 * (2 * rho B * B.radius ^ 2 + correction B) * t ^ 2 := by
  have hR := B.radius_nonneg
  have hρ := (rho_pos B).le
  let c := cosineInput B t n e
  let s := sineInput B t n e
  let c0 := constantInput B e
  let ut := u B t ht n e
  let vt := v B t ht n e
  have hc : ‖c - c0‖ ≤ t ^ 2 * B.radius ^ 2 / 2 * ‖c0‖ :=
    cosine_remainder B.domain B.measurable B.finite t n e B.radius_nonneg B.subset_ball
  have hs : ‖s‖ ≤ t * B.radius * ‖c0‖ := by
    have hh := sine_norm B.domain B.measurable B.finite t n e B.subset_ball
    rw [abs_of_pos ht] at hh
    change ‖sinSource B.domain B.measurable B.finite t n e‖ ≤
      t * B.radius * ‖constantSource B.domain B.measurable B.finite e‖
    exact hh
  have hu : ‖ut‖ ≤ rho B * ‖c0‖ := u_norm B t ht n e
  have hv : ‖vt‖ ≤ rho B * (t * B.radius * ‖c0‖) := v_norm B t ht n e
  have he : ‖ut - q0 B e‖ ≤ (rho B * B.radius ^ 2 / 2 + correction B) * ‖c0‖ * t ^ 2 :=
    u_error B hV t ht n e
  have hi := inner_im_error c ut c0 (q0 B e)
  have hj : |(inner ℂ s vt).im| ≤ ‖s‖ * ‖vt‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hsplit : forwardWork B t ht n e - D0 B e =
      ((inner ℂ c ut).im - (inner ℂ c0 (q0 B e)).im) + (inner ℂ s vt).im := by
    unfold forwardWork D0
    ring
  rw [hsplit]
  calc
    _ ≤ |(inner ℂ c ut).im - (inner ℂ c0 (q0 B e)).im| + |(inner ℂ s vt).im| := abs_add_le _ _
    _ ≤ ‖c - c0‖ * ‖ut‖ + ‖c0‖ * ‖ut - q0 B e‖ + ‖s‖ * ‖vt‖ := add_le_add hi hj
    _ ≤ (t ^ 2 * B.radius ^ 2 / 2 * ‖c0‖) * (rho B * ‖c0‖) +
        ‖c0‖ * ((rho B * B.radius ^ 2 / 2 + correction B) * ‖c0‖ * t ^ 2) +
        (t * B.radius * ‖c0‖) * (rho B * (t * B.radius * ‖c0‖)) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul hc hu (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left he (norm_nonneg _))
      · exact mul_le_mul hs hv (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_forward_decomposition (B : Medium) (t : ℝ) (ht : 0 < t)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ a b : Vector,
      bilinear a (B.susceptibility x b) = bilinear b (B.susceptibility x a))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) :
    (inner ℂ (domainIncidentSource t n e B.domain B.measurable B.finite)
      (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))).im =
        forwardWork B t ht n e := by
  let A := VolumeInverse.equiv B.domain B.measurable B.susceptibility B.measurable_susceptibility
    B.M B.cap B.m_pos B.loss ht B.M_pos B.finite B.radius_nonneg B.subset_ball
  let c := cosineInput B t n e
  let s := sineInput B t n e
  let T := dynamicResponse B t ht
  have hr := domain_inverse_bilinear_reciprocity B.domain A
    (VolumeInverse.operator_reciprocity B.domain B.measurable B.susceptibility B.measurable_susceptibility
      B.M B.cap B.m_pos B.loss ht hsym B.radius_nonneg B.subset_ball) c s
  have hc : domainConjugate B.domain c = c := cosine_fixed B.domain B.measurable B.finite t n e he
  have hs : domainConjugate B.domain s = s := sine_fixed B.domain B.measurable B.finite t n e he
  rw [hc, hs] at hr
  change inner ℂ c (T s) = inner ℂ s (T c) at hr
  rw [source_decomposition]
  change (inner ℂ (c - Complex.I • s) (T (c - Complex.I • s))).im = _
  have hh : inner ℂ (c - Complex.I • s) (T (c - Complex.I • s)) =
      inner ℂ c (T c) + inner ℂ s (T s) := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right]
    have h1 := _root_.inner_smul_left (𝕜 := ℂ) s (T c) Complex.I
    have h2 := _root_.inner_smul_right (𝕜 := ℂ) c (T s) Complex.I
    have h3 := _root_.inner_smul_left (𝕜 := ℂ) s (Complex.I • T s) Complex.I
    have h4 := _root_.inner_smul_right (𝕜 := ℂ) s (T s) Complex.I
    rw [h1, h2, h3, h4]
    rw [hr]
    simp
    ring_nf
    simp
  rw [hh, Complex.add_im]
  rfl

end FixedPatternWork
end QuarticMaxwell
