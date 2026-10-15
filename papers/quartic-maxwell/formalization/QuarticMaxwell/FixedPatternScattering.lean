import QuarticMaxwell.GramEstimates
import QuarticMaxwell.FixedPatternWork
import QuarticMaxwell.Asymptotics

/-! Signed complete-angle scattering and its actual fixed-pattern leading
moment, with an explicit cubic error before normalized division. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem norm_sq_opposite_i {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E) :
    ‖a - Complex.I • b‖ ^ 2 - ‖a + Complex.I • b‖ ^ 2 = 4 * (inner ℂ a b).im := by
  have hself (x : E) : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]
  rw [← hself, ← hself]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_I, neg_mul]
  simp [Complex.mul_re, Complex.sub_re, Complex.add_re]
  have hi := inner_im_symm (𝕜 := ℂ) b a
  change (inner ℂ b a).im = -(inner ℂ a b).im at hi
  linarith

theorem gram_cross_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q Q0 : H →L[ℂ] H) (u v a b : H) (t : ℝ) :
    ‖inner ℂ u (Q v) - (t : ℂ) * inner ℂ a (Q0 b)‖ ≤
      ‖u - a‖ * ‖Q‖ * ‖v‖ + ‖a‖ * ‖Q - Q0‖ * ‖v‖ +
      ‖a‖ * ‖Q0‖ * ‖v - (t : ℂ) • b‖ := by
  have he : inner ℂ u (Q v) - (t : ℂ) * inner ℂ a (Q0 b) =
      inner ℂ (u - a) (Q v) + inner ℂ a ((Q - Q0) v) +
      inner ℂ a (Q0 (v - (t : ℂ) • b)) := by
    simp only [inner_sub_left, inner_sub_right, sub_apply, map_sub, map_smul]
    rw [inner_smul_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℂ (u - a) (Q v) + inner ℂ a ((Q - Q0) v)‖ +
        ‖inner ℂ a (Q0 (v - (t : ℂ) • b))‖ := norm_add_le _ _
    _ ≤ ‖inner ℂ (u - a) (Q v)‖ + ‖inner ℂ a ((Q - Q0) v)‖ +
        ‖inner ℂ a (Q0 (v - (t : ℂ) • b))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖u - a‖ * ‖Q v‖ + ‖a‖ * ‖(Q - Q0) v‖ +
        ‖a‖ * ‖Q0 (v - (t : ℂ) • b)‖ := by gcongr <;> exact norm_inner_le_norm _ _
    _ ≤ _ := by
      have h1 := Q.le_opNorm v
      have h2 := (Q - Q0).le_opNorm v
      have h3 := Q0.le_opNorm (v - (t : ℂ) • b)
      nlinarith only [mul_le_mul_of_nonneg_left h1 (norm_nonneg (u - a)),
        mul_le_mul_of_nonneg_left h2 (norm_nonneg a),
        mul_le_mul_of_nonneg_left h3 (norm_nonneg a)]

namespace FixedPatternScattering
open WeakMaterial FixedPatternWork

def moment0 (B : Medium) (e : Vector) : Vector :=
  supportMomentLinear B.domain B.finite (q0 B e)

def moment1 (B : Medium) (n : UnitSphere) (e : Vector) : Vector :=
  supportMomentLinear B.domain B.finite (q1 B n e)

def leading (B : Medium) (n : UnitSphere) (e : Vector) : ℝ :=
  2 / (3 * Real.pi) * (inner ℂ (moment0 B e) (moment1 B n e)).im

def gramBound (B : Medium) : ℝ := volume.real B.domain / (6 * Real.pi)

def gramCorrection (B : Medium) : ℝ := volume.real B.domain * B.radius ^ 2 / (3 * Real.pi)

def errorConstant (B : Medium) (e : Vector) : ℝ :=
  4 * ‖constantInput B e‖ ^ 2 *
    ((rho B * B.radius ^ 2 / 2 + correction B) * gramBound B * rho B * B.radius +
      rho B ^ 2 * gramCorrection B * B.radius +
      rho B * gramBound B * (rho B * B.radius ^ 3 / 6 + correction B * B.radius))

/-- The actual full-angle norm difference with the far-field normalization.
The physical scattering cross-section difference is `t^4` times this value. -/
def signedScattering (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) : ℝ :=
  (1 / (16 * Real.pi ^ 2)) *
    (‖domainRadiationMap t B.domain B.measurable B.finite
        (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))‖ ^ 2 -
     ‖domainRadiationMap t B.domain B.measurable B.finite
        (dynamicResponse B t ht (domainIncidentSource (-t) n e B.domain B.measurable B.finite))‖ ^ 2)

theorem signedScattering_inner (B : Medium) (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) :
    signedScattering B t ht n e =
      4 * (inner ℂ (u B t ht n e) (radiationGram t B.domain B.measurable B.finite (v B t ht n e))).im := by
  unfold signedScattering
  rw [SourceTaylor.source_decomposition, SourceTaylor.source_reverse_decomposition]
  change (1 / (16 * Real.pi ^ 2)) *
    (‖domainRadiationMap t B.domain B.measurable B.finite
        (dynamicResponse B t ht (cosineInput B t n e - Complex.I • sineInput B t n e))‖ ^ 2 -
     ‖domainRadiationMap t B.domain B.measurable B.finite
        (dynamicResponse B t ht (cosineInput B t n e + Complex.I • sineInput B t n e))‖ ^ 2) = _
  simp only [map_add, map_sub, map_smul]
  rw [norm_sq_opposite_i, radiationGram_inner]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  unfold u v
  ring

theorem leading_moment (B : Medium) (n : UnitSphere) (e : Vector) :
    4 * (inner ℂ (q0 B e) (radiationGram 0 B.domain B.measurable B.finite (q1 B n e))).im =
      leading B n e := by
  rw [radiationGram_zero_moment]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  unfold leading moment0 moment1
  ring

theorem denominator_moment (B : Medium) (e : Vector) :
    D0 B e = (inner ℂ e (moment0 B e)).im := by
  unfold D0 constantInput moment0
  rw [constantSource_inner_moment]

theorem errorConstant_nonneg (B : Medium) (e : Vector) : 0 ≤ errorConstant B e := by
  have hρ := (rho_pos B).le
  have hR := B.radius_nonneg
  have hC := correction_nonneg B
  unfold errorConstant gramBound gramCorrection
  positivity

theorem signedScattering_error (B : Medium) (hV : 0 < volume.real B.domain)
    (t : ℝ) (ht : 0 < t) (n : UnitSphere) (e : Vector) :
    |signedScattering B t ht n e - leading B n e * t| ≤ errorConstant B e * t ^ 3 := by
  let Q := radiationGram t B.domain B.measurable B.finite
  let Q0 := radiationGram 0 B.domain B.measurable B.finite
  have hρ := (rho_pos B).le
  have hR := B.radius_nonneg
  have hC := correction_nonneg B
  have hQ : ‖Q‖ ≤ gramBound B := radiationGram_norm_le t B.domain B.measurable B.finite
  have hQ0 : ‖Q0‖ ≤ gramBound B := radiationGram_norm_le 0 B.domain B.measurable B.finite
  have hdiff : ‖Q - Q0‖ ≤ gramCorrection B * t ^ 2 :=
    radiationGram_difference_norm_le t B.domain B.measurable B.finite B.radius_nonneg B.subset_ball
  have hu := u_error B hV t ht n e
  have hv := v_error B hV t ht n e
  have hq := q0_norm B e
  have hvn := v_norm B t ht n e
  have h := gram_cross_error Q Q0 (u B t ht n e) (v B t ht n e) (q0 B e) (q1 B n e) t
  have him : |(inner ℂ (u B t ht n e) (Q (v B t ht n e))).im -
      t * (inner ℂ (q0 B e) (Q0 (q1 B n e))).im| ≤
      ‖u B t ht n e - q0 B e‖ * ‖Q‖ * ‖v B t ht n e‖ +
      ‖q0 B e‖ * ‖Q - Q0‖ * ‖v B t ht n e‖ +
      ‖q0 B e‖ * ‖Q0‖ * ‖v B t ht n e - (t : ℂ) • q1 B n e‖ := by
    have hh := (Complex.abs_im_le_norm
      (inner ℂ (u B t ht n e) (Q (v B t ht n e)) -
        (t : ℂ) * inner ℂ (q0 B e) (Q0 (q1 B n e)))).trans h
    simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using hh
  rw [signedScattering_inner, ← leading_moment]
  have he : |4 * (inner ℂ (u B t ht n e) (Q (v B t ht n e))).im -
      4 * (inner ℂ (q0 B e) (Q0 (q1 B n e))).im * t| =
      4 * |(inner ℂ (u B t ht n e) (Q (v B t ht n e))).im -
        t * (inner ℂ (q0 B e) (Q0 (q1 B n e))).im| := by
    calc
      _ = |4 * ((inner ℂ (u B t ht n e) (Q (v B t ht n e))).im -
          t * (inner ℂ (q0 B e) (Q0 (q1 B n e))).im)| := by congr 1; ring
      _ = _ := by rw [abs_mul]; norm_num
  change |4 * (inner ℂ (u B t ht n e) (Q (v B t ht n e))).im -
      4 * (inner ℂ (q0 B e) (Q0 (q1 B n e))).im * t| ≤ _
  rw [he]
  apply (mul_le_mul_of_nonneg_left him (by norm_num : (0 : ℝ) ≤ 4)).trans
  unfold errorConstant
  have hg : 0 ≤ gramBound B := by unfold gramBound; positivity
  have hgc : 0 ≤ gramCorrection B := by unfold gramCorrection; positivity
  calc
    _ ≤ 4 * (((rho B * B.radius ^ 2 / 2 + correction B) * ‖constantInput B e‖ * t ^ 2) *
        gramBound B * (rho B * (t * B.radius * ‖constantInput B e‖)) +
      (rho B * ‖constantInput B e‖) * (gramCorrection B * t ^ 2) *
        (rho B * (t * B.radius * ‖constantInput B e‖)) +
      (rho B * ‖constantInput B e‖) * gramBound B *
        ((rho B * B.radius ^ 3 / 6 + correction B * B.radius) * ‖constantInput B e‖ * t ^ 3)) := by
      gcongr
    _ = _ := by ring

end FixedPatternScattering
end QuarticMaxwell
