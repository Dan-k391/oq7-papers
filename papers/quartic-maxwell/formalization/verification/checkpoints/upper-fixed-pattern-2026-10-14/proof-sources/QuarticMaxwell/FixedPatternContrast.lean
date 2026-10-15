import QuarticMaxwell.FixedPatternScattering
import QuarticMaxwell.PhysicalPowers

/-! The fixed-pattern quartic coefficient for independently supplied actual
outgoing weak Maxwell fields, with explicit interval and sixth-order error. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QuarticMaxwell
namespace FixedPatternContrast
open MeasureTheory Set OQ7Prescribed WeakMaterial FixedPatternWork FixedPatternScattering PhysicalPowers

def denominatorError (B : Medium) (e : Vector) : ℝ :=
  ‖constantInput B e‖ ^ 2 * (2 * rho B * B.radius ^ 2 + correction B)

def coefficient (B : Medium) (n : UnitSphere) (e : Vector) : ℝ :=
  |leading B n e| / D0 B e

def remainderConstant (B : Medium) (n : UnitSphere) (e : Vector) : ℝ :=
  2 * errorConstant B e / D0 B e +
    2 * |leading B n e| * denominatorError B e / D0 B e ^ 2

def interval (B : Medium) (e : Vector) : ℝ :=
  Real.sqrt (D0 B e / (2 * (denominatorError B e + 1)))

def contrast (B : Medium) (t : ℝ) (n : UnitSphere) (e : Vector)
    (s : State B t n e) (r : State B t (opposite n) e) : ℝ :=
  |PhysicalPowers.absorption B t s.electric - PhysicalPowers.absorption B t r.electric| /
    PhysicalPowers.extinction B t n e s.electric

theorem denominatorError_nonneg (B : Medium) (e : Vector) : 0 ≤ denominatorError B e := by
  have hρ := (rho_pos B).le
  have hC := correction_nonneg B
  unfold denominatorError
  positivity

theorem state_extinction_forwardWork (B : Medium) (t : ℝ) (ht : 0 < t)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ a b : Vector,
      bilinear a (B.susceptibility x b) = bilinear b (B.susceptibility x a))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e)
    (htr : bilinear (complexify (n : Position)) e = 0) (s : State B t n e) :
    PhysicalPowers.extinction B t n e s.electric = t * forwardWork B t ht n e := by
  rw [PhysicalPowers.state_extinction B ht n e htr s]
  unfold UniformBound.extinctionPower
  have hi := inner_im_symm (𝕜 := ℂ)
    (domainIncidentSource t n e B.domain B.measurable B.finite)
    (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))
  change (inner ℂ (domainIncidentSource t n e B.domain B.measurable B.finite)
    (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))).im =
      -(inner ℂ (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))
        (domainIncidentSource t n e B.domain B.measurable B.finite)).im at hi
  change -t * (inner ℂ (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))
    (domainIncidentSource t n e B.domain B.measurable B.finite)).im = _
  rw [← neg_eq_iff_eq_neg.mpr hi, actual_forward_decomposition B t ht hsym n e he]
  ring

theorem state_scattering_difference (B : Medium) (t : ℝ) (ht : 0 < t)
    (n : UnitSphere) (e : Vector) (htr : bilinear (complexify (n : Position)) e = 0)
    (s : State B t n e) (r : State B t (opposite n) e) :
    PhysicalPowers.scattering B t s.electric s.electric_L2 -
      PhysicalPowers.scattering B t r.electric r.electric_L2 =
        t ^ 4 * signedScattering B t ht n e := by
  rw [PhysicalPowers.scattering_eq_volume, PhysicalPowers.scattering_eq_volume,
    state_current_response B ht n e htr s,
    state_current_response B ht (opposite n) e (PhysicalPowers.opposite_transverse n e htr) r,
    PhysicalPowers.response_opposite B ht n e]
  unfold UniformBound.scatteringPower signedScattering
  change t ^ 4 / (16 * Real.pi ^ 2) *
      ‖domainRadiationMap t B.domain B.measurable B.finite
        (dynamicResponse B t ht (domainIncidentSource t n e B.domain B.measurable B.finite))‖ ^ 2 -
    t ^ 4 / (16 * Real.pi ^ 2) *
      ‖domainRadiationMap t B.domain B.measurable B.finite
        (dynamicResponse B t ht (domainIncidentSource (-t) n e B.domain B.measurable B.finite))‖ ^ 2 = _
  ring

theorem contrast_eq_quotient (B : Medium) (t : ℝ) (ht : 0 < t)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ a b : Vector,
      bilinear a (B.susceptibility x b) = bilinear b (B.susceptibility x a))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (s : State B t n e) (r : State B t (opposite n) e) :
    contrast B t n e s r = t ^ 3 * |signedScattering B t ht n e| / forwardWork B t ht n e := by
  have hb := PhysicalPowers.state_power_balance B ht n e htr s
  have hr := PhysicalPowers.state_power_balance B ht (opposite n) e
    (PhysicalPowers.opposite_transverse n e htr) r
  have hx := PhysicalPowers.state_extinction_reciprocal B ht hsym n e he htr s r
  have hdiff := state_scattering_difference B t ht n e htr s r
  have hab : PhysicalPowers.absorption B t s.electric - PhysicalPowers.absorption B t r.electric =
      -(t ^ 4 * signedScattering B t ht n e) := by linarith
  unfold contrast
  rw [hab, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ 4),
    state_extinction_forwardWork B t ht hsym n e he htr s]
  by_cases hd : forwardWork B t ht n e = 0
  · simp [hd]
  · field_simp

theorem interval_pos (B : Medium) (hV : 0 < volume.real B.domain)
    (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) : 0 < interval B e := by
  unfold interval
  exact Real.sqrt_pos.mpr (div_pos (D0_pos B hV n e hen)
    (by have hE := denominatorError_nonneg B e; positivity))

theorem coefficient_moment (B : Medium) (n : UnitSphere) (e : Vector) :
    coefficient B n e = (2 / (3 * Real.pi)) *
      |(inner ℂ (moment0 B e) (moment1 B n e)).im| / (inner ℂ e (moment0 B e)).im := by
  unfold coefficient leading
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (3 * Real.pi)), denominator_moment]

theorem fixed_pattern_quartic (B : Medium) (hV : 0 < volume.real B.domain)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ a b : Vector,
      bilinear a (B.susceptibility x b) = bilinear b (B.susceptibility x a))
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (t : ℝ) (ht : 0 < t) (hsmall : t ≤ interval B e)
    (s : State B t n e) (r : State B t (opposite n) e) :
    |contrast B t n e s r - coefficient B n e * t ^ 4| ≤ remainderConstant B n e * t ^ 6 := by
  have hD := D0_pos B hV n e hen
  have hE := denominatorError_nonneg B e
  have hforward := forward_work_error B hV t ht n e
  change |forwardWork B t ht n e - D0 B e| ≤ denominatorError B e * t ^ 2 at hforward
  have hδ := interval_pos B hV n e hen
  have hδ2 : interval B e ^ 2 = D0 B e / (2 * (denominatorError B e + 1)) :=
    Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 ≤ interval B e ^ 2 := (sq_le_sq₀ ht.le hδ.le).mpr hsmall
  have hδeq : 2 * (denominatorError B e + 1) * interval B e ^ 2 = D0 B e := by
    rw [hδ2]
    field_simp
  have hsmallE : denominatorError B e * t ^ 2 ≤ D0 B e / 2 := by
    have hh := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 2 * (denominatorError B e + 1) by positivity)
    rw [hδeq] at hh
    nlinarith only [hh, sq_nonneg t]
  have hd : D0 B e / 2 ≤ forwardWork B t ht n e := by
    have hlo := (abs_le.mp hforward).1
    linarith
  rw [contrast_eq_quotient B t ht hsym n e he htr s r]
  exact quartic_quotient_error ht.le hD (errorConstant_nonneg B e) hE hd
    (signedScattering_error B hV t ht n e) hforward

end FixedPatternContrast
end QuarticMaxwell
