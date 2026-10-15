import QuarticMaxwell.BlockInteractionMoments
import QuarticMaxwell.TwoSphereGeometry
import QuarticMaxwell.HomogeneousScalars
import QuarticMaxwell.FixedPatternScattering
import PrescribedExtinction.DyadicAxisRepresentation

/-! Actual static moments of homogeneous unequal finite spheres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed SphereStatic SphereResponse SphereExterior SphereDoubleMean
  BlockSourceMoments BlockInteractionMoments TwoSupportStatic TwoSupportBounds TwoSphereGeometry
  SourceTaylor FixedPatternWork FixedPatternScattering MeasureTheory Set

structure Parameters where
  n : UnitSphere
  e : OQ7Prescribed.Position
  e_unit : ‖e‖ = 1
  transverse : inner ℝ (n : OQ7Prescribed.Position) e = 0
  μ : ℝ
  μ_pos : 0 < μ
  a : ℝ
  a_pos : 0 < a
  a_small : a ≤ 1 / 20

def Parameters.electric (P : Parameters) : Vector := complexify P.e
def Parameters.material (P : Parameters) : ScalarPair := homogeneousPair P.μ P.μ_pos
def Parameters.body (P : Parameters) : WeakMaterial.Medium := medium P.n P.a P.a_pos P.a_small P.material
def Parameters.A (P : Parameters) : DomainL2 P.body.domain →L[ℂ] DomainL2 P.body.domain :=
  blockInverse (leftBall P.n P.a) (rightBall P.n P.a) measurableSet_ball measurableSet_ball P.material
def Parameters.C (P : Parameters) : DomainL2 P.body.domain →L[ℂ] DomainL2 P.body.domain :=
  interaction (leftBall P.n P.a) (rightBall P.n P.a) measurableSet_ball measurableSet_ball

def Parameters.f0 (P : Parameters) : DomainL2 P.body.domain := constantInput P.body P.electric
def Parameters.f1 (P : Parameters) : DomainL2 P.body.domain := linearInput P.body P.n P.electric

def Parameters.moment (P : Parameters) : DomainL2 P.body.domain →L[ℂ] Vector :=
  MomentOperator.map P.body.domain P.body.finite

def Parameters.p0 (P : Parameters) : Vector := P.moment (staticResponse P.body P.f0)
def Parameters.p1 (P : Parameters) : Vector := P.moment (staticResponse P.body P.f1)
def Parameters.p0b (P : Parameters) : Vector := P.moment (P.A P.f0)
def Parameters.p1b (P : Parameters) : Vector := P.moment (P.A P.f1)
def Parameters.p0c (P : Parameters) : Vector := P.moment (P.A (P.C (P.A P.f0)))
def Parameters.p1c (P : Parameters) : Vector := P.moment (P.A (P.C (P.A P.f1)))

theorem Parameters.electric_norm (P : Parameters) : ‖P.electric‖ = 1 := by
  rw [Parameters.electric, complexify_norm, P.e_unit]

theorem Parameters.body_volume (P : Parameters) : volume.real P.body.domain = 12 * Real.pi * P.a ^ 3 :=
  medium_volume P.n P.a P.a_pos P.a_small P.material

theorem Parameters.center_projection_left (P : Parameters) :
    inner ℝ (P.n : OQ7Prescribed.Position) (leftCenter P.n) = -1 / 2 := by
  simp [leftCenter, inner_smul_right, inner_self_eq_norm_sq_to_K]

theorem Parameters.center_projection_right (P : Parameters) :
    inner ℝ (P.n : OQ7Prescribed.Position) (rightCenter P.n) = 1 / 2 := by
  simp [rightCenter, inner_smul_right, inner_self_eq_norm_sq_to_K]

theorem Parameters.p0b_formula (P : Parameters) :
    P.p0b = (beta (HomogeneousScalars.contrast P.μ) * (12 * Real.pi * P.a ^ 3 : ℝ)) • P.electric := by
  have h := moment_blockInverse_constant (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) P.material P.electric
  change P.p0b = _ at h
  rw [ball_volume_real (leftCenter P.n) P.a_pos.le,
    ball_volume_real (rightCenter P.n) (by linarith [P.a_pos] : 0 ≤ 2 * P.a)] at h
  convert h using 1
  unfold Parameters.material homogeneousPair HomogeneousScalars.contrast
  push_cast
  ring

theorem Parameters.p1b_formula (P : Parameters) :
    P.p1b = (beta (HomogeneousScalars.contrast P.μ) * (14 * Real.pi * P.a ^ 3 / 3 : ℝ)) • P.electric := by
  have h := moment_blockInverse_affine (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) P.material P.n P.electric (3 / 5) (domain_subset P.n P.a_small)
  change P.p1b = _ at h
  rw [P.center_projection_left, P.center_projection_right,
    ball_volume_real (leftCenter P.n) P.a_pos.le,
    ball_volume_real (rightCenter P.n) (by linarith [P.a_pos] : 0 ≤ 2 * P.a)] at h
  convert h using 1
  unfold Parameters.material homogeneousPair HomogeneousScalars.contrast
  push_cast
  ring

theorem Parameters.transverse_hessian (P : Parameters) :
    StaticHessian.newtonHessianOperator (leftCenter P.n - rightCenter P.n) P.electric =
      (-1 / (4 * Real.pi) : ℂ) • P.electric := by
  have hn : ‖(P.n : OQ7Prescribed.Position)‖ = 1 := by simp
  have he : inner ℂ (complexify (P.n : OQ7Prescribed.Position)) P.electric = 0 := by
    rw [Parameters.electric, ← axisCoupling_eq_inner, axisCoupling_complexify_inner, P.transverse]
    rfl
  have hc : leftCenter P.n - rightCenter P.n = -(P.n : OQ7Prescribed.Position) := by
    unfold leftCenter rightCenter
    module
  rw [hc, hessian_even]
  simp [StaticHessian.newtonHessianOperator, radialProjection, hn,
    InnerProductSpace.rankOne_apply, he]
  module

theorem Parameters.p0c_formula (P : Parameters) :
    P.p0c = (-(64 * Real.pi / 9 : ℝ) * (beta (HomogeneousScalars.contrast P.μ)) ^ 2 *
      (P.a ^ 6 : ℝ)) • P.electric := by
  have hsep : P.a + 2 * P.a < ‖leftCenter P.n - rightCenter P.n‖ := by
    rw [center_distance]
    linarith [P.a_small]
  have h := first_constant_moment (leftCenter P.n) (rightCenter P.n) P.a (2 * P.a)
    P.a_pos (by linarith [P.a_pos]) (gap P.a) (gap_pos P.a_small) hsep (sphere_separation P.n P.a) P.material P.electric
  change P.p0c = _ at h
  rw [P.transverse_hessian, smul_smul] at h
  convert h using 1
  unfold Parameters.material homogeneousPair HomogeneousScalars.contrast ballVolume
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

end QuarticMaxwell.HomogeneousMoments

namespace QuarticMaxwell.HomogeneousMoments
open OQ7Prescribed SphereStatic SphereResponse SphereExterior SphereDoubleMean
  BlockSourceMoments BlockInteractionMoments TwoSupportStatic TwoSupportBounds TwoSphereGeometry
  SourceTaylor FixedPatternWork FixedPatternScattering MeasureTheory Set

theorem phase_moment (e : Vector) (he : ‖e‖ = 1) (z : ℂ) (A B C : ℝ) :
    (inner ℂ (((A : ℂ) * z) • e + ((C : ℂ) * z ^ 2) • e) (((B : ℂ) * z) • e)).im =
      -B * C * ‖z‖ ^ 2 * z.im := by
  rw [inner_add_left, inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K, he]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, pow_two]
  ring

theorem Parameters.leading_moment (P : Parameters) :
    (inner ℂ (P.p0b + P.p0c) P.p1b).im = HomogeneousScalars.leading P.μ * P.a ^ 9 := by
  rw [P.p0b_formula, P.p0c_formula, P.p1b_formula]
  have h := phase_moment P.electric P.electric_norm (beta (HomogeneousScalars.contrast P.μ))
    (12 * Real.pi * P.a ^ 3) (14 * Real.pi * P.a ^ 3 / 3) (-(64 * Real.pi / 9) * P.a ^ 6)
  calc
    _ = -(14 * Real.pi * P.a ^ 3 / 3) * (-(64 * Real.pi / 9) * P.a ^ 6) *
        ‖beta (HomogeneousScalars.contrast P.μ)‖ ^ 2 * (beta (HomogeneousScalars.contrast P.μ)).im := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_neg, mul_comm, mul_left_comm, mul_assoc] using h
    _ = ((896 * Real.pi ^ 2 / 27) * P.a ^ 9) *
        (‖beta (HomogeneousScalars.contrast P.μ)‖ ^ 2 * (beta (HomogeneousScalars.contrast P.μ)).im) := by ring
    _ = _ := by rw [HomogeneousScalars.beta_leading_factor]; unfold HomogeneousScalars.leading; ring

theorem Parameters.cross_bound (P : Parameters) :
    crossBound (leftBall P.n P.a) (rightBall P.n P.a) (gap P.a) ≤ 4 * P.a ^ 3 := by
  rw [crossBound_formula P.n P.a_pos P.a_small]
  have hg : (4 / 5 : ℝ) ≤ gap P.a := by unfold gap; linarith [P.a_small]
  have hh : Real.sqrt 2 / (3 * (gap P.a) ^ 3) ≤ 1 := by
    apply (show Real.sqrt 2 / (3 * (gap P.a) ^ 3) ≤ Real.sqrt 2 / (3 * (4 / 5 : ℝ) ^ 3) by gcongr).trans
    exact OQ7Quartic.coupling_homogeneous
  calc
    _ = (4 * P.a ^ 3) * (Real.sqrt 2 / (3 * (gap P.a) ^ 3)) := by ring
    _ ≤ (4 * P.a ^ 3) * 1 := mul_le_mul_of_nonneg_left hh (by positivity [P.a_pos])
    _ = _ := mul_one _

theorem Parameters.static_norm (P : Parameters) : ‖staticResponse P.body‖ ≤ P.μ := by
  have h := response_resource_norm_le (leftBall P.n P.a) (rightBall P.n P.a)
    Metric.isOpen_ball Metric.isOpen_ball P.material
  rw [response_eq_staticResponse P.n P.a P.a_pos P.a_small P.material] at h
  change ‖staticResponse P.body‖ ≤ P.material.cap ^ 2 / P.material.loss at h
  rw [Parameters.material, homogeneous_cap, homogeneous_loss, sq,
    mul_div_cancel_right₀ P.μ (ne_of_gt P.μ_pos)] at h
  exact h

theorem Parameters.f0_norm (P : Parameters) : ‖P.f0‖ = Real.sqrt (volume.real P.body.domain) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  have h := constant_norm_sq P.body.domain P.body.measurable P.body.finite P.n P.electric
  change ‖P.f0‖ ^ 2 = volume.real P.body.domain * ‖P.electric‖ ^ 2 at h
  rw [P.electric_norm] at h
  rw [Real.sq_sqrt measureReal_nonneg]
  simpa only [one_pow, mul_one] using h

theorem Parameters.f1_norm (P : Parameters) :
    ‖P.f1‖ ≤ (3 / 5 : ℝ) * Real.sqrt (volume.real P.body.domain) := by
  have h := moment_norm P.body.domain P.body.measurable P.body.finite P.n P.electric P.body.subset_ball
  change ‖P.f1‖ ≤ (3 / 5 : ℝ) * ‖P.f0‖ at h
  rw [P.f0_norm] at h
  exact h

end QuarticMaxwell.HomogeneousMoments
