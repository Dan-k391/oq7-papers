import QuarticMaxwell.ProjectionGeometry
import QuarticMaxwell.GreenEigenvalues
import PrescribedExtinction.DyadicRemainder

/-! A sharp norm estimate for the actual dyadic remainder. The orthogonal
radial/tangential split avoids the triangle-inequality loss in the old bound.
This is a kernel estimate; the support rearrangement and Schur operator bridge
are separate results. -/

noncomputable section
namespace QuarticMaxwell
open OQ7Prescribed

def radialProjection (x : Position) : Vector →L[ℂ] Vector :=
  (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ (complexify x) (complexify x)

theorem radialProjection_orthogonal (x : Position) (hx : x ≠ 0) (v : Vector) :
    inner ℂ (radialProjection x v) (v - radialProjection x v) = 0 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hs : inner ℂ (complexify x) (complexify x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    exact congrArg Complex.ofReal (complexify_norm_sq x)
  have h : inner ℂ (complexify x) (v - radialProjection x v) = 0 := by
    simp only [radialProjection, smul_apply,
      InnerProductSpace.rankOne_apply, inner_sub_right, inner_smul_right, smul_smul, hs]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow]
    field_simp [Complex.ofReal_ne_zero.mpr hn]
    ring
  change inner ℂ (((((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
    (inner ℂ (complexify x) v • complexify x)) (v - radialProjection x v) = 0
  rw [inner_smul_left, inner_smul_left, h, mul_zero, mul_zero]

theorem dyadicRemainder_radial_tangential (k : ℝ) (x : Position) (hx : x ≠ 0) :
    dyadicRemainder k x =
      radialRemainderEigenvalue k ‖x‖ • radialProjection x +
      tangentialRemainderEigenvalue k ‖x‖ •
        (ContinuousLinearMap.id ℂ Vector - radialProjection x) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [dyadicRemainder_cancel]
  ext v i
  simp only [radialProjection, radialRemainderEigenvalue, tangentialRemainderEigenvalue,
    greenB, add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.rankOne_apply, smul_smul]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_ofNat, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem dyadicRemainder_sharp_norm_le {k : ℝ} (hk : 0 ≤ k) (x : Position) :
    ‖dyadicRemainder k x‖ ≤ 3 * k ^ 2 / (8 * Real.pi * ‖x‖) := by
  by_cases hx : x = 0
  · subst x
    simp [dyadicRemainder, classicalDyadic, outgoingRadial,
      outgoingRadialFirst, outgoingRadialSecond]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [dyadicRemainder_radial_tangential k x hx]
  apply orthogonal_split_norm_le (radialProjection x) (radialProjection_orthogonal x hx)
  · positivity
  · exact radial_eigenvalue_norm_le hk hr
  · exact tangential_eigenvalue_norm_le hk hr

end QuarticMaxwell
