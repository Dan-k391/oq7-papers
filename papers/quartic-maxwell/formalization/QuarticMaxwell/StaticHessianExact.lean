import QuarticMaxwell.StaticHessian

/-! Exact radial eigenvalue and attained operator norm of the actual Newton
Hessian.  The upper bound is supplemented by a concrete unit radial vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.StaticHessian
open OQ7Prescribed

theorem radialProjection_normalizedComplex (r : Position) (hr : r ≠ 0) :
    radialProjection r (normalizedComplex r) = normalizedComplex r := by
  rw [← normalizedComplex_projection]
  simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, normalizedComplex_norm r hr]

theorem newtonHessianOperator_radial (r : Position) (hr : r ≠ 0) :
    newtonHessianOperator r (normalizedComplex r) =
      (((1 / (2 * Real.pi * ‖r‖ ^ 3) : ℝ) : ℂ)) • normalizedComplex r := by
  simp only [newtonHessianOperator, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply,
    radialProjection_normalizedComplex r hr]
  have he : (3 : ℂ) • normalizedComplex r - normalizedComplex r = (2 : ℂ) • normalizedComplex r := by module
  rw [he, smul_smul]
  congr 1
  push_cast
  ring

theorem newtonHessianOperator_norm (r : Position) (hr : r ≠ 0) :
    ‖newtonHessianOperator r‖ = 1 / (2 * Real.pi * ‖r‖ ^ 3) := by
  apply le_antisymm (newtonHessianOperator_norm_le r hr)
  have h := (newtonHessianOperator r).le_opNorm (normalizedComplex r)
  rw [newtonHessianOperator_radial r hr, norm_smul, normalizedComplex_norm r hr,
    mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by have hn := norm_pos_iff.mpr hr; positivity : 0 < 1 / (2 * Real.pi * ‖r‖ ^ 3))] at h
  exact h

end QuarticMaxwell.StaticHessian
