import PrescribedExtinction.PhysicalPolarization
import PrescribedExtinction.ComplexCoerciveInverse
import Mathlib.Topology.Order.Compact

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem pairing_eq_inner (u v : Vector) : pairing u v = inner ℂ u v := by
  simp [pairing, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem tensor_quadratic_eq_inner (T : Tensor) (v : Vector) :
    quadratic T v = inner ℂ v (tensorMap T v) := by
  rw [quadratic, tensorMap_apply, pairing_eq_inner]

theorem vector_inner_real_smul (A : Vector →L[ℂ] Vector) (r : ℝ) (v : Vector) :
    inner ℂ ((r : ℂ) • v) (A ((r : ℂ) • v)) = (r ^ 2 : ℝ) • inner ℂ v (A v) := by
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_pow]
  ring

theorem vector_strict_imaginary_coercive (A : Vector →L[ℂ] Vector)
    (hpos : ∀ v : Vector, v ≠ 0 → 0 < (inner ℂ v (A v)).im) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Vector, c * ‖v‖ ^ 2 ≤ (inner ℂ v (A v)).im := by
  have hc : Continuous (fun v : Vector => (inner ℂ v (A v)).im) :=
    Complex.imCLM.continuous.comp (continuous_id.inner A.continuous)
  have hne : (Metric.sphere (0 : Vector) 1).Nonempty := by
    refine ⟨basisC 0, ?_⟩
    simp [Metric.mem_sphere, dist_zero_right, basisC]
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : Vector) 1).exists_isMinOn hne hc.continuousOn
  have hwne : w ≠ 0 := by
    intro hz
    simpa [hz] using hw
  refine ⟨(inner ℂ w (A w)).im, hpos w hwne, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
    simp [norm_smul, Complex.norm_real, abs_inv, abs_of_pos hn, hn.ne']
  have hbound := hmin (show ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ Metric.sphere (0 : Vector) 1 from by
    simpa [Metric.mem_sphere, dist_zero_right] using hunit)
  change (inner ℂ w (A w)).im ≤
    (inner ℂ (((‖v‖⁻¹ : ℝ) : ℂ) • v) (A (((‖v‖⁻¹ : ℝ) : ℂ) • v))).im at hbound
  rw [vector_inner_real_smul] at hbound
  have hid : ((‖v‖⁻¹ ^ 2 : ℝ) • inner ℂ v (A v)).im = (inner ℂ v (A v)).im / ‖v‖ ^ 2 := by
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_add]
    simp [div_eq_mul_inv, inv_pow, mul_comm]
  rw [hid] at hbound
  exact (le_div_iff₀ (sq_pos_of_pos hn)).mp hbound

theorem susceptibility_quadratic_im (T : Tensor) (v : Vector) :
    (inner ℂ v (tensorMap (T - 1) v)).im = (quadratic T v).im := by
  have he : tensorMap (T - 1) v = tensorMap T v - v := by
    ext i
    simp [tensorMap_apply, tensorApply, Matrix.sub_mulVec, PiLp.sub_apply]
  have hz : (inner ℂ v v).im = 0 := inner_self_im (𝕜 := ℂ) v
  rw [he, inner_sub_right, Complex.sub_im, hz, sub_zero, ← tensor_quadratic_eq_inner]

theorem admissible_susceptibility_imaginary_coercive (P Q : ℝ) (T : Tensor)
    (hT : MaterialAdmissible P Q T) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Vector, c * ‖v‖ ^ 2 ≤ (inner ℂ v (tensorMap (T - 1) v)).im := by
  apply vector_strict_imaginary_coercive
  intro v hv
  rw [susceptibility_quadratic_im]
  exact hT.2.2.1 v hv

/-- Strict physical tensor loss yields a genuine inverse susceptibility,
with an explicit inverse norm bound and a strictly negative inverse loss.
This does not yet invert the scattering operator containing T_k. -/
theorem admissible_susceptibility_bounded_inverse (P Q : ℝ) (T : Tensor)
    (hT : MaterialAdmissible P Q T) :
    ∃ c : ℝ, 0 < c ∧ ∃ e : Vector ≃L[ℂ] Vector,
      (∀ v : Vector, e v = tensorMap (T - 1) v) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ 1 / c ∧
      (∀ v : Vector, (c / (‖tensorMap (T - 1)‖ + 1) ^ 2) * ‖v‖ ^ 2 ≤ -(inner ℂ v (e.symm v)).im) := by
  obtain ⟨c, hc, hcoer⟩ := admissible_susceptibility_imaginary_coercive P Q T hT
  refine ⟨c, hc, complexImaginaryCoerciveEquiv (tensorMap (T - 1)) c hc hcoer, ?_, ?_, ?_⟩
  · exact complexImaginaryCoerciveEquiv_apply _ _ _ _
  · exact complexImaginaryCoerciveEquiv_inverse_norm_le _ _ _ _
  · exact complexImaginaryCoerciveEquiv_inverse_imaginary_bound _ _ _ _

end OQ7Prescribed
