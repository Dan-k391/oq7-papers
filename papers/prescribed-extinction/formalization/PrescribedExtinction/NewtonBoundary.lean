import PrescribedExtinction.SphereMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Limits of the actual angular boundary integrals in the Newton Hessian
calculation. These limits do not assert the missing punctured integration by
parts identity or the distributional Hessian formula. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Filter Set
open scoped Topology

theorem sphere_test_moment_continuous (φ : ScalarTest) (i j : Fin 3) :
    Continuous (fun r : ℝ => ∫ n : UnitSphere,
      (n : Position) i * (n : Position) j * φ (r • (n : Position)) ∂sphereArea) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := sphereArea) (s := univ)
    (f := fun r : ℝ => fun n : UnitSphere =>
      (n : Position) i * (n : Position) j * φ (r • (n : Position)))
    (by have hc := φ.continuous; fun_prop) isCompact_univ
  simpa only [Measure.restrict_univ] using h

theorem sphere_test_moment_zero (φ : ScalarTest) (i j : Fin 3) :
    (∫ n : UnitSphere, (n : Position) i * (n : Position) j * φ ((0 : ℝ) • (n : Position)) ∂sphereArea) =
      (if i = j then (4 * Real.pi) / 3 else 0) * φ 0 := by
  simp only [zero_smul, integral_mul_const, sphere_second_moment]

def newtonContactBoundary (φ : ScalarTest) (i j : Fin 3) (r : ℝ) : ℝ :=
  -(4 * Real.pi)⁻¹ * ∫ n : UnitSphere,
    (n : Position) i * (n : Position) j * φ (r • (n : Position)) ∂sphereArea

theorem newtonContactBoundary_tendsto (φ : ScalarTest) (i j : Fin 3) :
    Tendsto (newtonContactBoundary φ i j) (𝓝 (0 : ℝ))
      (𝓝 (-((if i = j then 1 else 0) / 3) * φ 0)) := by
  have h := ((sphere_test_moment_continuous φ i j).continuousAt (x := 0)).const_mul (-(4 * Real.pi)⁻¹)
  have he : -(4 * Real.pi)⁻¹ *
      (∫ n : UnitSphere, (n : Position) i * (n : Position) j * φ ((0 : ℝ) • (n : Position)) ∂sphereArea) =
      -((if i = j then 1 else 0) / 3) * φ 0 := by
    rw [sphere_test_moment_zero]
    split_ifs <;> field_simp
    ring
  unfold newtonContactBoundary
  rw [← he]
  exact h.tendsto

theorem sphere_test_derivative_continuous (φ : ScalarTest) (i j : Fin 3) :
    Continuous (fun r : ℝ => ∫ n : UnitSphere,
      (n : Position) j * (testPartial i φ) (r • (n : Position)) ∂sphereArea) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := sphereArea) (s := univ)
    (f := fun r : ℝ => fun n : UnitSphere =>
      (n : Position) j * (testPartial i φ) (r • (n : Position)))
    (by have hc := (testPartial i φ).continuous; fun_prop) isCompact_univ
  simpa only [Measure.restrict_univ] using h

def newtonDerivativeBoundary (φ : ScalarTest) (i j : Fin 3) (r : ℝ) : ℝ :=
  -r / (4 * Real.pi) * ∫ n : UnitSphere,
    (n : Position) j * (testPartial i φ) (r • (n : Position)) ∂sphereArea

theorem newtonDerivativeBoundary_tendsto (φ : ScalarTest) (i j : Fin 3) :
    Tendsto (newtonDerivativeBoundary φ i j) (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous (newtonDerivativeBoundary φ i j) := by
    exact (continuous_neg.div_const _).mul (sphere_test_derivative_continuous φ i j)
  simpa only [newtonDerivativeBoundary, neg_zero, zero_div, zero_mul] using
    (hc.continuousAt (x := 0)).tendsto

end OQ7Prescribed
