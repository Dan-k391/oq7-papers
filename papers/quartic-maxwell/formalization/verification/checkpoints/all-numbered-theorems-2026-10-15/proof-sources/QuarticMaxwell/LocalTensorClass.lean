import QuarticMaxwell.WeakMaterial
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Exact local-to-global and literal matrix-class correspondences for the
arbitrary measurable tensor theorem. No material assumption is imposed outside D. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
namespace LocalTensorClass
open MeasureTheory Set OQ7Prescribed
open scoped Matrix.Norms.L2Operator

def zeroExtension (D : Set Position) (χ : Position → Vector →L[ℂ] Vector) := D.indicator χ

theorem zeroExtension_measurable (D : Set Position) (hD : MeasurableSet D)
    (χ : Position → Vector →L[ℂ] Vector) (hχ : AEStronglyMeasurable χ (volume.restrict D)) :
    AEStronglyMeasurable (zeroExtension D χ) volume :=
  (aestronglyMeasurable_indicator_iff hD).mpr hχ

theorem zeroExtension_on_domain (D : Set Position) (χ : Position → Vector →L[ℂ] Vector)
    {x : Position} (hx : x ∈ D) : zeroExtension D χ x = χ x := indicator_of_mem hx χ

theorem zeroExtension_outside (D : Set Position) (χ : Position → Vector →L[ℂ] Vector)
    {x : Position} (hx : x ∉ D) : zeroExtension D χ x = 0 := indicator_of_notMem hx χ

theorem zeroExtension_cap (D : Set Position) (χ : Position → Vector →L[ℂ] Vector) {M : ℝ}
    (hcap : ∀ᵐ x ∂volume, x ∈ D → ‖χ x‖ ≤ M) :
    ∀ᵐ x ∂volume, x ∈ D → ‖zeroExtension D χ x‖ ≤ M := by
  filter_upwards [hcap] with x hx hd
  rw [zeroExtension_on_domain D χ hd]
  exact hx hd

theorem zeroExtension_loss (D : Set Position) (χ : Position → Vector →L[ℂ] Vector) {m : ℝ}
    (hloss : ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector, m * ‖v‖ ^ 2 ≤ (inner ℂ v (χ x v)).im) :
    ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector,
      m * ‖v‖ ^ 2 ≤ (inner ℂ v (zeroExtension D χ x v)).im := by
  filter_upwards [hloss] with x hx hd
  rw [zeroExtension_on_domain D χ hd]
  exact hx hd

theorem zeroExtension_reciprocal (D : Set Position) (χ : Position → Vector →L[ℂ] Vector)
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u)) :
    ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector,
      bilinear u (zeroExtension D χ x v) = bilinear v (zeroExtension D χ x u) := by
  filter_upwards [hsym] with x hx hd
  rw [zeroExtension_on_domain D χ hd]
  exact hx hd

def matrixOperator (A : Tensor) : Vector →L[ℂ] Vector :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)) A

theorem matrixOperator_apply (A : Tensor) (v : Vector) : matrixOperator A v = tensorApply A v := by
  exact Matrix.toEuclideanCLM_toLp A (WithLp.ofLp v)

theorem matrixOperator_norm (A : Tensor) : ‖matrixOperator A‖ = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

theorem matrixOperator_bijective : Function.Bijective matrixOperator :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)).bijective

theorem bilinear_transpose (A : Tensor) (u v : Vector) :
    bilinear u (matrixOperator A v) = bilinear v (matrixOperator A.transpose u) := by
  rw [matrixOperator_apply, matrixOperator_apply]
  change (∑ i : Fin 3, u i * ∑ j : Fin 3, A i j * v j) =
    ∑ i : Fin 3, v i * ∑ j : Fin 3, A j i * u j
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixOperator_reciprocal (A : Tensor) (hA : A.transpose = A) (u v : Vector) :
    bilinear u (matrixOperator A v) = bilinear v (matrixOperator A u) := by
  rw [bilinear_transpose, hA]

theorem matrixOperator_measurable (A : Position → Tensor)
    (hA : AEStronglyMeasurable A volume) : AEStronglyMeasurable (fun x => matrixOperator (A x)) volume := by
  exact ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 3)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous.comp_aestronglyMeasurable hA)

end LocalTensorClass
end QuarticMaxwell
