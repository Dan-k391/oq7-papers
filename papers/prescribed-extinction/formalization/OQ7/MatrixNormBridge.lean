import OQ7.Transfer
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Normed.Group.Continuity

noncomputable section
namespace OQ7
open Filter

section Operator
open scoped Matrix.Norms.Operator

/-- The submultiplicative row-sum matrix norm used in exponential estimates. -/
def matrixOperatorNorm (F : Mat2) : ℝ := ‖F‖

theorem matrixOperatorNorm_nonneg (F : Mat2) : 0 ≤ matrixOperatorNorm F := norm_nonneg F

theorem matrix_entry_norm_le_operator (F : Mat2) (i j : Fin 2) :
    ‖F i j‖ ≤ matrixOperatorNorm F := by
  unfold matrixOperatorNorm
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast
    ((Finset.single_le_sum (fun k _ => (show 0 ≤ ‖F i k‖₊ by positivity))
      (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun l : Fin 2 => ∑ k : Fin 2, ‖F l k‖₊) (Finset.mem_univ i)))

end Operator

section Elementwise
open scoped Matrix.Norms.Elementwise Asymptotics Topology

theorem matrix_elementwise_norm_le_operator (F : Mat2) : ‖F‖ ≤ matrixOperatorNorm F := by
  apply (Matrix.norm_le_iff (matrixOperatorNorm_nonneg F)).mpr
  exact matrix_entry_norm_le_operator F

/-- Explicit norm handoff for core perturbation orders; the hypothesis's norm
is named so it cannot be silently read with the matching norm instance. -/
theorem matrix_isBigO_of_operatorNorm {ι : Type*} {l : Filter ι}
    {F : ι → Mat2} {r : ι → ℝ} (h : (fun j => matrixOperatorNorm (F j)) =O[l] r) :
    F =O[l] r := by
  apply (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall (fun j => ?_))).trans h
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (matrixOperatorNorm_nonneg _)] using
    matrix_elementwise_norm_le_operator (F j)

theorem matrix_tendsto_of_operatorNorm {ι : Type*} {l : Filter ι}
    {F : ι → Mat2} {F₀ : Mat2}
    (h : Tendsto (fun j => matrixOperatorNorm (F j - F₀)) l (𝓝 0)) :
    Tendsto F l (𝓝 F₀) := by
  have hs : Tendsto (fun j => F j - F₀) l (𝓝 (0 : Mat2)) :=
    squeeze_zero_norm (fun j => matrix_elementwise_norm_le_operator (F j - F₀)) h
  simpa using hs.add_const F₀

end Elementwise

#print axioms matrixOperatorNorm_nonneg
#print axioms matrix_entry_norm_le_operator
#print axioms matrix_elementwise_norm_le_operator
#print axioms matrix_isBigO_of_operatorNorm
#print axioms matrix_tendsto_of_operatorNorm
end OQ7
