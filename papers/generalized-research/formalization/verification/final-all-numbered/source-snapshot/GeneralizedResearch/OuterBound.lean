import GeneralizedResearch.MiddleParameters
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

/-! # The overlap outer branch in the actual real matrix relaxation -/
noncomputable section
open scoped Matrix
namespace GeneralizedResearch
namespace OuterBound
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def P : Mat2 := (1 / 2 : ℝ) • !![1, 1; 1, 1]
def W (rho : ℝ) : Mat2 := !![(1 + rho) / 2, 0; 0, -(1 - rho) / 2]
def E : Mat2 := !![0, 1 / 2; 1 / 2, 0]

theorem offdiag_bounds (Q : Mat2) (hQ : Q.PosSemidef)
    (hI : ((1 : Mat2) - Q).PosSemidef) :
    -(1 / 2 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ 1 / 2 := by
  have hoff : Q 1 0 = Q 0 1 := by simpa using hQ.1.apply 0 1
  have hp := hQ.dotProduct_mulVec_nonneg ![1, 1]
  have hm := hQ.dotProduct_mulVec_nonneg ![1, -1]
  have hip := hI.dotProduct_mulVec_nonneg ![1, 1]
  have him := hI.dotProduct_mulVec_nonneg ![1, -1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hoff] at hp hm hip him
  constructor <;> linarith

theorem abs_offdiag_le_half (Q : Mat2) (hQ : Q.PosSemidef)
    (hI : ((1 : Mat2) - Q).PosSemidef) : |Q 0 1| ≤ 1 / 2 := by
  exact abs_le.mpr (offdiag_bounds Q hQ hI)

theorem overlap_branch_upper_bound {rho : ℝ} (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
    (Q : Mat2) (hQ : Q.PosSemidef)
    (hI : ((1 : Mat2) - Q).PosSemidef) :
    2 * Real.sqrt (1 - rho ^ 2) * |Q 0 1| ≤ Real.sqrt (1 - rho ^ 2) := by
  have hoff := abs_offdiag_le_half Q hQ hI
  have hs := Real.sqrt_nonneg (1 - rho ^ 2)
  nlinarith

theorem P_hermitian : P.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Matrix.conjTranspose_apply]

theorem P_posSemidef : P.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg P_hermitian
  intro v
  simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 0 + v 1)]

theorem P_square : P ^ 2 = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_contraction : ((1 : Mat2) - P).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.sub P_hermitian)
  intro v
  simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 0 - v 1)]

theorem P_weighted_trace (rho : ℝ) : (W rho * P).trace = rho / 2 := by
  simp [W, P, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem P_objective : (E * P).trace = 1 / 2 := by
  norm_num [E, P, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem overlap_branch_SDP_attainment {rho r : ℝ} (hrho : 0 < rho)
    (hr0 : 0 ≤ r) (hr1 : r ≤ rho / 2) :
    ∃ A Q : Mat2, A.IsHermitian ∧ Q.PosSemidef ∧
      (Q - A ^ 2).PosSemidef ∧ ((1 : Mat2) - Q).PosSemidef ∧
      (W rho * A).trace = r ∧ (E * Q).trace = 1 / 2 := by
  let t := 2 * r / rho
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hrho.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hrho]
    linarith
  have hts : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hAP : (t • P) ^ 2 = t ^ 2 • P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨t • P, P, ?_, P_posSemidef, ?_, P_contraction, ?_, P_objective⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.conjTranspose_apply]
  · rw [hAP]
    have hid : P - t ^ 2 • P = (1 - t ^ 2) • P := by module
    rw [hid]
    exact P_posSemidef.smul hts
  · simp [W, P, t, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hrho.ne']
    ring

#print axioms overlap_branch_upper_bound
#print axioms overlap_branch_SDP_attainment
end OuterBound
end GeneralizedResearch
