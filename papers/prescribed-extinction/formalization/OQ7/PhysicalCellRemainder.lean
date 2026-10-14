import OQ7.CoreExponential
import OQ7.CoreTaylor
import OQ7.CellNormBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7.CoreConstruction
open Filter Asymptotics
open scoped Topology Matrix Matrix.Norms.Operator

def coreCellPerturbation (k P Q M : ℝ) (m : ℕ) : Mat2 :=
  strippedCellTransfer k P Q M m - linearizedCore (k * M) (1 / (m : ℂ))

theorem matrix_reciprocalPower_smul_eq_real (X : Mat2) (m n : ℕ) :
    (1 / (m : ℂ) ^ n) • X = (1 / (m : ℝ) ^ n) • X := by
  ext i j
  simp [Complex.real_smul]

theorem coreSliceParameter_linearizedCore {Q : ℝ} (hQ : Q ≠ 0)
    (k M : ℝ) (m : ℕ) :
    (1 : Mat2) + coreSliceParameter k Q M m • lossGenerator Q =
      linearizedCore (k * M) (1 / (m : ℂ)) := by
  by_cases hm : m = 0
  · simp [hm, coreSliceParameter_eq, linearizedCore]
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [coreSliceParameter_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linearizedCore, lossGenerator, sheetGenerator, matrixUnit21, Complex.real_smul]
  field_simp

theorem linearizedCore_reciprocal_eq_real (g : ℝ) (m : ℕ) :
    linearizedCore g (1 / (m : ℂ)) = (1 : Mat2) + (1 / (m : ℝ)) • sheetGenerator g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linearizedCore, sheetGenerator, matrixUnit21, Complex.real_smul]

theorem strippedCellTransfer_eq_linearized_add (k P Q M : ℝ) (m : ℕ) :
    strippedCellTransfer k P Q M m =
      linearizedCore (k * M) (1 / (m : ℂ)) + coreCellPerturbation k P Q M m := by
  simp only [coreCellPerturbation]
  abel

theorem tripleTaylorTail_continuous {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X Y Z : A) : Continuous (tripleTaylorTail X Y Z) := by
  unfold tripleTaylorTail
  apply continuous_finsetSum
  intro c hc
  apply continuous_finsetSum
  intro b hb
  apply continuous_finsetSum
  intro a ha
  by_cases h : 5 ≤ a + b + c
  · simp only [ite_eq_left h]
    fun_prop
  · simp only [ite_eq_right h]
    exact continuous_const

theorem cellTaylorTail_continuous (P Q : ℝ) : Continuous (cellTaylorTail P Q) :=
  tripleTaylorTail_continuous _ _ _

theorem dimensionlessCell_quintic_remainder_isBigO (P Q : ℝ) :
    (fun t : ℝ => dimensionlessCell P Q t - cellTaylorPolynomial P Q t)
      =O[𝓝 0] (fun t : ℝ => t ^ 5) := by
  have hb := triple_exp_remainder_of_tail_identity
    ((-1 / 2 : ℝ) • realGenerator P) (realGenerator P + lossGenerator Q)
    ((-1 / 2 : ℝ) • realGenerator P) 5 (cellTaylorPolynomial P Q)
    (cellTaylorTail P Q) (cellTaylorTail_continuous P Q).continuousAt
    (concrete_cellTaylor_product P Q)
  have heq : ∀ t : ℝ, dimensionlessCell P Q t =
      NormedSpace.exp (t • ((-1 / 2 : ℝ) • realGenerator P)) *
        NormedSpace.exp (t • (realGenerator P + lossGenerator Q)) *
          NormedSpace.exp (t • ((-1 / 2 : ℝ) • realGenerator P)) := by
    intro t
    simp only [dimensionlessCell, smul_smul]
    have h : t * (-1 / 2 : ℝ) = -t / 2 := by ring
    rw [h]
  exact hb.congr_left (fun t => by rw [heq])

theorem dimensionlessCell_cubic_perturbation_isBigO (P Q : ℝ) :
    (fun t : ℝ => dimensionlessCell P Q t - ((1 : Mat2) + t • lossGenerator Q))
      =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  apply linear_remainder_isBigO_cubic_of_quartic
    (dimensionlessCell P Q) (lossGenerator Q) (cubicCoefficient P Q) (cellFourthCoefficient P Q)
  simpa only [cellTaylorPolynomial] using dimensionlessCell_quintic_remainder_isBigO P Q

theorem strippedCellTransfer_quintic_norm_bound {P : ℝ} (hP : 1 ≤ P)
    (k Q M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖strippedCellTransfer k P Q M m -
        cellTaylorPolynomial P Q (coreSliceParameter k Q M m)‖ ≤ C / (m : ℝ) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := isBigO_reciprocal_scale_norm_bound
    (dimensionlessCell_quintic_remainder_isBigO P Q) ((k * M) / Q)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with m hm
  simpa only [strippedCellTransfer_eq_dimensionless hP, coreSliceParameter_eq] using hm

theorem cellTaylorPolynomial_coreScale_eq {Q : ℝ} (hQ : Q ≠ 0)
    (k P M : ℝ) (m : ℕ) :
    cellTaylorPolynomial P Q (coreSliceParameter k Q M m) =
      linearizedCore (k * M) (1 / (m : ℂ)) +
        (1 / (m : ℂ) ^ 3) • coreH P Q (k * M) +
          (1 / (m : ℂ) ^ 4) • coreK4 P Q (k * M) := by
  by_cases hm : m = 0
  · simp [hm, coreSliceParameter_eq, cellTaylorPolynomial, linearizedCore]
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [coreSliceParameter_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cellTaylorPolynomial, cellFourthCoefficient, coreH, coreK4, cubicCoefficient,
      linearizedCore, lossGenerator, sheetGenerator, matrixUnit21, Complex.real_smul]
  all_goals field_simp

/-- The perturbation is the actual stripped finite-layer cell minus its nilpotent sheet part. -/
theorem coreCellPerturbation_cubic_norm_bound {P Q : ℝ} (hP : 1 ≤ P) (hQ : Q ≠ 0)
    (k M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖coreCellPerturbation k P Q M m‖ ≤ C / (m : ℝ) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := isBigO_reciprocal_scale_norm_bound
    (dimensionlessCell_cubic_perturbation_isBigO P Q) ((k * M) / Q)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with m hm
  simpa only [coreCellPerturbation, strippedCellTransfer_eq_dimensionless hP,
    ← coreSliceParameter_linearizedCore hQ k M m, coreSliceParameter_eq] using hm

theorem coreCellPerturbation_coefficientRemainder_norm_bound {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖coreCellPerturbation k P Q M m - (1 / (m : ℂ) ^ 3) • coreH P Q (k * M) -
        (1 / (m : ℂ) ^ 4) • coreK4 P Q (k * M)‖ ≤ C / (m : ℝ) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := strippedCellTransfer_quintic_norm_bound hP k Q M
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with m hm
  rw [cellTaylorPolynomial_coreScale_eq hQ] at hm
  convert hm using 1
  congr 1
  simp only [coreCellPerturbation]
  abel

theorem actual_core_doubleInsertion_quartic_norm_bound {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖insertionError (linearizedCore (k * M) (1 / (m : ℂ)))
        (coreCellPerturbation k P Q M m) m‖ ≤ C / (m : ℝ) ^ 4 := by
  obtain ⟨Cw, hCw, hw⟩ := coreCellPerturbation_cubic_norm_bound hP hQ k M
  simpa only [linearizedCore_reciprocal_eq_real] using
    reciprocalCell_insertionError_quartic_bound (sheetGenerator (k * M))
      (coreCellPerturbation k P Q M) hCw hw

#print axioms matrix_reciprocalPower_smul_eq_real
#print axioms coreSliceParameter_linearizedCore
#print axioms linearizedCore_reciprocal_eq_real
#print axioms strippedCellTransfer_eq_linearized_add
#print axioms tripleTaylorTail_continuous
#print axioms cellTaylorTail_continuous
#print axioms dimensionlessCell_quintic_remainder_isBigO
#print axioms dimensionlessCell_cubic_perturbation_isBigO
#print axioms strippedCellTransfer_quintic_norm_bound
#print axioms cellTaylorPolynomial_coreScale_eq
#print axioms coreCellPerturbation_cubic_norm_bound
#print axioms coreCellPerturbation_coefficientRemainder_norm_bound
#print axioms actual_core_doubleInsertion_quartic_norm_bound
end OQ7.CoreConstruction
