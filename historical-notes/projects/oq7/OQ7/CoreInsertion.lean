import OQ7.CoreAlgebra
import OQ7.ProductRemainder

noncomputable section
namespace OQ7.CoreConstruction
open scoped Matrix

/-- The finite single-insertion sum is an exact polynomial in the repetition count. -/
theorem linearizedCore_firstInsertion (g : ℝ) (t : ℂ) (w : Mat2) (n : ℕ) :
    firstInsertion (linearizedCore g t) w n =
      (n : ℂ) • w +
      (t * (n : ℂ) * ((n : ℂ) - 1) / 2) •
        (sheetGenerator g * w + w * sheetGenerator g) +
      (t ^ 2 * (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) / 6) •
        (sheetGenerator g * w * sheetGenerator g) := by
  induction n with
  | zero => simp [firstInsertion]
  | succ n ih =>
      rw [firstInsertion, ih, linearizedCore_pow]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [linearizedCore, sheetGenerator, matrixUnit21, Matrix.mul_apply,
          Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      all_goals ring

theorem sheetGenerator_coreK4_anticommutator (P Q g : ℝ) :
    sheetGenerator g * coreK4 P Q g + coreK4 P Q g * sheetGenerator g =
      sheetGenerator g * coreH P Q g * sheetGenerator g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetGenerator, matrixUnit21, coreK4, coreH, cubicCoefficient,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem sheetGenerator_coreK4_sandwich (P Q g : ℝ) :
    sheetGenerator g * coreK4 P Q g * sheetGenerator g = 0 := by
  rw [coreK4_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetGenerator, matrixUnit21, Matrix.mul_apply, Fin.sum_univ_two]

/-- This is the exact H/K4 insertion identity used in the checkpoint, before error estimates. -/
theorem core_firstInsertion_reciprocal {m : ℕ} (hm : m ≠ 0) (P Q g : ℝ) :
    firstInsertion (linearizedCore g (1 / (m : ℂ)))
      (((1 : ℂ) / (m : ℂ) ^ 3) • coreH P Q g +
        ((1 : ℂ) / (m : ℂ) ^ 4) • coreK4 P Q g) m =
      ((1 : ℂ) / (m : ℂ) ^ 2) • coreJ P Q g -
        ((1 : ℂ) / (6 * (m : ℂ) ^ 4)) •
          (sheetGenerator g * coreH P Q g * sheetGenerator g) := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [linearizedCore_firstInsertion]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetGenerator, matrixUnit21, coreH, coreK4, coreJ, cubicCoefficient]
  all_goals (field_simp <;> ring)

#print axioms linearizedCore_firstInsertion
#print axioms sheetGenerator_coreK4_anticommutator
#print axioms sheetGenerator_coreK4_sandwich
#print axioms core_firstInsertion_reciprocal
end OQ7.CoreConstruction
