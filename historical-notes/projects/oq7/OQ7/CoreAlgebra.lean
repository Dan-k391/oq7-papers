import OQ7.Layers
import OQ7.Transfer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

noncomputable section
namespace OQ7.CoreConstruction
open scoped Matrix

def matrixUnit21 : Mat2 := !![0, 0; 1, 0]

/-- The exact dimensionless Maxwell generator in a real-P homogeneous spacer. -/
def realGenerator (P : ℝ) : Mat2 := !![0, Complex.I; Complex.I * (P : ℂ), 0]

/-- The difference between the lossy P+iQ and lossless P Maxwell generators. -/
def lossGenerator (Q : ℝ) : Mat2 := -(Q : ℂ) • matrixUnit21

def cubicCoefficient (P Q : ℝ) : Mat2 :=
  (1 / 12 : ℂ) • !![0, -(Q : ℂ); (Q : ℂ) * ((P : ℂ) + 2 * Complex.I * (Q : ℂ)), 0]

def matrixCommutator (X Y : Mat2) : Mat2 := X * Y - Y * X

def sheetGenerator (g : ℝ) : Mat2 := -(g : ℂ) • matrixUnit21

def coreH (P Q g : ℝ) : Mat2 :=
  ((g : ℂ) ^ 3 / (Q : ℂ) ^ 3) • cubicCoefficient P Q

def coreK4 (P Q g : ℝ) : Mat2 :=
  (1 / 2 : ℂ) • (sheetGenerator g * coreH P Q g + coreH P Q g * sheetGenerator g)

def coreJ (P Q g : ℝ) : Mat2 :=
  coreH P Q g + coreK4 P Q g +
    (1 / 6 : ℂ) • (sheetGenerator g * coreH P Q g * sheetGenerator g)

def limitingSheet (g : ℝ) : Mat2 := 1 + sheetGenerator g

def linearizedCore (g : ℝ) (t : ℂ) : Mat2 := 1 + t • sheetGenerator g

def linearFluxVariation (g : ℝ) (J : Mat2) : Mat2 :=
  -(J.conjTranspose * fluxForm * limitingSheet g +
    (limitingSheet g).conjTranspose * fluxForm * J)

theorem matrixUnit21_sq : matrixUnit21 ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixUnit21, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem realGenerator_sq (P : ℝ) : realGenerator P ^ 2 = -(P : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realGenerator, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf; simp [Complex.I_sq]

theorem lossGenerator_sq (Q : ℝ) : lossGenerator Q ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lossGenerator, matrixUnit21, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetGenerator_sq (g : ℝ) : sheetGenerator g ^ 2 = 0 := by
  exact lossGenerator_sq g

/-- The cubic coefficient is the concrete commutator expression in equation (36). -/
theorem cubicCoefficient_eq_commutators (P Q : ℝ) :
    cubicCoefficient P Q =
      (1 / 24 : ℂ) • matrixCommutator (realGenerator P)
        (matrixCommutator (realGenerator P) (lossGenerator Q)) +
      (1 / 12 : ℂ) • matrixCommutator (lossGenerator Q)
        (matrixCommutator (realGenerator P) (lossGenerator Q)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCoefficient, matrixCommutator, realGenerator, lossGenerator,
      matrixUnit21]
  all_goals ring_nf; simp [Complex.I_sq]; ring

theorem coreH_upperRight {P Q g : ℝ} (hQ : Q ≠ 0) :
    coreH P Q g 0 1 = -(g : ℂ) ^ 3 / (12 * (Q : ℂ) ^ 2) := by
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  simp [coreH, cubicCoefficient]
  field_simp

theorem coreK4_diagonal (P Q g : ℝ) :
    coreK4 P Q g =
      ((-(g : ℂ) * coreH P Q g 0 1) / 2) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreK4, coreH, cubicCoefficient, sheetGenerator, matrixUnit21,
      ]
  all_goals ring

theorem coreJ_upperRight {P Q g : ℝ} (hQ : Q ≠ 0) :
    coreJ P Q g 0 1 = -(g : ℂ) ^ 3 / (12 * (Q : ℂ) ^ 2) := by
  rw [coreJ, coreK4_diagonal]
  simp [sheetGenerator, matrixUnit21, Matrix.mul_apply, Fin.sum_univ_two,
    coreH_upperRight hQ, Matrix.vecMul, dotProduct]

theorem limitingSheet_explicit (g : ℝ) :
    limitingSheet g = !![1, 0; -(g : ℂ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [limitingSheet, sheetGenerator, matrixUnit21]

theorem limitingSheet_det (g : ℝ) : (limitingSheet g).det = 1 := by
  rw [limitingSheet_explicit, Matrix.det_fin_two]
  simp

theorem limitingSheet_fluxDefect (g : ℝ) :
    fluxDefect (limitingSheet g) = !![2 * (g : ℂ), 0; 0, 0] := by
  rw [limitingSheet_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fluxDefect, fluxForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

theorem linearFluxVariation_lowerRight (g : ℝ) (J : Mat2) :
    linearFluxVariation g J 1 1 = -(star (J 0 1) + J 0 1) := by
  rw [linearFluxVariation, limitingSheet_explicit]
  simp [fluxForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- The lower-right first variation gives the exact coefficient in equation (38). -/
theorem core_linearFluxVariation_lowerRight {P Q g : ℝ} (hQ : Q ≠ 0) :
    linearFluxVariation g (coreJ P Q g) 1 1 = (g : ℂ) ^ 3 / (6 * (Q : ℂ) ^ 2) := by
  rw [linearFluxVariation_lowerRight, coreJ_upperRight hQ]
  simp
  field_simp
  ring

theorem core_linear_determinant_coefficient {P Q g : ℝ} (hQ : Q ≠ 0) :
    (2 * (g : ℂ)) * linearFluxVariation g (coreJ P Q g) 1 1 =
      (g : ℂ) ^ 4 / (3 * (Q : ℂ) ^ 2) := by
  rw [core_linearFluxVariation_lowerRight hQ]
  field_simp
  ring

/-- The exact powers used in the checkpoint's single-insertion expansion. -/
theorem linearizedCore_pow (g : ℝ) (t : ℂ) (n : ℕ) :
    linearizedCore g t ^ n = 1 + ((n : ℂ) * t) • sheetGenerator g := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [linearizedCore, sheetGenerator, matrixUnit21, Matrix.mul_apply, Fin.sum_univ_two]
      ring

theorem linearizedCore_reciprocal_pow (g : ℝ) (m j : ℕ) :
    linearizedCore g (1 / (m : ℂ)) ^ j =
      1 + ((j : ℂ) / (m : ℂ)) • sheetGenerator g := by
  rw [linearizedCore_pow]
  congr 2
  ring

theorem linearizedCore_reciprocal_fullPower {g : ℝ} {m : ℕ} (hm : m ≠ 0) :
    linearizedCore g (1 / (m : ℂ)) ^ m = limitingSheet g := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [linearizedCore_reciprocal_pow, div_self hmc, one_smul]
  rfl

#print axioms matrixUnit21_sq
#print axioms realGenerator_sq
#print axioms lossGenerator_sq
#print axioms sheetGenerator_sq
#print axioms cubicCoefficient_eq_commutators
#print axioms coreH_upperRight
#print axioms coreK4_diagonal
#print axioms coreJ_upperRight
#print axioms limitingSheet_explicit
#print axioms limitingSheet_det
#print axioms limitingSheet_fluxDefect
#print axioms linearFluxVariation_lowerRight
#print axioms core_linearFluxVariation_lowerRight
#print axioms core_linear_determinant_coefficient
#print axioms linearizedCore_pow
#print axioms linearizedCore_reciprocal_pow
#print axioms linearizedCore_reciprocal_fullPower
end OQ7.CoreConstruction
