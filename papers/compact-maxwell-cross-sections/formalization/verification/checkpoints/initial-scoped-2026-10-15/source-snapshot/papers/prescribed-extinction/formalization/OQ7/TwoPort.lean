import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

namespace OQ7

open scoped ComplexOrder

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The reciprocal two-port matrix, in the paper's port order. -/
def scatteringMatrix (rL rR t : ℂ) : Mat2 := !![rL, t; t, rR]

/-- The actual absorption matrix I - S† S. -/
def absorptionMatrix (rL rR t : ℂ) : Mat2 :=
  1 - (scatteringMatrix rL rR t).conjTranspose * scatteringMatrix rL rR t

def absorptanceLeft (rL t : ℂ) : ℝ := 1 - Complex.normSq rL - Complex.normSq t

def absorptanceRight (rR t : ℂ) : ℝ := 1 - Complex.normSq rR - Complex.normSq t

def transmissionPower (t : ℂ) : ℝ := Complex.normSq t

def meanAbsorptance (rL rR t : ℂ) : ℝ :=
  (absorptanceLeft rL t + absorptanceRight rR t) / 2

def halfAsymmetry (rL rR t : ℂ) : ℝ :=
  (absorptanceLeft rL t - absorptanceRight rR t) / 2

def interference (rL rR t : ℂ) : ℂ := star rL * t + star t * rR

/-- Passivity is the positive semidefiniteness of the actual absorption matrix. -/
def Passive (rL rR t : ℂ) : Prop := (absorptionMatrix rL rR t).PosSemidef

theorem absorptionMatrix_eq (rL rR t : ℂ) :
    absorptionMatrix rL rR t =
      !![(absorptanceLeft rL t : ℂ), -interference rL rR t;
         -star (interference rL rR t), (absorptanceRight rR t : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [absorptionMatrix, scatteringMatrix, absorptanceLeft, absorptanceRight,
      interference, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.normSq_eq_conj_mul_self] <;> ring

theorem absorptance_difference (rL rR t : ℂ) :
    absorptanceLeft rL t - absorptanceRight rR t =
      Complex.normSq rR - Complex.normSq rL := by
  unfold absorptanceLeft absorptanceRight
  ring

theorem absorptance_coordinates (rL rR t : ℂ) :
    absorptanceLeft rL t = meanAbsorptance rL rR t + halfAsymmetry rL rR t ∧
    absorptanceRight rR t = meanAbsorptance rL rR t - halfAsymmetry rL rR t := by
  unfold meanAbsorptance halfAsymmetry
  constructor <;> ring

theorem absorption_det (rL rR t : ℂ) :
    (absorptionMatrix rL rR t).det =
      ((absorptanceLeft rL t * absorptanceRight rR t -
        Complex.normSq (interference rL rR t) : ℝ) : ℂ) := by
  rw [absorptionMatrix_eq, Matrix.det_fin_two]
  simp [Complex.normSq_eq_conj_mul_self]
  ring

theorem absorption_det_coordinates (rL rR t : ℂ) :
    (absorptionMatrix rL rR t).det =
      ((meanAbsorptance rL rR t ^ 2 - halfAsymmetry rL rR t ^ 2 -
        Complex.normSq (interference rL rR t) : ℝ) : ℂ) := by
  rw [absorption_det]
  congr 1
  unfold meanAbsorptance halfAsymmetry
  ring

theorem transmission_positive {t : ℂ} (ht : t ≠ 0) : 0 < transmissionPower t := by
  exact Complex.normSq_pos.mpr ht

#print axioms absorptionMatrix_eq
#print axioms absorptance_difference
#print axioms absorptance_coordinates
#print axioms absorption_det
#print axioms absorption_det_coordinates
#print axioms transmission_positive

end

end OQ7
