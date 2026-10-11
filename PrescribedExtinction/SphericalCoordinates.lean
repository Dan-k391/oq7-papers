import PrescribedExtinction.Maxwell
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def sphericalPoint (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 0 * Real.sin (p 1) * Real.cos (p 2),
    p 0 * Real.sin (p 1) * Real.sin (p 2), p 0 * Real.cos (p 1)]

def sphericalJacobianMatrix (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sin (p 1) * Real.cos (p 2), p 0 * Real.cos (p 1) * Real.cos (p 2), -p 0 * Real.sin (p 1) * Real.sin (p 2);
     Real.sin (p 1) * Real.sin (p 2), p 0 * Real.cos (p 1) * Real.sin (p 2), p 0 * Real.sin (p 1) * Real.cos (p 2);
     Real.cos (p 1), -p 0 * Real.sin (p 1), 0]

def sphericalDerivative (p : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' (sphericalJacobianMatrix p)).toContinuousLinearMap

theorem sphericalPoint_hasFDerivAt (p : Fin 3 → ℝ) :
    HasFDerivAt sphericalPoint (sphericalDerivative p) p := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x := p)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt (x := p)
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt (x := p)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert (h0.mul h1.sin).mul h2.cos using 1
    · rfl
    · ext q
      simp [sphericalDerivative, sphericalJacobianMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]
      ring
  · convert (h0.mul h1.sin).mul h2.sin using 1
    · rfl
    · ext q
      simp [sphericalDerivative, sphericalJacobianMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]
      ring
  · convert h0.mul h1.cos using 1
    · rfl
    · ext q
      simp [sphericalDerivative, sphericalJacobianMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]
      ring

theorem sphericalDerivative_det (p : Fin 3 → ℝ) :
    (sphericalDerivative p).det = (p 0) ^ 2 * Real.sin (p 1) := by
  unfold sphericalDerivative
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
  simp [sphericalJacobianMatrix, Matrix.det_fin_three]
  have h1 := Real.sin_sq_add_cos_sq (p 1)
  have h2 := Real.sin_sq_add_cos_sq (p 2)
  calc
    _ = (p 0) ^ 2 * Real.sin (p 1) *
        ((Real.sin (p 1)) ^ 2 + (Real.cos (p 1)) ^ 2) *
        ((Real.sin (p 2)) ^ 2 + (Real.cos (p 2)) ^ 2) := by ring
    _ = _ := by rw [h1, h2]; ring

end OQ7Prescribed
