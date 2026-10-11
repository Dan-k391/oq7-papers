import OQ7.MatchingResponse

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7

open scoped Matrix Topology ContDiff Matrix.Norms.Elementwise

/-- The coated triangular limiting sheet from equations (39) and (40). -/
def triangularMatchingTransfer (A h : ℝ) : Mat2 :=
  !![(A : ℂ), 0; -(h : ℂ), ((A⁻¹ : ℝ) : ℂ)]

theorem logCoatedTransfer_eq_physical_scale (F : Mat2) (ℓ : ℝ × ℝ) :
    logCoatedTransfer F ℓ = losslessDiagonalScale ℓ.2 * F * losslessDiagonalScale ℓ.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [logCoatedTransfer, losslessDiagonalScale, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, sub_eq_add_neg, Real.exp_add, Complex.ofReal_mul] <;> ring

theorem triangularMatchingTransfer_det {A : ℝ} (hA : A ≠ 0) (h : ℝ) :
    (triangularMatchingTransfer A h).det = 1 := by
  have hc : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  simp [triangularMatchingTransfer, Matrix.det_fin_two, hc]

theorem triangularMatchingTransfer_wave (A h : ℝ) :
    waveTransfer (triangularMatchingTransfer A h) =
      (!![((A - h + A⁻¹) / 2 : ℝ), ((A - h - A⁻¹) / 2 : ℝ);
          ((A + h - A⁻¹) / 2 : ℝ), ((A + h + A⁻¹) / 2 : ℝ)] : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularMatchingTransfer, waveTransfer, waveBasis, waveBasisInv,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem triangularMatchingTransfer_denominator_ne_zero {A h : ℝ}
    (hA : 0 < A) (hh : 0 < h) :
    waveTransfer (triangularMatchingTransfer A h) 1 1 ≠ 0 := by
  rw [triangularMatchingTransfer_wave]
  change (((A + h + A⁻¹) / 2 : ℝ) : ℂ) ≠ 0
  exact_mod_cast (show (A + h + A⁻¹) / 2 ≠ 0 by positivity)

theorem triangularMatchingTransfer_response {A h : ℝ} (hA : A ≠ 0)
    (hD : A + h + A⁻¹ ≠ 0) :
    matchingResponse (triangularMatchingTransfer A h) =
      (4 / (A + A⁻¹ + h) ^ 2, 2 * h * (A + A⁻¹) / (A + A⁻¹ + h) ^ 2) := by
  have hpoly : A * (A + h) + 1 ≠ 0 := by
    have heq : A * (A + h) + 1 = A * (A + h + A⁻¹) := by
      calc
        A * (A + h) + 1 = A * (A + h) + A * A⁻¹ := by rw [mul_inv_cancel₀ hA]
        _ = A * (A + h + A⁻¹) := by ring
    rw [heq]
    exact mul_ne_zero hA hD
  have hpoly₂ : A ^ 2 + 1 + A * h ≠ 0 := by
    convert hpoly using 1 <;> ring
  have hF := triangularMatchingTransfer_det hA h
  have hquad : (A + A⁻¹) ^ 2 - (A - A⁻¹) ^ 2 = 4 := by
    calc
      _ = 4 * (A * A⁻¹) := by ring
      _ = 4 := by rw [mul_inv_cancel₀ hA, mul_one]
  unfold matchingResponse
  rw [matchingTransmissionPower_physical hF, matchingMeanAbsorptance_physical hF,
    triangularMatchingTransfer_wave]
  simp only [transferReflectionLeft, transferReflectionRight, transferTransmissionRight,
    transmissionPower, meanAbsorptance, absorptanceLeft, absorptanceRight,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_one,
    Complex.normSq_ofReal]
  apply Prod.ext
  · dsimp
    field_simp [hD, hA, hpoly, hpoly₂]
    <;> ring
  · dsimp
    field_simp [hD, hA, hpoly, hpoly₂]
    <;> ring

#print axioms logCoatedTransfer_eq_physical_scale
#print axioms triangularMatchingTransfer_det
#print axioms triangularMatchingTransfer_wave
#print axioms triangularMatchingTransfer_denominator_ne_zero
#print axioms triangularMatchingTransfer_response

end OQ7


