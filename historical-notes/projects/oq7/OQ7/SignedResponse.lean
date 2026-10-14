import OQ7.PhaseSmooth
import OQ7.ScalarSign

noncomputable section
namespace OQ7
open scoped Matrix

theorem halfAsymmetry_reflection_formula (rL rR t : ℂ) :
    halfAsymmetry rL rR t = (Complex.normSq rR - Complex.normSq rL) / 2 := by
  unfold halfAsymmetry absorptanceLeft absorptanceRight
  ring

theorem unit_smul_transferHalfAsymmetry {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    transferHalfAsymmetry (c • F) = transferHalfAsymmetry F := by
  unfold transferHalfAsymmetry
  rw [halfAsymmetry_reflection_formula, halfAsymmetry_reflection_formula,
    unit_smul_reflectionLeft hc, unit_smul_reflectionRight hc]

theorem signPow_sq (j : ℕ) : (((-1 : ℂ) ^ j) ^ 2) = 1 := by
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num

theorem signPow_unitPhase (rL rR t : ℂ) (j : ℕ) :
    unitPhase rL rR (((-1 : ℂ) ^ j) * t) = unitPhase rL rR t := by
  have ht : transmissionPower (((-1 : ℂ) ^ j) * t) = transmissionPower t := by
    unfold transmissionPower
    rw [Complex.normSq_mul, signPow_normSq, one_mul]
  unfold unitPhase phaseProduct
  rw [ht, star_mul, mul_pow]
  simp only [star_pow, star_neg, star_one, signPow_sq, mul_one]

theorem signPow_transferUnitPhase (F : Mat2) (j : ℕ) :
    transferUnitPhase (((-1 : ℂ) ^ j) • F) = transferUnitPhase F := by
  have hs := signPow_scattering F j
  unfold transferUnitPhase
  rw [hs.1, hs.2.1, hs.2.2, signPow_unitPhase]

theorem unit_smul_responseAsymmetry {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    responseAsymmetry (transferReflectionLeft (waveTransfer (c • F)))
      (transferReflectionRight (waveTransfer (c • F)))
      (transferTransmissionRight (waveTransfer (c • F))) =
    responseAsymmetry (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F))
      (transferTransmissionRight (waveTransfer F)) := by
  rw [responseAsymmetry_eq, responseAsymmetry_eq]
  exact congrArg (fun x : ℝ => 2 * |x|) (unit_smul_transferHalfAsymmetry hc F)

theorem signPow_transfer_det (F : Mat2) (j : ℕ) :
    (((-1 : ℂ) ^ j) • F).det = F.det := by
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin, signPow_sq, one_mul]

#print axioms halfAsymmetry_reflection_formula
#print axioms unit_smul_transferHalfAsymmetry
#print axioms signPow_sq
#print axioms signPow_unitPhase
#print axioms signPow_transferUnitPhase
#print axioms unit_smul_responseAsymmetry
#print axioms signPow_transfer_det
end OQ7
