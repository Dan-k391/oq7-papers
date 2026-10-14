import OQ7.Target

noncomputable section
namespace OQ7
open scoped Matrix

theorem waveTransfer_smul (c : ℂ) (F : Mat2) :
    waveTransfer (c • F) = c • waveTransfer F := by
  simp [waveTransfer]

theorem transferReflectionLeft_smul {c : ℂ} (hc : c ≠ 0) (K : Mat2) :
    transferReflectionLeft (c • K) = transferReflectionLeft K := by
  simp only [transferReflectionLeft, Matrix.smul_apply, smul_eq_mul, ← mul_neg]
  exact mul_div_mul_left _ _ hc

theorem transferReflectionRight_smul {c : ℂ} (hc : c ≠ 0) (K : Mat2) :
    transferReflectionRight (c • K) = transferReflectionRight K := by
  simp only [transferReflectionRight, Matrix.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

theorem transferTransmissionRight_smul (c : ℂ) (K : Mat2) :
    transferTransmissionRight (c • K) = c⁻¹ * transferTransmissionRight K := by
  simp [transferTransmissionRight, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

theorem transferTransmissionLeft_smul {c : ℂ} (hc : c ≠ 0) (K : Mat2) :
    transferTransmissionLeft (c • K) = c * transferTransmissionLeft K := by
  simp only [transferTransmissionLeft, Matrix.det_smul, Fintype.card_fin,
    Matrix.smul_apply, smul_eq_mul]
  calc
    c ^ 2 * K.det / (c * K 1 1) = c * (c * K.det) / (c * K 1 1) := by ring
    _ = c * K.det / K 1 1 := mul_div_mul_left _ _ hc
    _ = _ := by ring

theorem normSq_inv_mul_unit {c : ℂ} (hc : Complex.normSq c = 1) (t : ℂ) :
    Complex.normSq (c⁻¹ * t) = Complex.normSq t := by
  rw [Complex.normSq_mul, Complex.normSq_inv, hc, inv_one, one_mul]

theorem unit_smul_reflectionLeft {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    transferReflectionLeft (waveTransfer (c • F)) = transferReflectionLeft (waveTransfer F) := by
  have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc
  rw [waveTransfer_smul, transferReflectionLeft_smul hc0]

theorem unit_smul_reflectionRight {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    transferReflectionRight (waveTransfer (c • F)) = transferReflectionRight (waveTransfer F) := by
  have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc
  rw [waveTransfer_smul, transferReflectionRight_smul hc0]

theorem unit_smul_transmissionPower {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    transmissionPower (transferTransmissionRight (waveTransfer (c • F))) =
      transmissionPower (transferTransmissionRight (waveTransfer F)) := by
  rw [waveTransfer_smul, transferTransmissionRight_smul]
  exact normSq_inv_mul_unit hc _

theorem unit_smul_meanAbsorptance {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    meanAbsorptance (transferReflectionLeft (waveTransfer (c • F)))
      (transferReflectionRight (waveTransfer (c • F)))
      (transferTransmissionRight (waveTransfer (c • F))) =
    meanAbsorptance (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F)) := by
  rw [unit_smul_reflectionLeft hc, unit_smul_reflectionRight hc]
  unfold meanAbsorptance absorptanceLeft absorptanceRight
  rw [show Complex.normSq (transferTransmissionRight (waveTransfer (c • F))) =
      Complex.normSq (transferTransmissionRight (waveTransfer F)) from
    unit_smul_transmissionPower hc F]

theorem signPow_normSq (j : ℕ) : Complex.normSq ((-1 : ℂ) ^ j) = 1 := by
  simp [map_pow]

theorem unit_smul_fluxDefect {c : ℂ} (hc : Complex.normSq c = 1) (F : Mat2) :
    fluxDefect (c • F) = fluxDefect F := by
  have hc' : c * star c = 1 := by
    have hcC := congrArg (fun r : ℝ => (r : ℂ)) hc
    rw [Complex.normSq_eq_conj_mul_self] at hcC
    simpa only [Complex.ofReal_one, Complex.star_def, mul_comm] using hcC
  simp only [fluxDefect, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hc', one_smul]

theorem signPow_fluxDefect (F : Mat2) (j : ℕ) :
    fluxDefect ((-1 : ℂ) ^ j • F) = fluxDefect F :=
  unit_smul_fluxDefect (signPow_normSq j) F

theorem signPow_scattering (F : Mat2) (j : ℕ) :
    transferReflectionLeft (waveTransfer ((-1 : ℂ) ^ j • F)) =
      transferReflectionLeft (waveTransfer F) ∧
    transferReflectionRight (waveTransfer ((-1 : ℂ) ^ j • F)) =
      transferReflectionRight (waveTransfer F) ∧
    transferTransmissionRight (waveTransfer ((-1 : ℂ) ^ j • F)) =
      (-1 : ℂ) ^ j * transferTransmissionRight (waveTransfer F) := by
  refine ⟨unit_smul_reflectionLeft (signPow_normSq j) F,
    unit_smul_reflectionRight (signPow_normSq j) F, ?_⟩
  rw [waveTransfer_smul, transferTransmissionRight_smul]
  congr 1
  rw [← inv_pow]
  norm_num

/-- The scalar signs of quarter-wave pairs preserve both exact target powers. -/
theorem signPow_targetPowers (F : Mat2) (j : ℕ) :
    transmissionPower (transferTransmissionRight (waveTransfer ((-1 : ℂ) ^ j • F))) =
      transmissionPower (transferTransmissionRight (waveTransfer F)) ∧
    meanAbsorptance (transferReflectionLeft (waveTransfer ((-1 : ℂ) ^ j • F)))
      (transferReflectionRight (waveTransfer ((-1 : ℂ) ^ j • F)))
      (transferTransmissionRight (waveTransfer ((-1 : ℂ) ^ j • F))) =
    meanAbsorptance (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F)) :=
  ⟨unit_smul_transmissionPower (signPow_normSq j) F,
    unit_smul_meanAbsorptance (signPow_normSq j) F⟩

#print axioms waveTransfer_smul
#print axioms transferReflectionLeft_smul
#print axioms transferReflectionRight_smul
#print axioms transferTransmissionRight_smul
#print axioms transferTransmissionLeft_smul
#print axioms normSq_inv_mul_unit
#print axioms unit_smul_reflectionLeft
#print axioms unit_smul_reflectionRight
#print axioms unit_smul_transmissionPower
#print axioms unit_smul_meanAbsorptance
#print axioms signPow_normSq
#print axioms unit_smul_fluxDefect
#print axioms signPow_fluxDefect
#print axioms signPow_scattering
#print axioms signPow_targetPowers
end OQ7
