import OQ7.Transfer

noncomputable section

namespace OQ7

open scoped ComplexOrder

/-- Directed-flux form in vacuum travelling-wave coordinates. -/
def waveFluxForm : Mat2 := !![1, 0; 0, -1]

def waveFluxDefect (K : Mat2) : Mat2 :=
  waveFluxForm - K.conjTranspose * waveFluxForm * K

theorem waveBasis_fluxForm :
    waveBasis.conjTranspose * fluxForm * waveBasis = (2 : ℂ) • waveFluxForm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [waveBasis, fluxForm, waveFluxForm, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem waveBasis_fluxDefect (F : Mat2) :
    waveBasis.conjTranspose * fluxDefect F * waveBasis =
      (2 : ℂ) • waveFluxDefect (waveTransfer F) := by
  have hcore : waveBasis.conjTranspose * (F.conjTranspose * fluxForm * F) * waveBasis =
      (waveTransfer F).conjTranspose *
        (waveBasis.conjTranspose * fluxForm * waveBasis) * waveTransfer F := by
    calc
      _ = (F * waveBasis).conjTranspose * fluxForm * (F * waveBasis) := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [fieldTransfer_waveBasis]
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold fluxDefect
  rw [Matrix.mul_sub, Matrix.sub_mul, hcore, waveBasis_fluxForm]
  simp [waveFluxDefect, smul_sub]

theorem waveFluxDefect_11 (K : Mat2) :
    waveFluxDefect K 1 1 =
      (Complex.normSq (K 1 1) : ℂ) - (Complex.normSq (K 0 1) : ℂ) - 1 := by
  simp [waveFluxDefect, waveFluxForm, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  ring

/-- Algebraic consequence of a nonnegative actual field-flux defect. -/
theorem passive_transfer_denominator_bound (F : Mat2) (hF : (fluxDefect F).PosSemidef) :
    1 + Complex.normSq (waveTransfer F 0 1) ≤ Complex.normSq (waveTransfer F 1 1) := by
  have hcong := hF.conjTranspose_mul_mul_same waveBasis
  rw [waveBasis_fluxDefect] at hcong
  have hdiag := hcong.diag_nonneg (i := (1 : Fin 2))
  rw [Matrix.smul_apply, smul_eq_mul, waveFluxDefect_11] at hdiag
  have hreal := (RCLike.nonneg_iff.mp hdiag).1
  change 0 ≤ (2 * ((Complex.normSq (waveTransfer F 1 1) : ℂ) -
    (Complex.normSq (waveTransfer F 0 1) : ℂ) - 1)).re at hreal
  simp at hreal
  linarith

theorem passive_transfer_denominator_ne_zero (F : Mat2)
    (hF : (fluxDefect F).PosSemidef) : waveTransfer F 1 1 ≠ 0 := by
  intro hz
  have hbound := passive_transfer_denominator_bound F hF
  rw [hz, Complex.normSq_zero] at hbound
  have hnonneg := Complex.normSq_nonneg (waveTransfer F 0 1)
  linarith

/-- Passivity of the actual reciprocal scattering response of a unimodular field transfer.
The field-flux positivity hypothesis still needs to be proved from Maxwell flux balance. -/
theorem passive_transfer_scattering (F : Mat2)
    (hF : (fluxDefect F).PosSemidef) (hdet : F.det = 1) :
    Passive (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F))
      (transferTransmissionRight (waveTransfer F)) := by
  have hd := passive_transfer_denominator_ne_zero F hF
  have hcong := hF.conjTranspose_mul_mul_same
    (inputFieldStates (transferReflectionLeft (waveTransfer F))
      (transferTransmissionRight (waveTransfer F)))
  rw [← transfer_absorption_fluxDefect F hd hdet] at hcong
  have hscaled := hcong.smul (show (0 : ℂ) ≤ 1 / 2 by rw [RCLike.nonneg_iff]; norm_num)
  simpa [Passive, smul_smul] using hscaled

theorem passive_transfer_transmission_ne_zero (F : Mat2)
    (hF : (fluxDefect F).PosSemidef) : transferTransmissionRight (waveTransfer F) ≠ 0 := by
  exact transfer_transmissionRight_ne_zero (waveTransfer F)
    (passive_transfer_denominator_ne_zero F hF)

/-- The actual response has the paper's normalized determinant invariant. -/
theorem passive_transfer_absorption_det_ratio (F : Mat2)
    (hF : (fluxDefect F).PosSemidef) (hdet : F.det = 1) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F))
        (transferTransmissionRight (waveTransfer F))).det /
      (Complex.normSq (transferTransmissionRight (waveTransfer F)) : ℂ) =
        (fluxDefect F).det := by
  exact transfer_absorption_fluxDefect_ratio F
    (passive_transfer_denominator_ne_zero F hF) hdet

#print axioms waveBasis_fluxForm
#print axioms waveBasis_fluxDefect
#print axioms waveFluxDefect_11
#print axioms passive_transfer_denominator_bound
#print axioms passive_transfer_denominator_ne_zero
#print axioms passive_transfer_scattering
#print axioms passive_transfer_transmission_ne_zero
#print axioms passive_transfer_absorption_det_ratio

end OQ7
