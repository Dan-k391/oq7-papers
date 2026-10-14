import OQ7.TwoPort

noncomputable section

namespace OQ7

/-- Conversion from right/left travelling wave amplitudes to the field state. -/
def waveBasis : Mat2 := !![1, 1; 1, -1]

/-- Explicit inverse of the wave-to-field basis. -/
def waveBasisInv : Mat2 := !![1 / 2, 1 / 2; 1 / 2, -1 / 2]

theorem waveBasisInv_mul_waveBasis : waveBasisInv * waveBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [waveBasisInv, waveBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem waveBasis_mul_waveBasisInv : waveBasis * waveBasisInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [waveBasisInv, waveBasis, Matrix.mul_apply, Fin.sum_univ_two]

/-- Transfer matrix in travelling-wave coordinates, with the paper's port order. -/
def waveTransfer (F : Mat2) : Mat2 := waveBasisInv * F * waveBasis

theorem waveTransfer_det (F : Mat2) : (waveTransfer F).det = F.det := by
  unfold waveTransfer
  rw [Matrix.det_mul, Matrix.det_mul]
  have hi : waveBasisInv.det = -(1 / 2 : ℂ) := by
    norm_num [waveBasisInv, Matrix.det_fin_two]
  have hb : waveBasis.det = -(2 : ℂ) := by
    norm_num [waveBasis, Matrix.det_fin_two]
  rw [hi, hb]
  ring

def transferReflectionLeft (K : Mat2) : ℂ := -K 1 0 / K 1 1
def transferReflectionRight (K : Mat2) : ℂ := K 0 1 / K 1 1
def transferTransmissionLeft (K : Mat2) : ℂ := K.det / K 1 1
def transferTransmissionRight (K : Mat2) : ℂ := 1 / K 1 1

/-- The two boundary equations for unit incidence from the left. -/
theorem transfer_left_boundary (K : Mat2) (hd : K 1 1 ≠ 0) :
    K.mulVec ![1, transferReflectionLeft K] =
      ![transferTransmissionLeft K, 0] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      transferReflectionLeft, transferTransmissionLeft, Matrix.det_fin_two] <;>
    field_simp [hd] <;> ring

/-- The two boundary equations for unit incidence from the right. -/
theorem transfer_right_boundary (K : Mat2) (hd : K 1 1 ≠ 0) :
    K.mulVec ![0, transferTransmissionRight K] =
      ![transferReflectionRight K, 1] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      transferReflectionRight, transferTransmissionRight] <;>
    field_simp [hd]

/-- Unimodular transfers have identical left and right transmission amplitudes. -/
theorem transfer_transmission_reciprocity (K : Mat2) (hdet : K.det = 1) :
    transferTransmissionLeft K = transferTransmissionRight K := by
  simp [transferTransmissionLeft, transferTransmissionRight, hdet]

theorem transfer_transmissionRight_ne_zero (K : Mat2) (hd : K 1 1 ≠ 0) :
    transferTransmissionRight K ≠ 0 := by
  exact one_div_ne_zero hd

/-- The left-boundary travelling-wave states for the two incident ports. -/
def incomingWaveStates (K : Mat2) : Mat2 :=
  !![1, 0; transferReflectionLeft K, transferTransmissionRight K]

/-- The right-boundary travelling-wave states for the two incident ports. -/
def outgoingWaveStates (K : Mat2) : Mat2 :=
  !![transferTransmissionLeft K, transferReflectionRight K; 0, 1]

theorem transfer_boundary_states (K : Mat2) (hd : K 1 1 ≠ 0) :
    K * incomingWaveStates K = outgoingWaveStates K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [incomingWaveStates, outgoingWaveStates, Matrix.mul_apply, Fin.sum_univ_two,
      transferReflectionLeft, transferReflectionRight,
      transferTransmissionLeft, transferTransmissionRight, Matrix.det_fin_two] <;>
    field_simp [hd] <;> ring

theorem fieldTransfer_waveBasis (F : Mat2) :
    F * waveBasis = waveBasis * waveTransfer F := by
  simp [waveTransfer, ← Matrix.mul_assoc, waveBasis_mul_waveBasisInv]

/-- Incoming amplitudes mapped to the actual field state at the left boundary. -/
def inputFieldStates (rL t : ℂ) : Mat2 := !![1 + rL, t; 1 - rL, -t]

/-- Incoming amplitudes mapped to the actual field state at the right boundary. -/
def outputFieldStates (rR t : ℂ) : Mat2 := !![t, 1 + rR; t, rR - 1]

theorem inputFieldStates_det (rL t : ℂ) :
    (inputFieldStates rL t).det = -2 * t := by
  simp [inputFieldStates, Matrix.det_fin_two]
  ring

theorem waveBasis_incoming_states (K : Mat2) :
    waveBasis * incomingWaveStates K =
      inputFieldStates (transferReflectionLeft K) (transferTransmissionRight K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [waveBasis, incomingWaveStates, inputFieldStates,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem waveBasis_outgoing_states (K : Mat2) (hdet : K.det = 1) :
    waveBasis * outgoingWaveStates K =
      outputFieldStates (transferReflectionRight K) (transferTransmissionRight K) := by
  rw [← transfer_transmission_reciprocity K hdet]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [waveBasis, outgoingWaveStates, outputFieldStates,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- The scattering states obtained from a unimodular field transfer satisfy both boundaries. -/
theorem field_transfer_boundary_states (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0) (hdet : F.det = 1) :
    F * inputFieldStates (transferReflectionLeft (waveTransfer F))
        (transferTransmissionRight (waveTransfer F)) =
      outputFieldStates (transferReflectionRight (waveTransfer F))
        (transferTransmissionRight (waveTransfer F)) := by
  rw [← waveBasis_incoming_states, ← Matrix.mul_assoc, fieldTransfer_waveBasis,
    Matrix.mul_assoc, transfer_boundary_states (waveTransfer F) hd]
  exact waveBasis_outgoing_states (waveTransfer F) (by rw [waveTransfer_det, hdet])

/-- Field-state flux form, twice the normalized directed flux. -/
def fluxForm : Mat2 := !![0, 1; 1, 0]

/-- Actual flux defect of a field transfer. -/
def fluxDefect (F : Mat2) : Mat2 := fluxForm - F.conjTranspose * fluxForm * F

theorem fluxForm_conjTranspose : fluxForm.conjTranspose = fluxForm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fluxForm, Matrix.conjTranspose_apply]

theorem fluxDefect_conjTranspose (F : Mat2) :
    (fluxDefect F).conjTranspose = fluxDefect F := by
  simp [fluxDefect, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    fluxForm_conjTranspose, Matrix.mul_assoc]

/-- Flux balance in the two exterior vacuum regions gives the actual absorption matrix. -/
theorem absorption_boundary_flux (rL rR t : ℂ) :
    (2 : ℂ) • absorptionMatrix rL rR t =
      (inputFieldStates rL t).conjTranspose * fluxForm * inputFieldStates rL t -
      (outputFieldStates rR t).conjTranspose * fluxForm * outputFieldStates rR t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [absorptionMatrix, scatteringMatrix, inputFieldStates, outputFieldStates,
      fluxForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- Exact absorption/field-defect congruence for any boundary-consistent reciprocal state. -/
theorem absorption_fluxDefect_congruence (F : Mat2) (rL rR t : ℂ)
    (hboundary : F * inputFieldStates rL t = outputFieldStates rR t) :
    (2 : ℂ) • absorptionMatrix rL rR t =
      (inputFieldStates rL t).conjTranspose * fluxDefect F * inputFieldStates rL t := by
  rw [absorption_boundary_flux, ← hboundary]
  simp only [fluxDefect, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem transfer_absorption_fluxDefect (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0) (hdet : F.det = 1) :
    (2 : ℂ) • absorptionMatrix
        (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F))
        (transferTransmissionRight (waveTransfer F)) =
      (inputFieldStates (transferReflectionLeft (waveTransfer F))
          (transferTransmissionRight (waveTransfer F))).conjTranspose *
        fluxDefect F *
        inputFieldStates (transferReflectionLeft (waveTransfer F))
          (transferTransmissionRight (waveTransfer F)) := by
  exact absorption_fluxDefect_congruence F _ _ _
    (field_transfer_boundary_states F hd hdet)

/-- The determinant relation (21), with transmitted power represented by normSq. -/
theorem absorption_fluxDefect_det (F : Mat2) (rL rR t : ℂ)
    (hboundary : F * inputFieldStates rL t = outputFieldStates rR t) :
    (absorptionMatrix rL rR t).det = (Complex.normSq t : ℂ) * (fluxDefect F).det := by
  have h := congrArg Matrix.det (absorption_fluxDefect_congruence F rL rR t hboundary)
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul,
    Matrix.det_conjTranspose, inputFieldStates_det] at h
  apply mul_left_cancel₀ (show (4 : ℂ) ≠ 0 by norm_num)
  calc
    4 * (absorptionMatrix rL rR t).det =
        2 ^ 2 * (absorptionMatrix rL rR t).det := by norm_num
    _ = star (-2 * t) * (fluxDefect F).det * (-2 * t) := h
    _ = 4 * ((Complex.normSq t : ℂ) * (fluxDefect F).det) := by
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [star_mul, star_neg, star_ofNat, Complex.star_def]
      ring

theorem transfer_absorption_fluxDefect_det (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0) (hdet : F.det = 1) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F))
        (transferTransmissionRight (waveTransfer F))).det =
      (Complex.normSq (transferTransmissionRight (waveTransfer F)) : ℂ) *
        (fluxDefect F).det := by
  exact absorption_fluxDefect_det F _ _ _ (field_transfer_boundary_states F hd hdet)

/-- Division by the nonzero transmitted power gives exactly the defect determinant. -/
theorem absorption_fluxDefect_ratio (F : Mat2) (rL rR t : ℂ)
    (hboundary : F * inputFieldStates rL t = outputFieldStates rR t) (ht : t ≠ 0) :
    (absorptionMatrix rL rR t).det / (Complex.normSq t : ℂ) = (fluxDefect F).det := by
  have htR : Complex.normSq t ≠ 0 := by
    exact fun h => ht (Complex.normSq_eq_zero.mp h)
  have htC : (Complex.normSq t : ℂ) ≠ 0 := by exact_mod_cast htR
  rw [absorption_fluxDefect_det F rL rR t hboundary]
  field_simp

theorem transfer_absorption_fluxDefect_ratio (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0) (hdet : F.det = 1) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F))
        (transferTransmissionRight (waveTransfer F))).det /
      (Complex.normSq (transferTransmissionRight (waveTransfer F)) : ℂ) =
        (fluxDefect F).det := by
  exact absorption_fluxDefect_ratio F _ _ _
    (field_transfer_boundary_states F hd hdet)
    (transfer_transmissionRight_ne_zero (waveTransfer F) hd)

/-- Surrounding a core by flux-preserving coatings transforms its defect by congruence. -/
theorem coated_fluxDefect (F CL CR : Mat2)
    (hL : CL.conjTranspose * fluxForm * CL = fluxForm)
    (hR : CR.conjTranspose * fluxForm * CR = fluxForm) :
    fluxDefect (CR * F * CL) = CL.conjTranspose * fluxDefect F * CL := by
  have htrans : (CR * F * CL).conjTranspose * fluxForm * (CR * F * CL) =
      CL.conjTranspose * (F.conjTranspose * fluxForm * F) * CL := by
    calc
      _ = CL.conjTranspose * F.conjTranspose *
          (CR.conjTranspose * fluxForm * CR) * F * CL := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hR]; simp [Matrix.mul_assoc]
  unfold fluxDefect
  rw [htrans]
  calc
    _ = CL.conjTranspose * fluxForm * CL -
        CL.conjTranspose * (F.conjTranspose * fluxForm * F) * CL := by rw [hL]
    _ = _ := by rw [Matrix.mul_sub, Matrix.sub_mul]

/-- The defect determinant is unchanged by unimodular lossless coatings. -/
theorem coated_fluxDefect_det (F CL CR : Mat2)
    (hL : CL.conjTranspose * fluxForm * CL = fluxForm)
    (hR : CR.conjTranspose * fluxForm * CR = fluxForm)
    (hdetL : CL.det = 1) :
    (fluxDefect (CR * F * CL)).det = (fluxDefect F).det := by
  rw [coated_fluxDefect F CL CR hL hR]
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hdetL]

#print axioms waveBasisInv_mul_waveBasis
#print axioms waveBasis_mul_waveBasisInv
#print axioms waveTransfer_det
#print axioms transfer_left_boundary
#print axioms transfer_right_boundary
#print axioms transfer_transmission_reciprocity
#print axioms transfer_transmissionRight_ne_zero
#print axioms transfer_boundary_states
#print axioms fieldTransfer_waveBasis
#print axioms waveBasis_incoming_states
#print axioms inputFieldStates_det
#print axioms waveBasis_outgoing_states
#print axioms field_transfer_boundary_states
#print axioms fluxForm_conjTranspose
#print axioms fluxDefect_conjTranspose
#print axioms absorption_boundary_flux
#print axioms absorption_fluxDefect_congruence
#print axioms transfer_absorption_fluxDefect
#print axioms absorption_fluxDefect_det
#print axioms transfer_absorption_fluxDefect_det
#print axioms absorption_fluxDefect_ratio
#print axioms transfer_absorption_fluxDefect_ratio
#print axioms coated_fluxDefect
#print axioms coated_fluxDefect_det

end OQ7
