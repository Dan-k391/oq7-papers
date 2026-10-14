import OQ7.SignedResponse
import OQ7.MatchingResponse
import OQ7.ResourceBounds
import OQ7.PhysicalPassivity

noncomputable section
namespace OQ7
open scoped ComplexOrder

theorem physical_signed_transfer_det {k P Q : ℝ} {layers : List HomogeneousLayer}
    {F : Mat2} {j : ℕ} (h : StackAdmissible P Q layers)
    (hF : stackTransfer k layers = ((-1 : ℂ) ^ j) • F) : F.det = 1 := by
  have hd := stackTransfer_det k h
  rwa [hF, signPow_transfer_det] at hd

theorem physical_signed_transfer_fluxPSD {k P Q : ℝ} {layers : List HomogeneousLayer}
    {F : Mat2} {j : ℕ} (hk : 0 < k) (h : StackAdmissible P Q layers)
    (hF : stackTransfer k layers = ((-1 : ℂ) ^ j) • F) : (fluxDefect F).PosSemidef := by
  have hp := stackTransfer_fluxDefect_posSemidef hk.le h
  rwa [hF, signPow_fluxDefect] at hp

theorem physical_signed_transfer_response {k P Q : ℝ} {layers : List HomogeneousLayer}
    {F : Mat2} {j : ℕ} (h : StackAdmissible P Q layers)
    (hF : stackTransfer k layers = ((-1 : ℂ) ^ j) • F) :
    matchingResponse F = (stackTransmissionPower k layers, stackMeanAbsorptance k layers) := by
  have hd := physical_signed_transfer_det h hF
  have hp := signPow_targetPowers F j
  unfold matchingResponse
  rw [matchingTransmissionPower_physical hd, matchingMeanAbsorptance_physical hd]
  apply Prod.ext
  · unfold stackTransmissionPower stackTransmission
    rw [hF]
    exact hp.1.symm
  · unfold stackMeanAbsorptance stackReflectionLeft stackReflectionRight stackTransmission
    rw [hF]
    exact hp.2.symm

theorem physical_signed_transfer_asymmetry {k : ℝ} {layers : List HomogeneousLayer}
    {F : Mat2} {j : ℕ} (hF : stackTransfer k layers = ((-1 : ℂ) ^ j) • F) :
    stackAsymmetry k layers =
      responseAsymmetry (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F)) := by
  change responseAsymmetry (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
    (transferReflectionRight (waveTransfer (stackTransfer k layers)))
    (transferTransmissionRight (waveTransfer (stackTransfer k layers))) = _
  rw [hF]
  exact unit_smul_responseAsymmetry (signPow_normSq j) F

theorem physical_signed_transfer_invariant {k P Q : ℝ} {layers : List HomogeneousLayer}
    {F : Mat2} {j : ℕ} (hk : 0 < k) (h : StackAdmissible P Q layers)
    (hF : stackTransfer k layers = ((-1 : ℂ) ^ j) • F) :
    stackResourceInvariant k layers = (fluxDefect F).det.re := by
  rw [stackResourceInvariant_eq_fluxDefect hk h, hF, signPow_fluxDefect]

#print axioms physical_signed_transfer_det
#print axioms physical_signed_transfer_fluxPSD
#print axioms physical_signed_transfer_response
#print axioms physical_signed_transfer_asymmetry
#print axioms physical_signed_transfer_invariant
end OQ7
