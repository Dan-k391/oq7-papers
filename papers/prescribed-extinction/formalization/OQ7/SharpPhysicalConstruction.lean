import OQ7.PhysicalCoreInvariant
import OQ7.PhysicalCoatedCore
import OQ7.MatchedTransfer
import OQ7.TransferSharpLimit
import OQ7.PhysicalSignedTransfer
import OQ7.PhysicalSequenceSqueeze

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7
open Filter Asymptotics CoreConstruction
open scoped Topology ComplexOrder Matrix.Norms.Elementwise

/-- The sharp construction consists entirely of actual finite homogeneous layers.
All original material bounds, exact targets and every layer's thickness are included. -/
theorem sharp_physical_constructed_sequence (p : PhysicalParameters) :
    ∃ layers : ℕ → List HomogeneousLayer, ∃ C : ℝ,
      (∀ᶠ m : ℕ in atTop,
        StackAdmissible p.P p.Q (layers m) ∧ integratedLoss (layers m) = p.M ∧
        stackTransmissionPower p.k (layers m) = p.T ∧
        stackMeanAbsorptance p.k (layers m) = p.a ∧
        p.k * totalThickness (layers m) ≤ Real.pi * (m : ℝ) / Real.sqrt p.P + C) ∧
      Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
        (ScalarEnvelope.D0 p.T p.a - stackAsymmetry p.k (layers m))) atTop
        (𝓝 (ScalarEnvelope.alpha p.T p.a * (p.k * p.M) ^ 4 / (3 * p.Q ^ 2))) := by
  let F : ℕ → Mat2 := fun m => strippedCellTransfer p.k p.P p.Q p.M m ^ m
  have hzero := actual_repeatedCore_operatorNorm_tendsto p.P_gt_one.le p.Q_pos.ne' p.k p.M
  have horder := actual_repeatedCore_operatorNorm_isBigO p.P_gt_one.le p.Q_pos.ne' p.k p.M
  obtain ⟨ψ, hlogs, _, hconv, hrate, htarget⟩ :=
    exact_target_matched_transfer_sequence_operatorNorm (mul_pos p.k_pos p.M_pos) p.active hzero horder
  let ℓ : ℕ → ℝ × ℝ := fun m => ψ (F m)
  let G : ℕ → Mat2 := fun m => matchedTransferMap ψ (F m)
  let ℓ₀ := targetMatchingLogs (p.k * p.M) p.T p.a
  have hℓ : Tendsto ℓ atTop (𝓝 ℓ₀) := hlogs
  obtain ⟨jL, hjL, hcapL⟩ := exists_coatingPairCount p.P_gt_one ℓ₀.1
  obtain ⟨jR, hjR, hcapR⟩ := exists_coatingPairCount p.P_gt_one ℓ₀.2
  let layers : ℕ → List HomogeneousLayer := fun m =>
    physicalCoatedCore p.k p.P p.Q p.M m jL jR (ℓ m)
  let C : ℝ := Real.pi / Real.sqrt p.P + ((jL + jR : ℕ) : ℝ) * Real.pi
  have htransfer (m : ℕ) : stackTransfer p.k (layers m) =
      (-1 : ℂ) ^ (jL + jR + (m + 1)) • G m :=
    physicalCoatedCore_transfer p.k_pos (lt_trans (by norm_num) p.P_gt_one)
      p.Q p.M m hjL hjR (ℓ m)
  have hphysical := physicalCoatedCore_eventually_physical p.k_pos p.P_gt_one p.Q_pos p.M_pos
    hjL hjR hcapL hcapR hℓ
  have hthickness := physicalCoatedCore_eventually_dimensionless_thickness
    p.k_pos p.P_gt_one p.Q_pos p.M_pos hjL hjR hcapL hcapR hℓ
  have hresponse : ∀ᶠ m : ℕ in atTop, matchingResponse (G m) = (p.T, p.a) := by
    simpa only [G, F, matchedTransferMap_response] using htarget
  have hproperties : ∀ᶠ m : ℕ in atTop,
      (fluxDefect (G m)).PosSemidef ∧ (G m).det = 1 ∧ matchingResponse (G m) = (p.T, p.a) := by
    filter_upwards [hphysical, hresponse] with m hm hr
    exact ⟨physical_signed_transfer_fluxPSD p.k_pos hm.1 (htransfer m),
      physical_signed_transfer_det hm.1 (htransfer m), hr⟩
  have hbudget : ∀ᶠ m : ℕ in atTop,
      StackAdmissible p.P p.Q (layers m) ∧ integratedLoss (layers m) = p.M ∧
      stackTransmissionPower p.k (layers m) = p.T ∧
      stackMeanAbsorptance p.k (layers m) = p.a ∧
      p.k * totalThickness (layers m) ≤ Real.pi * (m : ℝ) / Real.sqrt p.P + C := by
    filter_upwards [hphysical, hresponse, hthickness] with m hm hr hw
    have ht := (physical_signed_transfer_response hm.1 (htransfer m)).symm.trans hr
    refine ⟨hm.1, hm.2.1, congrArg Prod.fst ht, congrArg Prod.snd ht, ?_⟩
    simpa only [C, mul_comm (m : ℝ) Real.pi] using hw.le
  have hnative : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      (fluxDefect (stackTransfer p.k (layers m))).det.re) atTop
      (𝓝 ((p.k * p.M) ^ 4 / (3 * p.Q ^ 2))) := by
    simpa only [layers, physicalCoatedCore] using
      physicallyCoatedCore_scaledFluxDeterminant_tendsto p.k_pos p.P_gt_one.le p.Q_pos.ne' p.M
        (fun m => (ℓ m).1) (fun m => (ℓ m).2) hjL hjR
  have hc : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (fluxDefect (G m)).det.re) atTop
      (𝓝 ((p.k * p.M) ^ 4 / (3 * p.Q ^ 2))) := by
    apply hnative.congr
    intro m
    rw [htransfer, signPow_fluxDefect]
  have hsharp := transfer_sharp_deficit_limit p.active G hproperties hconv hrate hc
  refine ⟨layers, C, hbudget, ?_⟩
  have hvalue : ScalarEnvelope.alpha p.T p.a * ((p.k * p.M) ^ 4 / (3 * p.Q ^ 2)) =
      ScalarEnvelope.alpha p.T p.a * (p.k * p.M) ^ 4 / (3 * p.Q ^ 2) := by ring
  rw [hvalue] at hsharp
  apply hsharp.congr
  intro m
  rw [physical_signed_transfer_asymmetry (htransfer m)]
  rfl

/-- The original physical Theorem 5.1, including eventual exact realizability,
strict finite-stack gap and the sharp all-budget supremum asymptotic. -/
theorem theorem51 (p : PhysicalParameters) : Theorem51Statement p := by
  obtain ⟨layers, C, hphysical, hlimit⟩ := sharp_physical_constructed_sequence p
  exact theorem51_of_physical_constructed_sequence p layers C hphysical hlimit

#print axioms sharp_physical_constructed_sequence
#print axioms theorem51
end OQ7
