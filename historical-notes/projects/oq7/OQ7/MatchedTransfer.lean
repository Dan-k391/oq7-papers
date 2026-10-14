import OQ7.MatchingTargetImplicit

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7
open Filter ScalarEnvelope
open scoped Topology Asymptotics Matrix.Norms.Elementwise

/-- The matrix of the core together with the exact matching coatings. -/
def matchedTransferMap (ψ : Mat2 → ℝ × ℝ) (F : Mat2) : Mat2 :=
  logCoatedTransfer F (ψ F)

theorem matchedTransferMap_differentiableAt {ψ : Mat2 → ℝ × ℝ} {F₀ : Mat2}
    (hψ : DifferentiableAt ℝ ψ F₀) : DifferentiableAt ℝ (matchedTransferMap ψ) F₀ := by
  have ho : DifferentiableAt ℝ (fun u : Mat2 × (ℝ × ℝ) => logCoatedTransfer u.1 u.2)
      (F₀, ψ F₀) :=
    (logCoatedTransfer_contDiff 1).contDiffAt.differentiableAt one_ne_zero
  have hi : DifferentiableAt ℝ (fun F : Mat2 => (F, ψ F)) F₀ :=
    differentiableAt_id.prodMk hψ
  simpa only [matchedTransferMap, Function.comp_def] using! ho.comp F₀ hi

theorem matchedTransferMap_isBigO {ψ : Mat2 → ℝ × ℝ} {F₀ : Mat2}
    (hψ : DifferentiableAt ℝ ψ F₀) :
    (fun F => matchedTransferMap ψ F - matchedTransferMap ψ F₀) =O[𝓝 F₀]
      (fun F => F - F₀) :=
  (matchedTransferMap_differentiableAt hψ).isBigO_sub

theorem matchedTransferMap_response (ψ : Mat2 → ℝ × ℝ) (F : Mat2) :
    matchingResponse (matchedTransferMap ψ F) = matchingLogResponse (F, ψ F) := rfl

theorem matchedTransferMap_det (ψ : Mat2 → ℝ × ℝ) (F : Mat2) :
    (matchedTransferMap ψ F).det = F.det := logCoatedTransfer_det F (ψ F)

theorem matchedTransferMap_eq_physical_scales (ψ : Mat2 → ℝ × ℝ) (F : Mat2) :
    matchedTransferMap ψ F = losslessDiagonalScale (ψ F).2 * F * losslessDiagonalScale (ψ F).1 :=
  logCoatedTransfer_eq_physical_scale F (ψ F)

theorem exact_target_matched_transfer_maps {g T a : ℝ} (hg : 0 < g) (h : ActiveTarget T a) :
    ∃ ψ : Mat2 → ℝ × ℝ,
      ψ (CoreConstruction.limitingSheet g) = targetMatchingLogs g T a ∧
      Tendsto ψ (𝓝 (CoreConstruction.limitingSheet g)) (𝓝 (targetMatchingLogs g T a)) ∧
      DifferentiableAt ℝ ψ (CoreConstruction.limitingSheet g) ∧
      DifferentiableAt ℝ (matchedTransferMap ψ) (CoreConstruction.limitingSheet g) ∧
      matchedTransferMap ψ (CoreConstruction.limitingSheet g) =
        triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a) ∧
      (fun F => matchedTransferMap ψ F -
        triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))
          =O[𝓝 (CoreConstruction.limitingSheet g)] (fun F => F - CoreConstruction.limitingSheet g) ∧
      ∀ᶠ F in 𝓝 (CoreConstruction.limitingSheet g), matchingLogResponse (F, ψ F) = (T, a) := by
  rcases exact_target_matching_exists hg h with ⟨ψ, hψ, ht, hd, _, he⟩
  have hvalue : matchedTransferMap ψ (CoreConstruction.limitingSheet g) =
      triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a) := by
    unfold matchedTransferMap
    rw [hψ, targetMatchingLogs_coated_sheet hg h]
  refine ⟨ψ, hψ, ht, hd, matchedTransferMap_differentiableAt hd, hvalue, ?_, he⟩
  simpa only [hvalue] using matchedTransferMap_isBigO hd

/-- Exact matching along a finite-core family. Both coating-log and full matched
transfer errors retain the explicit incoming operator-norm perturbation order. -/
theorem exact_target_matched_transfer_sequence_operatorNorm {g T a : ℝ}
    (hg : 0 < g) (h : ActiveTarget T a) {ι : Type*} {l : Filter ι}
    {F : ι → Mat2} {r : ι → ℝ}
    (hzero : Tendsto (fun j => matrixOperatorNorm (F j - CoreConstruction.limitingSheet g)) l (𝓝 0))
    (horder : (fun j => matrixOperatorNorm (F j - CoreConstruction.limitingSheet g)) =O[l] r) :
    ∃ ψ : Mat2 → ℝ × ℝ,
      Tendsto (ψ ∘ F) l (𝓝 (targetMatchingLogs g T a)) ∧
      (fun j => ψ (F j) - targetMatchingLogs g T a) =O[l] r ∧
      Tendsto (matchedTransferMap ψ ∘ F) l
        (𝓝 (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))) ∧
      (fun j => matchedTransferMap ψ (F j) -
        triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) =O[l] r ∧
      ∀ᶠ j in l, matchingLogResponse (F j, ψ (F j)) = (T, a) := by
  have hF := matrix_tendsto_of_operatorNorm hzero
  have hFo := matrix_isBigO_of_operatorNorm horder
  rcases exact_target_matched_transfer_maps hg h with ⟨ψ, hψ, ht, hd, hdt, hv, ho, he⟩
  have hlogs : (fun F => ψ F - targetMatchingLogs g T a) =O[𝓝 (CoreConstruction.limitingSheet g)]
      (fun F => F - CoreConstruction.limitingSheet g) := by
    simpa only [hψ] using! hd.isBigO_sub
  refine ⟨ψ, ht.comp hF, (hlogs.comp_tendsto hF).trans hFo, ?_,
    (ho.comp_tendsto hF).trans hFo, hF.eventually he⟩
  simpa only [hv] using hdt.continuousAt.tendsto.comp hF

#print axioms matchedTransferMap_differentiableAt
#print axioms matchedTransferMap_isBigO
#print axioms matchedTransferMap_response
#print axioms matchedTransferMap_det
#print axioms matchedTransferMap_eq_physical_scales
#print axioms exact_target_matched_transfer_maps
#print axioms exact_target_matched_transfer_sequence_operatorNorm
end OQ7
