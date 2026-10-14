import OQ7.MatchingImplicit
import OQ7.MatchingTarget
import OQ7.MatrixNormBridge

noncomputable section
namespace OQ7
open Filter ScalarEnvelope
open scoped Topology Asymptotics Matrix.Norms.Elementwise

theorem targetMatchingLogs_jacobian_conditions {g T a : ℝ} (hg : 0 < g)
    (h : ActiveTarget T a) :
    sheetLogA (targetMatchingLogs g T a) < 1 ∧
      (sheetLogVH g (targetMatchingLogs g T a)).1 -
        (sheetLogVH g (targetMatchingLogs g T a)).2 ≠ 0 := by
  have he := targetMatchingLogs_exp hg h
  have hA : sheetLogA (targetMatchingLogs g T a) = targetSheetA T a := he.1
  have hH : sheetLogH g (targetMatchingLogs g T a) = targetSheetH T a := he.2
  refine ⟨by rw [hA]; exact (targetSheetA_properties h).2.1, ?_⟩
  change sheetLogA (targetMatchingLogs g T a) +
    (sheetLogA (targetMatchingLogs g T a))⁻¹ - sheetLogH g (targetMatchingLogs g T a) ≠ 0
  rw [hA, hH, (targetSheetA_properties h).2.2, targetSheetV_sub_H]
  exact ne_of_gt (div_pos (mul_pos (by norm_num) (active_target_properties h).1)
    (Real.sqrt_pos.mpr h.transmission_pos))

/-- The active targets have a genuine local exact matching map around the
physical limiting sheet, with no remaining Jacobian or response premise. -/
theorem exact_target_matching_exists {g T a : ℝ} (hg : 0 < g) (h : ActiveTarget T a) :
    ∃ ψ : Mat2 → ℝ × ℝ,
      ψ (CoreConstruction.limitingSheet g) = targetMatchingLogs g T a ∧
      Tendsto ψ (𝓝 (CoreConstruction.limitingSheet g)) (𝓝 (targetMatchingLogs g T a)) ∧
      DifferentiableAt ℝ ψ (CoreConstruction.limitingSheet g) ∧
      (fun F => ψ F - targetMatchingLogs g T a) =O[𝓝 (CoreConstruction.limitingSheet g)]
        (fun F => F - CoreConstruction.limitingSheet g) ∧
      ∀ᶠ F in 𝓝 (CoreConstruction.limitingSheet g), matchingLogResponse (F, ψ F) = (T, a) := by
  have hc := targetMatchingLogs_jacobian_conditions hg h
  have hsheet : triangularMatchingTransfer 1 g = CoreConstruction.limitingSheet g := by
    rw [CoreConstruction.limitingSheet_explicit]
    simp [triangularMatchingTransfer]
  rcases matching_implicit_sheet_exists hg (targetMatchingLogs g T a) hc.1 hc.2 with
    ⟨ψ, hψ, ht, hd, ho, he⟩
  rw [hsheet] at hψ ht hd ho he
  refine ⟨ψ, hψ, ht, hd, ho, ?_⟩
  filter_upwards [he] with F hF
  exact hF.trans (targetMatchingLogs_response hg h)

/-- The quantitative exact correction applied to a genuine core sequence.
The incoming bound explicitly uses the exponential module's operator norm. -/
theorem exact_target_matching_sequence_operatorNorm {g T a : ℝ} (hg : 0 < g)
    (h : ActiveTarget T a) {ι : Type*} {l : Filter ι} {F : ι → Mat2} {r : ι → ℝ}
    (hzero : Tendsto (fun j => matrixOperatorNorm (F j - CoreConstruction.limitingSheet g))
      l (𝓝 0))
    (horder : (fun j => matrixOperatorNorm (F j - CoreConstruction.limitingSheet g)) =O[l] r) :
    ∃ logs : ι → ℝ × ℝ,
      Tendsto logs l (𝓝 (targetMatchingLogs g T a)) ∧
      (fun j => logs j - targetMatchingLogs g T a) =O[l] r ∧
      ∀ᶠ j in l, matchingLogResponse (F j, logs j) = (T, a) := by
  have hF := matrix_tendsto_of_operatorNorm hzero
  have hFo := matrix_isBigO_of_operatorNorm horder
  rcases exact_target_matching_exists hg h with ⟨ψ, _, ht, _, ho, he⟩
  exact ⟨ψ ∘ F, ht.comp hF, (ho.comp_tendsto hF).trans hFo, hF.eventually he⟩

#print axioms targetMatchingLogs_jacobian_conditions
#print axioms exact_target_matching_exists
#print axioms exact_target_matching_sequence_operatorNorm
end OQ7
