import OQ7.MatchingJacobian

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7
open Filter
open scoped Topology Asymptotics Matrix.Norms.Elementwise

/-- The actual coating partial of the eight-real-entry response is invertible
at the limiting sheet. Its two factors are the explicit Jacobians. -/
theorem matchingLogResponse_sheet_coating_partial {g : ℝ} (hg : 0 < g)
    (ℓ : ℝ × ℝ) (hA : sheetLogA ℓ < 1)
    (hdiff : (sheetLogVH g ℓ).1 - (sheetLogVH g ℓ).2 ≠ 0) :
    ((fderiv ℝ matchingLogResponse (triangularMatchingTransfer 1 g, ℓ)) ∘L
      ContinuousLinearMap.inr ℝ Mat2 (ℝ × ℝ)).IsInvertible := by
  have hApos : 0 < sheetLogA ℓ := Real.exp_pos _
  have hHpos : 0 < sheetLogH g ℓ := mul_pos hg (Real.exp_pos _)
  have hd : waveTransfer (logCoatedTransfer (triangularMatchingTransfer 1 g) ℓ) 1 1 ≠ 0 := by
    rw [logCoatedTransfer_sheet]
    exact triangularMatchingTransfer_denominator_ne_zero hApos hHpos
  have hc := matchingLogResponse_contDiffAt 1 (triangularMatchingTransfer 1 g, ℓ) hd
  have hf := (hc.differentiableAt one_ne_zero).hasFDerivAt
  have hpartial := hf.comp ℓ (hasFDerivAt_prodMk_right (triangularMatchingTransfer 1 g) ℓ)
  have heq := hpartial.unique (matchingLogResponse_sheet_hasFDerivAt hg ℓ)
  rw [heq]
  exact matchingSheetLogJacobian_isInvertible hg ℓ hA hdiff

/-- Local exact target correction with all eight real core entries as parameters.
The correction is differentiable and has first-order control by core perturbation. -/
theorem matching_implicit_sheet_exists {g : ℝ} (hg : 0 < g) (ℓ : ℝ × ℝ)
    (hA : sheetLogA ℓ < 1)
    (hdiff : (sheetLogVH g ℓ).1 - (sheetLogVH g ℓ).2 ≠ 0) :
    ∃ ψ : Mat2 → ℝ × ℝ,
      ψ (triangularMatchingTransfer 1 g) = ℓ ∧
      Tendsto ψ (𝓝 (triangularMatchingTransfer 1 g)) (𝓝 ℓ) ∧
      DifferentiableAt ℝ ψ (triangularMatchingTransfer 1 g) ∧
      (fun F => ψ F - ℓ) =O[𝓝 (triangularMatchingTransfer 1 g)]
        (fun F => F - triangularMatchingTransfer 1 g) ∧
      ∀ᶠ F in 𝓝 (triangularMatchingTransfer 1 g),
        matchingLogResponse (F, ψ F) =
          matchingLogResponse (triangularMatchingTransfer 1 g, ℓ) := by
  have hApos : 0 < sheetLogA ℓ := Real.exp_pos _
  have hHpos : 0 < sheetLogH g ℓ := mul_pos hg (Real.exp_pos _)
  have hd : waveTransfer (logCoatedTransfer (triangularMatchingTransfer 1 g) ℓ) 1 1 ≠ 0 := by
    rw [logCoatedTransfer_sheet]
    exact triangularMatchingTransfer_denominator_ne_zero hApos hHpos
  have hc := matchingLogResponse_contDiffAt 1 (triangularMatchingTransfer 1 g, ℓ) hd
  have dfu := hc.hasStrictFDerivAt one_ne_zero
  have hp := matchingLogResponse_sheet_coating_partial hg ℓ hA hdiff
  let ψ := dfu.implicitFunctionOfProdDomain hp
  have hψ : ψ (triangularMatchingTransfer 1 g) = ℓ :=
    (dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain hp).self_of_nhds.mp rfl
  have hs := dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain hp
  refine ⟨ψ, hψ, dfu.tendsto_implicitFunctionOfProdDomain hp,
    hs.hasFDerivAt.differentiableAt, ?_, dfu.eventually_apply_implicitFunctionOfProdDomain hp⟩
  have ho : (fun F => ψ F - ψ (triangularMatchingTransfer 1 g)) =O[𝓝 (triangularMatchingTransfer 1 g)]
      (fun F => F - triangularMatchingTransfer 1 g) := hs.hasFDerivAt.isBigO_sub
  simpa only [hψ] using ho

/-- A converging physical core family inherits exact target correction and its
perturbation order. No interpolation in the integer repetition counter is used. -/
theorem matching_implicit_sheet_sequence {g : ℝ} (hg : 0 < g) (ℓ : ℝ × ℝ)
    (hA : sheetLogA ℓ < 1)
    (hdiff : (sheetLogVH g ℓ).1 - (sheetLogVH g ℓ).2 ≠ 0)
    {ι : Type*} {l : Filter ι} {F : ι → Mat2} {r : ι → ℝ}
    (hF : Tendsto F l (𝓝 (triangularMatchingTransfer 1 g)))
    (horder : (fun j => F j - triangularMatchingTransfer 1 g) =O[l] r) :
    ∃ ψ : Mat2 → ℝ × ℝ,
      Tendsto (ψ ∘ F) l (𝓝 ℓ) ∧
      (fun j => ψ (F j) - ℓ) =O[l] r ∧
      ∀ᶠ j in l, matchingLogResponse (F j, ψ (F j)) =
        matchingLogResponse (triangularMatchingTransfer 1 g, ℓ) := by
  rcases matching_implicit_sheet_exists hg ℓ hA hdiff with
    ⟨ψ, hψ, ht, _, ho, he⟩
  exact ⟨ψ, ht.comp hF, (ho.comp_tendsto hF).trans horder, hF.eventually he⟩

#print axioms matchingLogResponse_sheet_coating_partial
#print axioms matching_implicit_sheet_exists
#print axioms matching_implicit_sheet_sequence
end OQ7
