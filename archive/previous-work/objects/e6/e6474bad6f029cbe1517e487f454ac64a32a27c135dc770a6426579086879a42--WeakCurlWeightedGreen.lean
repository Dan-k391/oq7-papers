import work.WeakCurlLocalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped ENNReal

/-- Local weak Green identity with a compact smooth scalar weight, derived
from compact L2 Fourier integration by parts. No differentiability of the
four weak fields is assumed. -/
theorem weakCurl_weighted_inner_identity (F G C D : Field)
    (hF : LocallySquareIntegrable F) (hG : LocallySquareIntegrable G)
    (hC : LocallySquareIntegrable C) (hD : LocallySquareIntegrable D)
    (hFC : HasWeakCurl F C) (hGD : HasWeakCurl G D)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsψ : HasCompactSupport ψ) :
    (∫ x : Position, inner ℂ (F x)
      (cross (complexify (scalarGradient ψ x)) (G x) + ψ x • D x)) =
      ∫ x : Position, inner ℂ (C x) (ψ x • G x) := by
  let K := tsupport ψ
  obtain ⟨R, hR, hb⟩ := hsψ.isBounded.exists_pos_norm_lt
  let χ : ContDiffBump (0 : Position) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  let F' : Field := fun x => χ x • F x
  let G' : Field := fun x => ψ x • G x
  let C' : Field := fun x => cross (complexify (scalarGradient χ x)) (F x) + χ x • C x
  let D' : Field := fun x => cross (complexify (scalarGradient ψ x)) (G x) + ψ x • D x
  have hF2 : MemLp F' 2 volume := compactScalarWeight_memLp F hF χ χ.continuous χ.hasCompactSupport
  have hG2 : MemLp G' 2 volume := compactScalarWeight_memLp G hG ψ hψ.continuous hsψ
  have hC2 : MemLp C' 2 volume := localizedWeakCurl_memLp F C hF hC χ χ.contDiff χ.hasCompactSupport
  have hD2 : MemLp D' 2 volume := localizedWeakCurl_memLp G D hG hD ψ hψ hsψ
  have hsF : HasCompactSupport F' := χ.hasCompactSupport.smul_right (f' := F)
  have hsG : HasCompactSupport G' := hsψ.smul_right (f' := G)
  have hsC : HasCompactSupport C' := localizedWeakCurl_hasCompactSupport F C χ χ.hasCompactSupport
  have hsD : HasCompactSupport D' := localizedWeakCurl_hasCompactSupport G D ψ hsψ
  have hF1 : MemLp F' 1 volume := memLp_one_iff_integrable.mpr (memLp_compactSupport_integrable F' hF2 hsF)
  have hG1 : MemLp G' 1 volume := memLp_one_iff_integrable.mpr (memLp_compactSupport_integrable G' hG2 hsG)
  have hC1 : MemLp C' 1 volume := memLp_one_iff_integrable.mpr (memLp_compactSupport_integrable C' hC2 hsC)
  have hD1 : MemLp D' 1 volume := memLp_one_iff_integrable.mpr (memLp_compactSupport_integrable D' hD2 hsD)
  have hfc : HasWeakCurl F' C' := hFC.real_smul_field F C
    (locallySquareIntegrable_locallyIntegrable _ hF) (locallySquareIntegrable_locallyIntegrable _ hC) χ χ.contDiff
  have hgd : HasWeakCurl G' D' := hGD.real_smul_field G D
    (locallySquareIntegrable_locallyIntegrable _ hG) (locallySquareIntegrable_locallyIntegrable _ hD) ψ hψ
  obtain ⟨S, hS, hv⟩ := four_compact_fields_common_radius F' G' C' D' hsF hsG hsC hsD
  have he := compactWeakCurl_integral_inner F' G' C' D' hF1 hF2 hG1 hG2 hC1 hC2 hD1 hD2
    hfc hgd S hS.le (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2.1)
      (fun x hx => (hv x hx).2.2.1) (fun x hx => (hv x hx).2.2.2)
  rw [memLp_toLp_inner_integral F' D' hF2 hD2, memLp_toLp_inner_integral C' G' hC2 hG2] at he
  have hcz (v : Vector) : cross (complexify (0 : Position)) v = 0 := by
    ext i
    fin_cases i <;> simp [cross, complexify]
  have hl (x : Position) : inner ℂ (F' x) (D' x) = inner ℂ (F x) (D' x) := by
    by_cases hx : x ∈ K
    · have hr : ‖x‖ ≤ R + 1 := by have h := hb x hx; linarith
      change inner ℂ (χ x • F x) (D' x) = _
      rw [χ.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hr), one_smul]
    · have hz : ψ x = 0 := by by_contra hn; exact hx (subset_tsupport ψ hn)
      have hd : D' x = 0 := by
        dsimp [D']
        rw [scalarGradient_zero_off_tsupport ψ x hx, hcz, hz, zero_smul, add_zero]
      rw [hd, inner_zero_right, inner_zero_right]
  have hr (x : Position) : inner ℂ (C' x) (G' x) = inner ℂ (C x) (G' x) := by
    by_cases hx : x ∈ K
    · have hxχ : ‖x‖ < χ.rIn := by dsimp [χ]; have h := hb x hx; linarith
      have hχ : χ x = 1 := χ.one_of_mem_closedBall
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hxχ.le)
      change inner ℂ (cross (complexify (scalarGradient χ x)) (F x) + χ x • C x) (G' x) = _
      rw [bump_scalarGradient_zero χ x hxχ, hcz, hχ, one_smul, zero_add]
    · have hz : G' x = 0 := by
        have hψx : ψ x = 0 := by by_contra hn; exact hx (subset_tsupport ψ hn)
        simp [G', hψx]
      rw [hz, inner_zero_right, inner_zero_right]
  calc
    _ = ∫ x : Position, inner ℂ (F' x) (D' x) := integral_congr_ae (ae_of_all _ fun x => (hl x).symm)
    _ = ∫ x : Position, inner ℂ (C' x) (G' x) := he
    _ = _ := integral_congr_ae (ae_of_all _ hr)

end OQ7Prescribed
