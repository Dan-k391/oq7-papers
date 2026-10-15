import PrescribedExtinction.WeakCurlFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped ENNReal

theorem compactScalarWeight_memLp (F : Field) (hF : LocallySquareIntegrable F)
    (ψ : Position → ℝ) (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    MemLp (fun x => ψ x • F x) 2 volume := by
  let K := tsupport ψ
  have hK : IsCompact K := hs
  have hF2 : MemLp (K.indicator F) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (hF K hK)
  have hψ : MemLp ψ ⊤ volume := hc.memLp_top_of_hasCompactSupport hs volume
  have h : MemLp (fun x => ψ x • K.indicator F x) 2 volume := hψ.smul hF2
  apply (memLp_congr_ae ?_).mp h
  apply ae_of_all
  intro x
  change ψ x • K.indicator F x = ψ x • F x
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · have hz : ψ x = 0 := by
      by_contra hy
      exact hx (subset_tsupport ψ hy)
    simp [hx, hz]

theorem compactCrossWeight_memLp (F : Field) (hF : LocallySquareIntegrable F)
    (V : Field) (hc : Continuous V) (hs : HasCompactSupport V) :
    MemLp (fun x => cross (V x) (F x)) 2 volume := by
  let K := tsupport V
  have hK : IsCompact K := hs
  have hF2 : MemLp (K.indicator F) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (hF K hK)
  have hv (j : Fin 3) : MemLp (fun x => V x j) ⊤ volume :=
    ((vectorCoordinate j).continuous.comp hc).memLp_top_of_hasCompactSupport
      (hs.comp_left (vectorCoordinate j).map_zero) volume
  have hf (j : Fin 3) : MemLp (fun x => K.indicator F x j) 2 volume := hF2.eval_piLp j
  have hm : MemLp (fun x => cross (V x) (K.indicator F x)) 2 volume := by
    apply memLp_piLp_iff.mpr
    intro i
    fin_cases i
    · exact ((hv 1).mul (hf 2)).sub ((hv 2).mul (hf 1))
    · exact ((hv 2).mul (hf 0)).sub ((hv 0).mul (hf 2))
    · exact ((hv 0).mul (hf 1)).sub ((hv 1).mul (hf 0))
  apply (memLp_congr_ae ?_).mp hm
  apply ae_of_all
  intro x
  change cross (V x) (K.indicator F x) = cross (V x) (F x)
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · have hz : V x = 0 := by
      by_contra hy
      exact hx (subset_tsupport V hy)
    rw [hz]
    ext i
    fin_cases i <;> simp [cross]

theorem memLp_compactSupport_integrable (F : Field) (hF : MemLp F 2 volume)
    (hs : HasCompactSupport F) : Integrable F volume := by
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport F)).mp
  exact (hF.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrableOn_isCompact hs

theorem scalarGradient_zero_off_tsupport (ψ : Position → ℝ) (x : Position)
    (hx : x ∉ tsupport ψ) : scalarGradient ψ x = 0 := by
  have hd := fderiv_of_notMem_tsupport ℝ hx
  ext j
  simp [scalarGradient, hd]

theorem scalarGradient_hasCompactSupport (ψ : Position → ℝ) (hs : HasCompactSupport ψ) :
    HasCompactSupport (scalarGradient ψ) := by
  apply hs.mono'
  intro x hx
  by_contra hn
  exact hx (scalarGradient_zero_off_tsupport ψ x hn)

theorem localizedWeakCurl_memLp (F G : Field) (hF : LocallySquareIntegrable F)
    (hG : LocallySquareIntegrable G) (ψ : Position → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    MemLp (fun x => cross (complexify (scalarGradient ψ x)) (F x) + ψ x • G x) 2 volume := by
  exact (compactCrossWeight_memLp F hF _
    (complexify_continuous.comp (scalarGradient_contDiff ψ hc).continuous)
    ((scalarGradient_hasCompactSupport ψ hs).comp_left (show complexify (0 : Position) = 0 by ext i; simp [complexify]))).add
      (compactScalarWeight_memLp G hG ψ hc.continuous hs)

theorem cross_compactSupport_left (F G : Field) (hF : HasCompactSupport F) :
    HasCompactSupport (fun x => cross (F x) (G x)) := by
  have h := cross_compactSupport_right G F hF
  have he : (fun x => cross (F x) (G x)) = -(fun x => cross (G x) (F x)) :=
    funext (fun x => cross_antisymm (F x) (G x))
  rw [he]
  exact h.neg

theorem localizedWeakCurl_hasCompactSupport (F G : Field) (ψ : Position → ℝ)
    (hs : HasCompactSupport ψ) :
    HasCompactSupport (fun x => cross (complexify (scalarGradient ψ x)) (F x) + ψ x • G x) := by
  have hgrad : HasCompactSupport (fun x => complexify (scalarGradient ψ x)) :=
    (scalarGradient_hasCompactSupport ψ hs).comp_left
      (show complexify (0 : Position) = 0 by ext i; simp [complexify])
  exact (cross_compactSupport_left _ _ hgrad).add (hs.smul_right (f' := G))

theorem four_compact_fields_common_radius (F G C D : Field)
    (hF : HasCompactSupport F) (hG : HasCompactSupport G)
    (hC : HasCompactSupport C) (hD : HasCompactSupport D) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Position, R < ‖x‖ → F x = 0 ∧ G x = 0 ∧ C x = 0 ∧ D x = 0 := by
  let K := tsupport F ∪ tsupport G ∪ tsupport C ∪ tsupport D
  have hK : IsCompact K := ((hF.union hG).union hC).union hD
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnot : x ∉ K := by intro hk; exact (hb x hk).not_gt hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hz
    exact hnot (Or.inl (Or.inl (Or.inl (subset_tsupport F hz))))
  · by_contra hz
    exact hnot (Or.inl (Or.inl (Or.inr (subset_tsupport G hz))))
  · by_contra hz
    exact hnot (Or.inl (Or.inr (subset_tsupport C hz)))
  · by_contra hz
    exact hnot (Or.inr (subset_tsupport D hz))

theorem memLp_toLp_inner_integral (F G : Field) (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    inner ℂ (hF.toLp F) (hG.toLp G) = ∫ x : Position, inner ℂ (F x) (G x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hf hg
  rw [hf, hg]

theorem memLp_inner_integrable (F G : Field) (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    Integrable (fun x => inner ℂ (F x) (G x)) volume := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hF.toLp F) (hG.toLp G)
  apply h.congr
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hf hg
  rw [hf, hg]

theorem locallyL2_inner_compactL2_integrable (F : Field) (hF : LocallySquareIntegrable F)
    (G : Field) (hG : MemLp G 2 volume) (hsG : HasCompactSupport G) :
    Integrable (fun x => inner ℂ (F x) (G x)) volume := by
  let K := tsupport G
  have hK : IsCompact K := hsG
  have hf : MemLp (K.indicator F) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (hF K hK)
  apply (memLp_inner_integrable _ _ hf hG).congr
  apply ae_of_all
  intro x
  change inner ℂ (K.indicator F x) (G x) = inner ℂ (F x) (G x)
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · have hz : G x = 0 := by by_contra hn; exact hx (subset_tsupport G hn)
    rw [hz, inner_zero_right, inner_zero_right]

theorem locallyL2_weighted_inner_integrable (F G : Field) (hF : LocallySquareIntegrable F)
    (hG : LocallySquareIntegrable G) (ψ : Position → ℝ) (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) : Integrable (fun x => inner ℂ (F x) (ψ x • G x)) volume :=
  locallyL2_inner_compactL2_integrable F hF _ (compactScalarWeight_memLp G hG ψ hc hs)
    (hs.smul_right (f' := G))

end OQ7Prescribed
