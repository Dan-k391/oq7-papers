import PrescribedExtinction.RemovablePointIBP

/-! Integration by parts across a genuine inverse-distance pole in three
dimensions. The shrinking annular error is O(ε), so no first-derivative
contact term is lost. This will be applied to the actual outgoing kernel. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter Metric
open scoped Topology

theorem shrinkingCutoffPoleError_norm_le (ε R M C T : ℝ) (hε : 0 < ε)
    (hεR : 2 * ε ≤ R) (hM : 0 ≤ M) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hMb : ∀ s : ℝ, ‖transitionDerivative s‖ ≤ M)
    (F : Position → ℝ) (hFb : ∀ x, ‖x‖ ≤ R → ‖F x‖ ≤ C / ‖x‖)
    (φ : ScalarTest) (hφb : ∀ x, ‖φ x‖ ≤ T) (i : Fin 3) :
    ‖∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x‖ ≤
      (8 * M * C * T * volume.real (ball (0 : Position) 1)) * ε := by
  have hz : ∀ x ∉ closedBall (0 : Position) (2 * ε),
      exteriorCutoffPartial ε ε i x * F x * φ x = 0 := by
    intro x hx
    have hp : exteriorCutoffPartial ε ε i x = 0 := by
      by_contra hn
      exact hx (shrinkingCutoffPartial_support ε hε i hn)
    rw [hp, zero_mul, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ((M / ε) * (C / ε) * T) * volume.real (closedBall (0 : Position) (2 * ε)) := by
      apply norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top
      intro x hx
      by_cases hi : ‖x‖ ≤ ε
      · rw [exteriorCutoffPartial_zero_inner ε ε hε i x hi]
        simp only [zero_mul, norm_zero]
        positivity
      · have hn : ‖x‖ ≤ R :=
          (by simpa only [mem_closedBall, dist_zero_right] using hx : ‖x‖ ≤ 2 * ε).trans hεR
        have hF : ‖F x‖ ≤ C / ε := (hFb x hn).trans
          (div_le_div_of_nonneg_left hC hε (le_of_not_ge hi))
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (exteriorCutoffPartial_norm_le ε ε M hε hM hMb i x)
          hF (norm_nonneg _) (by positivity)) (hφb x) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Measure.addHaar_real_closedBall volume (0 : Position) (by positivity : 0 ≤ 2 * ε)]
      simp only [Position, finrank_euclideanSpace_fin]
      field_simp [hε.ne']
      ring

theorem shrinkingCutoffPoleError_tendsto (F : Position → ℝ)
    (hbound : ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖x‖ ≤ R → ‖F x‖ ≤ C / ‖x‖)
    (φ : ScalarTest) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨R, hR, C, hC, hFb⟩ := hbound
  obtain ⟨M, hM, hMb⟩ := transitionDerivative_global_bound
  obtain ⟨T, hTb⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hT : 0 ≤ T := (norm_nonneg (φ 0)).trans (hTb 0)
  let A : ℝ := 8 * M * C * T * volume.real (ball (0 : Position) 1)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x‖ ≤ A * ε := by
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iio_mem_nhds (by linarith : (0 : ℝ) < R / 2))] with ε hε hεR
    change 0 < ε at hε
    change ε < R / 2 at hεR
    exact shrinkingCutoffPoleError_norm_le ε R M C T hε (by linarith)
      hM hC hT hMb F hFb φ hTb i
  have hl : Tendsto (fun ε : ℝ => A * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.mul ht
  exact squeeze_zero_norm' he hl

theorem pole_point_test_ibp (F D : Position → ℝ) (i : Fin 3)
    (hF : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 F x)
    (hD : ∀ x, x ≠ 0 → HasLineDerivAt ℝ F (D x) x (basisR i))
    (hFI : LocallyIntegrable F volume) (hDI : LocallyIntegrable D volume)
    (hB : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖F x‖ ≤ M / ‖x‖)
    (φ : ScalarTest) :
    (∫ x : Position, F x * (testPartial i φ) x) =
      -(∫ x : Position, D x * φ x) := by
  have hFa : Integrable (fun x : Position => F x * (testPartial i φ) x) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      (testPartial i φ).integrable_smul (hFI.locallyIntegrableOn _)
  have hDa : Integrable (fun x : Position => D x * φ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using φ.integrable_smul (hDI.locallyIntegrableOn _)
  have hleft := shrinking_cutoff_integral_tendsto _ hFa
  have hright := shrinking_cutoff_integral_tendsto _ hDa
  have herr := shrinkingCutoffPoleError_tendsto F hB φ i
  have he : (fun ε : ℝ => ∫ x : Position, exteriorCutoff ε ε x *
      (F x * (testPartial i φ) x)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => -(∫ x : Position, exteriorCutoffPartial ε ε i x * F x * φ x) -
        (∫ x : Position, exteriorCutoff ε ε x * (D x * φ x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hi := contDiff_test_ibp (fun x : Position => exteriorCutoff ε ε x * F x)
      (exteriorCutoff_mul_contDiff ε ε hε hε F hF) φ i
    simp only [exteriorCutoff_mul_lineDeriv ε ε hε hε F D i hD] at hi
    have hb : Integrable (fun x : Position => exteriorCutoffPartial ε ε i x * F x * φ x)
        volume := by
      have hc := exteriorCutoffPartial_mul_integrable ε ε hε hε i
        (fun x : Position => F x * φ x) fun x hx => (hF x hx).continuousAt.mul φ.continuous.continuousAt
      simpa only [mul_assoc] using hc
    have hd : Integrable (fun x : Position => exteriorCutoff ε ε x * (D x * φ x))
        volume := by
      apply hDa.bdd_mul
      · exact (exteriorCutoff_contDiff ε ε hε hε).continuous.aestronglyMeasurable
      · exact ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (exteriorCutoff_nonneg ε ε x)]
          exact exteriorCutoff_le_one ε ε x
    simp_rw [add_mul] at hi
    rw [integral_add hb (by simpa only [mul_assoc] using hd)] at hi
    simpa only [mul_assoc, neg_add, sub_eq_add_neg] using hi
  have hsum := herr.neg.sub hright
  have hsum' : Tendsto (fun ε : ℝ => ∫ x : Position, exteriorCutoff ε ε x *
      (F x * (testPartial i φ) x)) (𝓝[>] (0 : ℝ))
        (𝓝 (-(∫ x : Position, D x * φ x))) := by
    simpa only [neg_zero, zero_sub] using (tendsto_congr' he).mpr hsum
  exact tendsto_nhds_unique hleft hsum'

theorem pole_point_complex_test_ibp (F D : Position → ℂ) (i : Fin 3)
    (hF : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 F x)
    (hD : ∀ x, x ≠ 0 → HasLineDerivAt ℝ F (D x) x (basisR i))
    (hFI : LocallyIntegrable F volume) (hDI : LocallyIntegrable D volume)
    (hB : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖F x‖ ≤ M / ‖x‖)
    (φ : ScalarTest) :
    (∫ x : Position, (testPartial i φ) x • F x) =
      -(∫ x : Position, φ x • D x) := by
  have hFa : Integrable (fun x : Position => (testPartial i φ) x • F x) volume :=
    (testPartial i φ).integrable_smul (hFI.locallyIntegrableOn _)
  have hDa : Integrable (fun x : Position => φ x • D x) volume :=
    φ.integrable_smul (hDI.locallyIntegrableOn _)
  have hFre : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 (fun y => (F y).re) x := by
    intro x hx
    exact Complex.reCLM.contDiff.contDiffAt.comp x (hF x hx)
  have hFim : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 (fun y => (F y).im) x := by
    intro x hx
    exact Complex.imCLM.contDiff.contDiffAt.comp x (hF x hx)
  have hDre : ∀ x, x ≠ 0 →
      HasLineDerivAt ℝ (fun y => (F y).re) (D x).re x (basisR i) := by
    intro x hx
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hD x hx)
  have hDim : ∀ x, x ≠ 0 →
      HasLineDerivAt ℝ (fun y => (F y).im) (D x).im x (basisR i) := by
    intro x hx
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (hD x hx)
  have hLIre (f : Position → ℂ) (hf : LocallyIntegrable f volume) :
      LocallyIntegrable (fun x => (f x).re) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact (hf.integrableOn_isCompact hK).re
  have hLIim (f : Position → ℂ) (hf : LocallyIntegrable f volume) :
      LocallyIntegrable (fun x => (f x).im) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact (hf.integrableOn_isCompact hK).im
  obtain ⟨R, hR, M, hM, hBM⟩ := hB
  have hBre : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖(F x).re‖ ≤ M / ‖x‖ :=
    ⟨R, hR, M, hM, fun x hx => (RCLike.norm_re_le_norm (F x)).trans (hBM x hx)⟩
  have hBim : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖(F x).im‖ ≤ M / ‖x‖ :=
    ⟨R, hR, M, hM, fun x hx => (RCLike.norm_im_le_norm (F x)).trans (hBM x hx)⟩
  have hre := pole_point_test_ibp (fun x => (F x).re) (fun x => (D x).re) i
    hFre hDre (hLIre F hFI) (hLIre D hDI) hBre φ
  have him := pole_point_test_ibp (fun x => (F x).im) (fun x => (D x).im) i
    hFim hDim (hLIim F hFI) (hLIim D hDI) hBim φ
  apply Complex.ext
  · rw [Complex.neg_re]
    change RCLike.re (∫ x : Position, (testPartial i φ) x • F x) =
      -RCLike.re (∫ x : Position, φ x • D x)
    rw [← integral_re hFa, ← integral_re hDa]
    simpa only [RCLike.smul_re, mul_comm] using! hre
  · rw [Complex.neg_im]
    change RCLike.im (∫ x : Position, (testPartial i φ) x • F x) =
      -RCLike.im (∫ x : Position, φ x • D x)
    rw [← integral_im hFa, ← integral_im hDa]
    simpa only [RCLike.smul_im, mul_comm] using! him

end OQ7Prescribed
