import PrescribedExtinction.NewtonShell
import PrescribedExtinction.StaticSymbolCoordinates
import PrescribedExtinction.ShrinkingCutoff

/-! Removable-point integration by parts for actual locally integrable
functions. This analytic lemma will be instantiated with actual dynamic Green
functions; none of its analytic hypotheses is a Maxwell assumption. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

theorem shrinking_cutoff_tendsto (x : Position) (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => exteriorCutoff ε ε x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hn : 0 < ‖x‖ / 2 := div_pos (norm_pos_iff.mpr hx) (by norm_num)
  have he : (fun ε : ℝ => exteriorCutoff ε ε x) =ᶠ[𝓝[>] (0 : ℝ)]
      fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, mem_inf_of_left (Iio_mem_nhds hn)] with ε hε hs
    exact exteriorCutoff_one hε x (by change ε < ‖x‖ / 2 at hs; linarith)
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem shrinking_cutoff_integral_tendsto (f : Position → ℝ) (hf : Integrable f volume) :
    Tendsto (fun ε : ℝ => ∫ x : Position, exteriorCutoff ε ε x * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : Position, f x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ)) (F := fun ε x => exteriorCutoff ε ε x * f x)
    (f := f) (fun x => ‖f x‖)
  · filter_upwards with ε
    have hc : Continuous (exteriorCutoff ε ε) :=
      Real.smoothTransition.continuous.comp ((continuous_norm.sub continuous_const).div_const ε)
    exact hc.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards with ε
    exact ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_of_nonneg (exteriorCutoff_nonneg ε ε x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (exteriorCutoff_le_one ε ε x)
  · exact hf.norm
  · filter_upwards [position_ae_ne_zero] with x hx
    simpa only [one_mul] using (shrinking_cutoff_tendsto x hx).mul_const (f x)

theorem removable_point_test_ibp (F D : Position → ℝ) (i : Fin 3)
    (hF : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 F x)
    (hD : ∀ x, x ≠ 0 → HasLineDerivAt ℝ F (D x) x (basisR i))
    (hFI : LocallyIntegrable F volume) (hDI : LocallyIntegrable D volume)
    (hB : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖F x‖ ≤ M)
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
  have herr := shrinkingCutoffError_tendsto F
    (fun x hx => (hF x hx).continuousAt) hB φ i
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

theorem removable_point_complex_test_ibp (F D : Position → ℂ) (i : Fin 3)
    (hF : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 F x)
    (hD : ∀ x, x ≠ 0 → HasLineDerivAt ℝ F (D x) x (basisR i))
    (hFI : LocallyIntegrable F volume) (hDI : LocallyIntegrable D volume)
    (hB : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖F x‖ ≤ M)
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
      ∀ x : Position, ‖x‖ ≤ R → ‖(F x).re‖ ≤ M :=
    ⟨R, hR, M, hM, fun x hx => (RCLike.norm_re_le_norm (F x)).trans (hBM x hx)⟩
  have hBim : ∃ R : ℝ, 0 < R ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Position, ‖x‖ ≤ R → ‖(F x).im‖ ≤ M :=
    ⟨R, hR, M, hM, fun x hx => (RCLike.norm_im_le_norm (F x)).trans (hBM x hx)⟩
  have hre := removable_point_test_ibp (fun x => (F x).re) (fun x => (D x).re) i
    hFre hDre (hLIre F hFI) (hLIre D hDI) hBre φ
  have him := removable_point_test_ibp (fun x => (F x).im) (fun x => (D x).im) i
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
