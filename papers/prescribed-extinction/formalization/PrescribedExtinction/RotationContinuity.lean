import PrescribedExtinction.PhysicalResponseStability
import PrescribedExtinction.RotationExtinction
import PrescribedExtinction.RankOneAbsorption

noncomputable section
set_option maxHeartbeats 200000
namespace OQ7Prescribed
open MeasureTheory

section SupportedParameter
variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def supportedConstMapParameterLinear (μ : Measure α) (s : Set α) :
    (E →L[ℂ] F) →ₗ[ℂ] SetSupportedL2 (E := E) μ s →L[ℂ] SetSupportedL2 (E := F) μ s where
  toFun := supportedConstMap μ s
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact ContinuousLinearMap.add_compLp A B (f : Lp E 2 μ)
  map_smul' z A := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact ContinuousLinearMap.smul_compLp z A (f : Lp E 2 μ)

theorem supportedConstMap_norm_le (μ : Measure α) (s : Set α) (A : E →L[ℂ] F) :
    ‖supportedConstMap μ s A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le (supportedConstMapLinear μ s A) (norm_nonneg A) _

theorem supportedConstMap_lipschitz (μ : Measure α) (s : Set α) :
    LipschitzWith 1 (supportedConstMap (E := E) (F := F) μ s) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  rw [dist_eq_norm, dist_eq_norm]
  change ‖supportedConstMap μ s A - supportedConstMap μ s B‖ ≤ 1 * ‖A - B‖
  rw [one_mul]
  have he : supportedConstMap μ s (A - B) = supportedConstMap μ s A - supportedConstMap μ s B :=
    map_sub (supportedConstMapParameterLinear (E := E) (F := F) μ s) A B
  rw [← he]
  exact supportedConstMap_norm_le μ s (A - B)

theorem supportedConstMap_continuous (μ : Measure α) (s : Set α) :
    Continuous (supportedConstMap (E := E) (F := F) μ s) :=
  (supportedConstMap_lipschitz (E := E) (F := F) μ s).continuous

theorem twoPieceSupportedMap_continuous (μ : Measure α) (s t : Set α) (ht : MeasurableSet t) :
    Continuous (fun p : (E →L[ℂ] F) × (E →L[ℂ] F) => twoPieceSupportedMap μ s t ht p.1 p.2) := by
  exact (((supportedConstMap_continuous (E := E) (F := F) μ s).comp continuous_fst).clm_comp continuous_const).add
    (((supportedConstMap_continuous (E := E) (F := F) μ s).comp continuous_snd).clm_comp continuous_const)

end SupportedParameter

theorem axisEmbedding_continuous : Continuous axisEmbedding :=
  ((ContinuousLinearMap.smulRightL ℂ ℂ Vector) (ContinuousLinearMap.id ℂ ℂ)).continuous.comp complexify_continuous

theorem rotatedAxis_continuous : Continuous rotatedAxis := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [rotatedAxis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> fun_prop

theorem activeInjection_rotation_continuous (B : TwoLayerBody) :
    Continuous (fun θ : ℝ => activeInjection B (basisR 0) (rotatedAxis θ)) := by
  unfold activeInjection
  have hp : Continuous (fun θ : ℝ => (axisEmbedding (basisR 0), axisEmbedding (rotatedAxis θ))) :=
    continuous_const.prodMk (axisEmbedding_continuous.comp rotatedAxis_continuous)
  have hc := twoPieceSupportedMap_continuous (α := Position) (E := ℂ) (F := Vector)
    (volume : Measure Position) B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
  have hh := hc.comp hp
  simpa only [Function.comp_def] using hh

theorem activeProjection_rotation_continuous (B : TwoLayerBody) :
    Continuous (fun θ : ℝ => activeProjection B (basisR 0) (rotatedAxis θ)) := by
  unfold activeProjection
  have hc : Continuous (fun θ : ℝ => (axisEmbedding (rotatedAxis θ)).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp (axisEmbedding_continuous.comp rotatedAxis_continuous)
  have hp : Continuous (fun θ : ℝ => ((axisEmbedding (basisR 0)).adjoint, (axisEmbedding (rotatedAxis θ)).adjoint)) :=
    continuous_const.prodMk hc
  have ht := twoPieceSupportedMap_continuous (α := Position) (E := Vector) (F := ℂ)
    (volume : Measure Position) B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
  have hh := ht.comp hp
  simpa only [Function.comp_def] using hh

theorem activeMaterialOperator_rotation_continuous (k : ℝ) (B : TwoLayerBody) (α β : ℂ) :
    Continuous (fun θ : ℝ => activeMaterialOperator k B (basisR 0) (rotatedAxis θ) α β) :=
  ((activeProjection_rotation_continuous B).clm_comp
    (continuous_const.clm_comp (activeInjection_rotation_continuous B))).sub continuous_const

theorem normalizedActiveResponse_continuous (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ : ℝ => normalizedActiveResponse k hk B σ θ α β hα hβ) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  apply continuousLinearEquiv_response_continuousAt
    (fun φ => activeMaterialEquiv k hk B (basisR 0) (rotatedAxis φ) α β hα hβ)
    (fun _ => -normalizedIncidentDrive k B σ) θ
    (1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β))
  · intro φ
    exact activeMaterialEquiv_inverse_norm_le k hk B (basisR 0) (rotatedAxis φ) α β hα hβ
  · have he : (fun φ : ℝ => (activeMaterialEquiv k hk B (basisR 0) (rotatedAxis φ) α β hα hβ).toContinuousLinearMap) =
        (fun φ => activeMaterialOperator k B (basisR 0) (rotatedAxis φ) α β) := by
      funext φ
      apply ContinuousLinearMap.ext
      intro q
      exact activeMaterialEquiv_apply k hk B (basisR 0) (rotatedAxis φ) α β hα hβ q
    rw [he]
    exact (activeMaterialOperator_rotation_continuous k B α β).continuousAt
  · exact continuousAt_const

theorem normalizedExtinction_continuous (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ : ℝ => normalizedExtinction k hk B σ θ α β hα hβ) :=
  continuous_const.mul (Complex.imCLM.continuous.comp
    (continuous_const.inner (normalizedActiveResponse_continuous k hk B σ α β hα hβ)))

theorem normalizedAbsorption_continuous (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ : ℝ => normalizedAbsorption k hk B σ θ α β hα hβ) := by
  have hr := normalizedActiveResponse_continuous k hk B σ α β hα hβ
  exact continuous_const.mul (Complex.imCLM.continuous.comp
    (hr.inner ((activeInverseMaterial B α β).continuous.comp hr))).neg

end OQ7Prescribed
