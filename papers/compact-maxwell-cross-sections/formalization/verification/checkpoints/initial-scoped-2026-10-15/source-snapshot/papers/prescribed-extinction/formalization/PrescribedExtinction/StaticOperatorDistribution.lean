import PrescribedExtinction.NewtonTransform

/-! The existing bounded static Fourier operator as an actual distribution on
the original test functions. These identities are the Fourier side of physical
current-operator identification; they do not assume that identification. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory FourierTransform

theorem vectorL2_locallyIntegrable (f : VectorL2) :
    LocallyIntegrable (fun x : Position => f x) volume :=
  (Lp.memLp f).locallyIntegrable (by norm_num)

def vectorL2Distribution (f : VectorL2) : VectorDistribution :=
  Distribution.ofFun ⊤ (fun x : Position => f x) volume ⊤

theorem vectorL2Distribution_apply (f : VectorL2) (φ : ScalarTest) :
    vectorL2Distribution f φ = ∫ x : Position, φ x • f x := by
  exact Distribution.ofFun_apply ((vectorL2_locallyIntegrable f).locallyIntegrableOn _)

theorem vectorL2Distribution_tempered (f : VectorL2) (φ : ScalarTest) :
    vectorL2Distribution f φ = Lp.toTemperedDistribution f (scalarTestSchwartz φ) := by
  rw [vectorL2Distribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change φ x • f x = scalarTestSchwartz φ x • f x
    rw [scalarTestSchwartz_apply]
    exact (IsScalarTower.algebraMap_smul ℂ (φ x) (f x)).symm

def vectorL2ComponentDistribution (f : VectorL2) (i : Fin 3) : ScalarDistribution :=
  Distribution.mapCLM (vectorCoordinate i) (vectorL2Distribution f)

theorem vectorL2ComponentDistribution_apply (f : VectorL2) (i : Fin 3) (φ : ScalarTest) :
    vectorL2ComponentDistribution f i φ = (∫ x : Position, φ x • f x) i := by
  rw [vectorL2ComponentDistribution, Distribution.mapCLM_apply, vectorL2Distribution_apply]
  rfl

theorem staticFourierOperator_tempered_apply (f : VectorL2) (φ : SchwartzMap Position ℂ) :
    Lp.toTemperedDistribution (staticFourierOperator f) φ =
      ∫ ξ : Position, (𝓕⁻ φ) ξ • staticSymbol ξ ((𝓕 f : VectorL2) ξ) := by
  have he : staticFourierOperator f = 𝓕⁻ (staticMultiplierLp (𝓕 f)) := rfl
  rw [he, ← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [staticMultiplierLp_coe (𝓕 f)] with ξ hξ
  rw [hξ]

theorem staticFourierOperator_distribution_apply (f : VectorL2) (φ : ScalarTest) :
    vectorL2Distribution (staticFourierOperator f) φ =
      ∫ ξ : Position, (𝓕⁻ (scalarTestSchwartz φ)) ξ •
        staticSymbol ξ ((𝓕 f : VectorL2) ξ) := by
  rw [vectorL2Distribution_tempered, staticFourierOperator_tempered_apply]

theorem staticFourierOperator_pairing_integrable
    (f : VectorL2) (φ : SchwartzMap Position ℂ) :
    Integrable (fun ξ : Position => φ ξ • staticSymbol ξ (f ξ)) volume := by
  have hi := (φ.memLp 2 volume).norm.integrable_mul (Lp.memLp f).norm
  apply hi.mono'
  · exact φ.continuous.aestronglyMeasurable.smul (staticSymbol_memLp f).aestronglyMeasurable
  · exact ae_of_all _ fun ξ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (staticSymbol_apply_norm_le ξ (f ξ)) (norm_nonneg _)

theorem staticFourierOperator_entry_pairing_integrable
    (f : VectorL2) (φ : SchwartzMap Position ℂ) (i j : Fin 3) :
    Integrable (fun ξ : Position => φ ξ * newtonHessianFrequency i j ξ * f ξ j) volume := by
  have hm : AEStronglyMeasurable
      (fun ξ : Position => φ ξ * newtonHessianFrequency i j ξ * f ξ j) volume := by
    have hf := (vectorCoordinate j).continuous.comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable
    exact (φ.continuous.aestronglyMeasurable.mul
      (newtonHessianFrequency_measurable i j).aestronglyMeasurable).mul hf
  apply ((φ.memLp 2 volume).norm.integrable_mul (Lp.memLp f).norm).mono' hm
  exact ae_of_all _ fun ξ => by
    rw [norm_mul, norm_mul]
    calc
      ‖φ ξ‖ * ‖newtonHessianFrequency i j ξ‖ * ‖f ξ j‖ ≤
          ‖φ ξ‖ * 1 * ‖f ξ‖ := by
        gcongr
        · exact newtonHessianFrequency_norm_le i j ξ
        · exact PiLp.norm_apply_le _ _
      _ = ‖φ ξ‖ * ‖f ξ‖ := by ring

theorem staticFourierOperator_component_distribution_apply
    (f : VectorL2) (i : Fin 3) (φ : ScalarTest) :
    vectorL2ComponentDistribution (staticFourierOperator f) i φ =
      ∑ j : Fin 3, ∫ ξ : Position, (𝓕⁻ (scalarTestSchwartz φ)) ξ *
        newtonHessianFrequency i j ξ * (𝓕 f : VectorL2) ξ j := by
  rw [vectorL2ComponentDistribution, Distribution.mapCLM_apply,
    staticFourierOperator_distribution_apply]
  rw [← (vectorCoordinate i).integral_comp_comm
    (staticFourierOperator_pairing_integrable (𝓕 f) (𝓕⁻ (scalarTestSchwartz φ)))]
  have he (ξ : Position) : vectorCoordinate i
      ((𝓕⁻ (scalarTestSchwartz φ)) ξ • staticSymbol ξ ((𝓕 f : VectorL2) ξ)) =
        ∑ j : Fin 3, (𝓕⁻ (scalarTestSchwartz φ)) ξ *
          newtonHessianFrequency i j ξ * (𝓕 f : VectorL2) ξ j := by
    change (𝓕⁻ (scalarTestSchwartz φ)) ξ *
      (staticSymbol ξ ((𝓕 f : VectorL2) ξ)) i = _
    rw [staticSymbol_coordinate, Finset.mul_sum]
    congr 1
    ext j
    simp only [newtonHessianFrequency]
    ring
  simp_rw [he]
  exact integral_finsetSum _ fun j _ =>
    staticFourierOperator_entry_pairing_integrable (𝓕 f) (𝓕⁻ (scalarTestSchwartz φ)) i j

end OQ7Prescribed
