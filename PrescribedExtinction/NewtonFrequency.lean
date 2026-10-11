import PrescribedExtinction.NewtonTempered
import PrescribedExtinction.StaticSymbolCoordinates

/-! The actual inverse-square candidate frequency kernel is locally
integrable in three dimensions and defines a genuine tempered distribution.
Its value at zero is fixed to zero; this does not assert that it is the
Fourier transform of the Newton kernel. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped SchwartzMap ENNReal

def newtonFrequencyKernel (ξ : Position) : ℂ :=
  (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)

theorem newtonFrequencyKernel_zero : newtonFrequencyKernel 0 = 0 := by
  simp [newtonFrequencyKernel]

theorem newtonFrequencyKernel_norm (ξ : Position) :
    ‖newtonFrequencyKernel ξ‖ = (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ := by
  rw [newtonFrequencyKernel, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem newtonFrequencyKernel_measurable : Measurable newtonFrequencyKernel := by
  unfold newtonFrequencyKernel
  fun_prop

theorem newtonFrequencyKernel_locallyIntegrable :
    LocallyIntegrable newtonFrequencyKernel volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi ^ 2)⁻¹) (α := 2)
    (by norm_num [Position, finrank_euclideanSpace_fin])
    (by norm_num [Position, finrank_euclideanSpace_fin])
    (ae_of_all _ fun ξ => ?_) newtonFrequencyKernel_measurable.aestronglyMeasurable
  rw [newtonFrequencyKernel_norm]
  simp [mul_inv_rev, mul_comm]

def newtonFrequencyLocal : Position → ℂ :=
  (Metric.closedBall (0 : Position) 1).indicator newtonFrequencyKernel

def newtonFrequencyExterior : Position → ℂ :=
  (Metric.closedBall (0 : Position) 1)ᶜ.indicator newtonFrequencyKernel

theorem newtonFrequencyLocal_memLp : MemLp newtonFrequencyLocal 1 volume := by
  rw [newtonFrequencyLocal, memLp_indicator_iff_restrict Metric.isClosed_closedBall.measurableSet,
    memLp_one_iff_integrable]
  exact newtonFrequencyKernel_locallyIntegrable.integrableOn_isCompact (isCompact_closedBall _ _)

theorem newtonFrequencyExterior_memLp : MemLp newtonFrequencyExterior ∞ volume := by
  apply memLp_top_of_bound
    (newtonFrequencyKernel_measurable.aestronglyMeasurable.indicator
      Metric.isClosed_closedBall.measurableSet.compl) ((4 * Real.pi ^ 2)⁻¹)
  exact ae_of_all _ fun ξ => by
    change ‖newtonFrequencyExterior ξ‖ ≤ (4 * Real.pi ^ 2)⁻¹
    by_cases hx : ξ ∈ Metric.closedBall (0 : Position) 1
    · rw [newtonFrequencyExterior, indicator_of_notMem
        (show ξ ∉ (Metric.closedBall (0 : Position) 1)ᶜ from not_not.mpr hx), norm_zero]
      positivity
    · have hn : 1 < ‖ξ‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
      rw [newtonFrequencyExterior, indicator_of_mem
        (show ξ ∈ (Metric.closedBall (0 : Position) 1)ᶜ from hx), newtonFrequencyKernel_norm]
      apply (inv_le_inv₀ (by positivity : 0 < 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)
        (by positivity : 0 < 4 * Real.pi ^ 2)).mpr
      have hsq : 1 ≤ ‖ξ‖ ^ 2 := by nlinarith
      have h := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * Real.pi ^ 2)
      simpa only [mul_one] using h

theorem newtonFrequencyKernel_split (ξ : Position) :
    newtonFrequencyLocal ξ + newtonFrequencyExterior ξ = newtonFrequencyKernel ξ := by
  classical
  by_cases hx : ξ ∈ Metric.closedBall (0 : Position) 1 <;>
    simp [newtonFrequencyLocal, newtonFrequencyExterior, hx]

def newtonFrequencyTempered : TemperedDistribution Position ℂ :=
  Lp.toTemperedDistribution (newtonFrequencyLocal_memLp.toLp newtonFrequencyLocal) +
    Lp.toTemperedDistribution (newtonFrequencyExterior_memLp.toLp newtonFrequencyExterior)

theorem newtonFrequency_local_schwartz_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun ξ => φ ξ * newtonFrequencyLocal ξ) volume :=
  (φ.memLp ∞ volume).integrable_mul newtonFrequencyLocal_memLp

theorem newtonFrequency_exterior_schwartz_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun ξ => φ ξ * newtonFrequencyExterior ξ) volume :=
  (φ.memLp 1 volume).integrable_mul newtonFrequencyExterior_memLp

theorem newtonFrequency_schwartz_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun ξ => φ ξ * newtonFrequencyKernel ξ) volume := by
  have h := (newtonFrequency_local_schwartz_integrable φ).add
    (newtonFrequency_exterior_schwartz_integrable φ)
  change Integrable (fun ξ => φ ξ * newtonFrequencyLocal ξ +
    φ ξ * newtonFrequencyExterior ξ) volume at h
  simpa only [← mul_add, newtonFrequencyKernel_split] using h

theorem newtonFrequencyTempered_apply (φ : SchwartzMap Position ℂ) :
    newtonFrequencyTempered φ = ∫ ξ : Position, φ ξ * newtonFrequencyKernel ξ := by
  change Lp.toTemperedDistribution (newtonFrequencyLocal_memLp.toLp _) φ +
    Lp.toTemperedDistribution (newtonFrequencyExterior_memLp.toLp _) φ = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
  have hl : (∫ ξ : Position, φ ξ * (newtonFrequencyLocal_memLp.toLp _ : Position → ℂ) ξ) =
      ∫ ξ : Position, φ ξ * newtonFrequencyLocal ξ := by
    apply integral_congr_ae
    filter_upwards [newtonFrequencyLocal_memLp.coeFn_toLp] with ξ hξ
    rw [hξ]
  have he : (∫ ξ : Position, φ ξ * (newtonFrequencyExterior_memLp.toLp _ : Position → ℂ) ξ) =
      ∫ ξ : Position, φ ξ * newtonFrequencyExterior ξ := by
    apply integral_congr_ae
    filter_upwards [newtonFrequencyExterior_memLp.coeFn_toLp] with ξ hξ
    rw [hξ]
  rw [hl, he, ← integral_add (newtonFrequency_local_schwartz_integrable φ)
    (newtonFrequency_exterior_schwartz_integrable φ)]
  simp only [← mul_add, newtonFrequencyKernel_split]

end OQ7Prescribed
