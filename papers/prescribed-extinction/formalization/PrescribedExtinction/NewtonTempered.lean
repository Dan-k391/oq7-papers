import PrescribedExtinction.NewtonContact
import PrescribedExtinction.VolumePotential
import Mathlib.Analysis.Fourier.LpSpace

/-! The actual singular Newton kernel as a tempered distribution. A local
L² part and a bounded exterior part give a continuous functional on Schwartz
space. This construction does not assume a Fourier transform formula. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped SchwartzMap ENNReal

def newtonExterior : Position → ℂ :=
  (Metric.closedBall (0 : Position) 1)ᶜ.indicator (outgoingGreen 0)

theorem newtonExterior_memLp : MemLp newtonExterior ∞ volume := by
  apply memLp_top_of_bound
    ((outgoingGreen_measurable 0).aestronglyMeasurable.indicator
      Metric.isClosed_closedBall.measurableSet.compl) ((4 * Real.pi)⁻¹)
  exact ae_of_all _ fun x => by
    change ‖newtonExterior x‖ ≤ (4 * Real.pi)⁻¹
    by_cases hx : x ∈ Metric.closedBall (0 : Position) 1
    · rw [newtonExterior, indicator_of_notMem (show x ∉ (Metric.closedBall (0 : Position) 1)ᶜ from not_not.mpr hx), norm_zero]
      positivity
    · have hn : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
      rw [newtonExterior, indicator_of_mem (show x ∈ (Metric.closedBall (0 : Position) 1)ᶜ from hx),
        outgoingGreen_norm]
      exact (inv_le_inv₀ (by positivity : 0 < 4 * Real.pi * ‖x‖)
        (by positivity : 0 < 4 * Real.pi)).mpr (by nlinarith [Real.pi_pos])

theorem newton_kernel_split (x : Position) :
    cutoffGreen 0 1 x + newtonExterior x = outgoingGreen 0 x := by
  classical
  by_cases hx : x ∈ Metric.closedBall (0 : Position) 1 <;>
    simp [cutoffGreen, newtonExterior, hx]

def newtonTempered : TemperedDistribution Position ℂ :=
  Lp.toTemperedDistribution ((cutoffGreen_memLp 0 1).toLp (cutoffGreen 0 1)) +
    Lp.toTemperedDistribution (newtonExterior_memLp.toLp newtonExterior)

theorem newton_schwartz_local_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun x => φ x * cutoffGreen 0 1 x) volume := by
  exact (φ.memLp 2 volume).integrable_mul (cutoffGreen_memLp 0 1)

theorem newton_schwartz_exterior_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun x => φ x * newtonExterior x) volume := by
  exact (φ.memLp 1 volume).integrable_mul newtonExterior_memLp

theorem newton_schwartz_integrable (φ : SchwartzMap Position ℂ) :
    Integrable (fun x => φ x * outgoingGreen 0 x) volume := by
  have h := (newton_schwartz_local_integrable φ).add (newton_schwartz_exterior_integrable φ)
  change Integrable (fun x => φ x * cutoffGreen 0 1 x + φ x * newtonExterior x) volume at h
  simpa only [← mul_add, newton_kernel_split] using h

theorem newtonTempered_apply (φ : SchwartzMap Position ℂ) :
    newtonTempered φ = ∫ x : Position, φ x * outgoingGreen 0 x := by
  change Lp.toTemperedDistribution ((cutoffGreen_memLp 0 1).toLp _) φ +
    Lp.toTemperedDistribution (newtonExterior_memLp.toLp _) φ = _
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
  have hlocal : (∫ x : Position, φ x * ((cutoffGreen_memLp 0 1).toLp _ : Position → ℂ) x) =
      ∫ x : Position, φ x * cutoffGreen 0 1 x := by
    apply integral_congr_ae
    filter_upwards [(cutoffGreen_memLp 0 1).coeFn_toLp] with x hx
    rw [hx]
  have hexterior : (∫ x : Position, φ x * (newtonExterior_memLp.toLp _ : Position → ℂ) x) =
      ∫ x : Position, φ x * newtonExterior x := by
    apply integral_congr_ae
    filter_upwards [newtonExterior_memLp.coeFn_toLp] with x hx
    rw [hx]
  rw [hlocal, hexterior, ← integral_add (newton_schwartz_local_integrable φ)
    (newton_schwartz_exterior_integrable φ)]
  simp only [← mul_add, newton_kernel_split]

end OQ7Prescribed
