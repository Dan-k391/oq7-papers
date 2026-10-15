import PrescribedExtinction.SlabGreen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem slabPolar_integrable (f : ℂ → ℂ) (hm : Measurable f) (hi : Integrable f volume) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      polarCoord.target volume := by
  refine ⟨?_, ?_⟩
  · have hcp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    exact (measurable_fst.smul (hm.comp hcp.measurable)).aestronglyMeasurable.restrict
  · rw [hasFiniteIntegral_iff_norm]
    have he := Complex.lintegral_comp_polarCoord_symm (fun y => ENNReal.ofReal ‖f y‖)
    have hh : (∫⁻ p : ℝ × ℝ in polarCoord.target,
        ENNReal.ofReal ‖p.1 • f (Complex.polarCoord.symm p)‖) =
        ∫⁻ y : ℂ, ENNReal.ofReal ‖f y‖ := by
      rw [← he]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
      have hp0 : 0 < p.1 := hp.1
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hp0,
        ENNReal.ofReal_mul hp0.le, smul_eq_mul]
    rw [hh]
    exact (hasFiniteIntegral_iff_norm f (μ := volume)).mp hi.hasFiniteIntegral

theorem slabPolar_symm (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [circleMap, zero_add]
  rw [Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

end OQ7Prescribed
