import PrescribedExtinction.PlanarScalarPotential
import PrescribedExtinction.HeightL1Bound

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Convolution ENNReal

theorem scalarPlanarPotential_integrand_integrable (k : ℝ) (hk : 0 < k)
    (q : ℝ → ℂ) (hq : Integrable q volume) (z : ℝ) :
    Integrable (fun t : ℝ => planarScalarGreen k (z - t) * q t) volume := by
  have hc : Continuous (fun t : ℝ => planarScalarGreen k (z - t)) :=
    (planarScalarGreen_continuous k).comp (continuous_const.sub continuous_id)
  exact hq.bdd_mul (c := 1 / (2 * k)) hc.aestronglyMeasurable
    (ae_of_all _ fun t => (planarScalarGreen_norm k (z - t) hk).le)

theorem scalarPlanarPotential_norm_bound (k : ℝ) (hk : 0 < k)
    (q : ℝ → ℂ) (hq : Integrable q volume) (z : ℝ) :
    ‖scalarPlanarPotential k q z‖ ≤ (1 / (2 * k)) * ∫ t : ℝ, ‖q t‖ := by
  have hm : Integrable (fun t : ℝ => (1 / (2 * k)) * ‖q t‖) volume := hq.norm.const_mul _
  have he := norm_integral_le_of_norm_le hm (ae_of_all _ fun t => by
    change ‖planarScalarGreen k (z - t) * q t‖ ≤ _
    rw [norm_mul, planarScalarGreen_norm k (z - t) hk])
  rw [integral_const_mul] at he
  exact he

theorem scalarPlanarPotential_continuous_integrable (k : ℝ) (hk : 0 < k)
    (q : ℝ → ℂ) (hq : Integrable q volume) : Continuous (scalarPlanarPotential k q) := by
  have hb : BddAbove (range fun s : ℝ => ‖planarScalarGreen k s‖) := by
    refine ⟨1 / (2 * k), ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (planarScalarGreen_norm k s hk).le
  rw [scalarPlanarPotential_convolution]
  exact hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℂ) hq
    (planarScalarGreen_continuous k)

theorem scalarPlanarPotential_height_memLp (k : ℝ) (hk : 0 < k)
    (q : ℝ → ℂ) (hq : Integrable q volume) (L : ℝ) :
    MemLp ((Icc 0 L).indicator (scalarPlanarPotential k q)) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  have hf : AEStronglyMeasurable (scalarPlanarPotential k q) (volume.restrict (Icc 0 L)) :=
    (scalarPlanarPotential_continuous_integrable k hk q hq).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  apply MemLp.of_bound hf ((1 / (2 * k)) * ∫ t : ℝ, ‖q t‖)
  exact ae_of_all _ fun z => scalarPlanarPotential_norm_bound k hk q hq z

theorem scalarPlanarPotential_height_norm_bound (k : ℝ) (hk : 0 < k)
    (q : ℝ → ℂ) (hq : Integrable q volume) (L : ℝ) (hL : 0 ≤ L) :
    ‖(scalarPlanarPotential_height_memLp k hk q hq L).toLp
      ((Icc 0 L).indicator (scalarPlanarPotential k q))‖ ≤
        Real.sqrt L * (1 / (2 * k)) * ∫ t : ℝ, ‖q t‖ := by
  let C := (1 / (2 * k)) * ∫ t : ℝ, ‖q t‖
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))
  have hf : AEStronglyMeasurable (scalarPlanarPotential k q) (volume.restrict (Icc 0 L)) :=
    (scalarPlanarPotential_continuous_integrable k hk q hq).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have he := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hf
    (ae_of_all _ fun z => scalarPlanarPotential_norm_bound k hk q hq z)
  have ht : (volume.restrict (Icc 0 L)) univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simp)).ne ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono ht he
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hL, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofNat] at hr
  simpa only [Real.sqrt_eq_rpow, one_div, C, mul_assoc] using hr

end OQ7Prescribed
