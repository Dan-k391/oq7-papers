import PrescribedExtinction.FarFieldCurrent
import PrescribedExtinction.RadialEnergyCutoff

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Topology

theorem radialDirection_positive_smul (s : ℝ) (hs : 0 < s) (n : UnitSphere) :
    radialDirection (s • (n : Position)) = (n : Position) := by
  simp [radialDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hs, unitSphere_norm,
    smul_smul, hs.ne']

theorem sourceEnergyWeight_direction_integral (r : ℝ) (hr : 0 < r) (A : Position → ℝ) :
    (∫ x : Position, sourceEnergyWeight r x / ‖x‖ ^ 2 * A (radialDirection x)) =
      ∫ n : UnitSphere, A n ∂sphereArea := by
  rw [integral_polar_actual]
  have he : (fun p : UnitSphere × Ioi (0 : ℝ) =>
      sourceEnergyWeight r (p.2.1 • (p.1 : Position)) / ‖p.2.1 • (p.1 : Position)‖ ^ 2 *
        A (radialDirection (p.2.1 • (p.1 : Position)))) =
      (fun p => A p.1 * (transitionDerivative ((p.2.1 - r) / r) / r / p.2.1 ^ 2)) := by
    funext p
    rw [radialDirection_positive_smul p.2.1 p.2.2 p.1]
    simp only [sourceEnergyWeight, norm_smul, Real.norm_eq_abs, abs_of_pos (mem_Ioi.mp p.2.2), unitSphere_norm, mul_one]
    ring
  rw [he]
  rw [integral_prod_mul (μ := sphereArea) (ν := Measure.volumeIoiPow 2)
    (fun n : UnitSphere => A n)
    (fun s : Ioi (0 : ℝ) => transitionDerivative ((s.1 - r) / r) / r / s.1 ^ 2)]
  have hi : (∫ s : Ioi (0 : ℝ), transitionDerivative ((s.1 - r) / r) / r / s.1 ^ 2
      ∂Measure.volumeIoiPow 2) = 1 := by
    unfold Measure.volumeIoiPow
    simp only [ENNReal.ofReal]
    rw [integral_withDensity_eq_integral_smul (measurable_subtype_coe.pow_const 2 |>.real_toNNReal)]
    have hfun : (fun s : Ioi (0 : ℝ) => Real.toNNReal (s.1 ^ 2) •
        (transitionDerivative ((s.1 - r) / r) / r / s.1 ^ 2)) =
        (fun s => transitionDerivative ((s.1 - r) / r) / r) := by
      funext s
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg s.1), smul_eq_mul]
      field_simp [(mem_Ioi.mp s.2).ne']
    rw [hfun, integral_subtype_comap measurableSet_Ioi (fun s : ℝ => transitionDerivative ((s - r) / r) / r),
      show (fun s : ℝ => transitionDerivative ((s - r) / r) / r) =
        (fun s => transitionDerivative ((s - r) / r) * (1 / r)) by funext s; ring]
    rw [transition_radial_integral r r hr hr (fun _ => 1 / r), intervalIntegral.integral_mul_const]
    have hscale := transition_radial_rescale r r hr (fun _ => 1)
    simp only [mul_one, transitionDerivative_integral] at hscale
    rw [mul_comm]
    simpa only [one_div] using hscale
  rw [hi, mul_one]

theorem sourceEnergyWeight_direction_continuous (r : ℝ) (hr : 0 < r)
    (A : Position → ℝ) (hA : Continuous A) :
    Continuous (fun x : Position => sourceEnergyWeight r x / ‖x‖ ^ 2 * A (radialDirection x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : (fun y : Position => sourceEnergyWeight r y / ‖y‖ ^ 2 * A (radialDirection y)) =ᶠ[𝓝 (0 : Position)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hr)] with y hy
      rw [sourceEnergyWeight_zero_inner r hr y hy.le, zero_div, zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he
  · have hn := norm_ne_zero_iff.mpr hx
    have hc : ContinuousAt radialDirection x := by
      unfold radialDirection
      exact (continuous_norm.continuousAt.inv₀ hn).smul continuousAt_id
    exact (((sourceEnergyWeight_continuous r).continuousAt.div (continuous_norm.continuousAt.pow 2)
      (pow_ne_zero 2 hn)).mul (hA.continuousAt.comp hc))

theorem sourceEnergyWeight_direction_integrable (r : ℝ) (hr : 0 < r)
    (A : Position → ℝ) (hA : Continuous A) :
    Integrable (fun x : Position => sourceEnergyWeight r x / ‖x‖ ^ 2 * A (radialDirection x)) volume := by
  have hc := sourceEnergyWeight_direction_continuous r hr A hA
  have hs : HasCompactSupport (fun x : Position => sourceEnergyWeight r x / ‖x‖ ^ 2 * A (radialDirection x)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) (2 * r))
    intro x hx
    have hn : 2 * r ≤ ‖x‖ := (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).le
    rw [sourceEnergyWeight_zero_outer r hr x hn, zero_div, zero_mul]
  exact hc.integrable_of_hasCompactSupport hs

end OQ7Prescribed
