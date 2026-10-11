import PrescribedExtinction.RadialEnergyCutoff
import PrescribedExtinction.RadiationEnergyBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

def sourceEnergyErrorConstant (k : ℝ) (p : CompactPolarization) (M : ℝ) : ℝ :=
  M * magneticDecayConstant k * radiationKernelConstant k p.radius *
    (∫ y : Position, ‖p.current y‖) ^ 2

theorem sourceEnergyErrorConstant_nonneg (k : ℝ) (p : CompactPolarization) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ sourceEnergyErrorConstant k p M := by
  have hR := p.radius_nonneg
  unfold sourceEnergyErrorConstant magneticDecayConstant radiationKernelConstant
  positivity

theorem weighted_source_flux_lower_bound_ae (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (M : ℝ) (hM : 0 ≤ M)
    (hMb : ∀ s : ℝ, transitionDerivative s ≤ M) (r : ℝ) (hr : 0 < r)
    (hfar : 2 * p.radius + 2 ≤ r) :
    ∀ᵐ x ∂volume, -(sourceEnergyErrorConstant k p M / r ^ 4) ≤
      sourceEnergyWeight r x * (pairing (smoothElectricSource k p x)
        (cross (smoothMagneticSource k p x) (complexify (radialDirection x)))).re := by
  have hR := p.radius_nonneg
  have hA : 0 ≤ magneticDecayConstant k := by unfold magneticDecayConstant; positivity
  have hD : 0 ≤ radiationKernelConstant k p.radius := by unfold radiationKernelConstant; positivity
  have hN : 0 ≤ ∫ y : Position, ‖p.current y‖ := integral_nonneg (fun y => norm_nonneg (p.current y))
  have hC : 0 ≤ sourceEnergyErrorConstant k p M := sourceEnergyErrorConstant_nonneg k p M hM
  filter_upwards [smoothPhysicalSource_flux_lower_bound_ae k p hp] with x hx
  by_cases hinner : ‖x‖ ≤ r
  · rw [sourceEnergyWeight_zero_inner r hr x hinner, zero_mul]
    exact neg_nonpos.mpr (div_nonneg hC (pow_nonneg hr.le 4))
  have hs : 0 < ‖x‖ := hr.trans (lt_of_not_ge hinner)
  have hsr : r ≤ ‖x‖ := (lt_of_not_ge hinner).le
  have hf := hx (hfar.trans hsr)
  have hw := sourceEnergyWeight_nonneg r hr x
  have hwm := sourceEnergyWeight_le r M hr hMb x
  let B := magneticDecayConstant k * radiationKernelConstant k p.radius *
    (∫ y : Position, ‖p.current y‖) ^ 2
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hA hD) (sq_nonneg _)
  have hprod : (magneticDecayConstant k / ‖x‖ * ∫ y : Position, ‖p.current y‖) *
      (radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖) = B / ‖x‖ ^ 3 := by
    dsimp [B]
    field_simp
  rw [hprod] at hf
  have hfrac : B / ‖x‖ ^ 3 ≤ B / r ^ 3 :=
    div_le_div_of_nonneg_left hB (pow_pos hr 3) (pow_le_pow_left₀ hr.le hsr 3)
  have herr := mul_le_mul hwm hfrac (div_nonneg hB (pow_nonneg hs.le 3)) (div_nonneg hM hr.le)
  have heq : (M / r) * (B / r ^ 3) = sourceEnergyErrorConstant k p M / r ^ 4 := by
    dsimp [B, sourceEnergyErrorConstant]
    field_simp
  rw [heq] at herr
  have hmul := mul_le_mul_of_nonneg_left hf hw
  nlinarith

theorem integral_compact_ball_lower_bound (f : Position → ℝ) (hf : Integrable f volume)
    (r C : ℝ) (hr : 0 < r)
    (hz : ∀ x : Position, 2 * r < ‖x‖ → f x = 0)
    (hb : ∀ᵐ x ∂volume, -(C / r ^ 4) ≤ f x) :
    -((32 * Real.pi / 3) * C / r) ≤ ∫ x : Position, f x := by
  let K := Metric.closedBall (0 : Position) (2 * r)
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hg : Integrable (K.indicator (fun _ : Position => -(C / r ^ 4))) volume :=
    (integrable_indicator_iff hK).mpr
      (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
  have hle : ∫ x : Position, K.indicator (fun _ : Position => -(C / r ^ 4)) x ≤ ∫ x : Position, f x := by
    apply integral_mono_ae hg hf
    filter_upwards [hb] with x hx
    by_cases hk : x ∈ K
    · simpa [indicator_of_mem hk] using hx
    · have hn : 2 * r < ‖x‖ := by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hk
      simp [indicator_of_notMem hk, hz x hn]
  rw [integral_indicator hK, setIntegral_const] at hle
  have hm : volume.real K = (2 * r) ^ 3 * (Real.pi * 4 / 3) := by
    rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  change volume.real K * (-(C / r ^ 4)) ≤ _ at hle
  rw [hm] at hle
  have heq : ((2 * r) ^ 3 * (Real.pi * 4 / 3)) * (-(C / r ^ 4)) =
      -((32 * Real.pi / 3) * C / r) := by field_simp; ring
  rwa [heq] at hle

theorem smoothPhysicalSource_work_lower_bound (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (M : ℝ) (hM : 0 ≤ M)
    (hMb : ∀ s : ℝ, transitionDerivative s ≤ M) (r : ℝ) (hr : 0 < r)
    (hfar : 2 * p.radius + 2 ≤ r) :
    -((32 * Real.pi / 3) * sourceEnergyErrorConstant k p M / r) ≤
      k * (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im := by
  rw [smoothPhysicalSource_radial_energy k p hp r hr (by linarith [p.radius_nonneg])]
  apply integral_compact_ball_lower_bound _ (smoothPhysicalSource_radial_flux_integrable k p hp r hr)
    r _ hr
  · intro x hx
    rw [sourceEnergyWeight_zero_outer r hr x hx.le, zero_mul]
  · exact weighted_source_flux_lower_bound_ae k p hp M hM hMb r hr hfar

theorem smoothPhysicalSource_work_nonneg (k : ℝ) (hk : 0 < k) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    0 ≤ (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im := by
  obtain ⟨M, hM, hMb⟩ := transitionDerivative_global_bound
  have hbound (s : ℝ) : transitionDerivative s ≤ M :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMb s)
  have ht : Tendsto (fun r : ℝ => -((32 * Real.pi / 3) * sourceEnergyErrorConstant k p M / r))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (-((32 * Real.pi / 3) * sourceEnergyErrorConstant k p M))
  have hevent : ∀ᶠ r : ℝ in atTop,
      -((32 * Real.pi / 3) * sourceEnergyErrorConstant k p M / r) ≤
        k * (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im := by
    filter_upwards [eventually_ge_atTop (2 * p.radius + 2)] with r hr
    exact smoothPhysicalSource_work_lower_bound k p hp M hM hbound r (by linarith [p.radius_nonneg]) hr
  have hnon : 0 ≤ k * (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im :=
    le_of_tendsto ht hevent
  exact (mul_nonneg_iff_of_pos_left hk).mp hnon

end OQ7Prescribed
