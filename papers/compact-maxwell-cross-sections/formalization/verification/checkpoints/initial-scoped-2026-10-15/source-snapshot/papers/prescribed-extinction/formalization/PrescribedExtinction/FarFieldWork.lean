import PrescribedExtinction.FarFieldFlux
import PrescribedExtinction.FarFieldRadial
import PrescribedExtinction.SmoothOutgoingDissipativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

theorem integral_compact_ball_abs_bound (f : Position → ℝ) (hf : Integrable f volume)
    (r C : ℝ) (hr : 0 < r)
    (hz : ∀ x : Position, 2 * r < ‖x‖ → f x = 0)
    (hb : ∀ᵐ x ∂volume, |f x| ≤ C / r ^ 4) :
    |∫ x : Position, f x| ≤ (32 * Real.pi / 3) * C / r := by
  have hlo := integral_compact_ball_lower_bound f hf r C hr hz (hb.mono fun _ hx => (abs_le.mp hx).1)
  have hup := integral_compact_ball_lower_bound (-f) hf.neg r C hr
    (fun x hx => by simp [hz x hx]) (hb.mono fun _ hx => by
      change -(C / r ^ 4) ≤ -f _
      linarith [(abs_le.mp hx).2])
  simp only [Pi.neg_apply, integral_neg] at hup
  exact abs_le.mpr ⟨hlo, by linarith⟩

def farFieldWorkErrorConstant (k : ℝ) (p : CompactPolarization) (M : ℝ) : ℝ :=
  M * farFieldFluxConstant k p.radius * (∫ y : Position, ‖p.current y‖) ^ 2

theorem smoothPhysicalSource_weighted_farField_error (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (M : ℝ) (hM : 0 ≤ M)
    (hMb : ∀ s : ℝ, transitionDerivative s ≤ M) (r : ℝ) (hr : 0 < r)
    (hfar : 2 * p.radius + 2 ≤ r) :
    ∀ᵐ x ∂volume,
      |sourceEnergyWeight r x * (pairing (smoothElectricSource k p x)
        (cross (smoothMagneticSource k p x) (complexify (radialDirection x)))).re -
        sourceEnergyWeight r x / ‖x‖ ^ 2 * ‖compactCurrentFarField k p (radialDirection x)‖ ^ 2| ≤
          farFieldWorkErrorConstant k p M / r ^ 4 := by
  have hR := p.radius_nonneg
  have hC : 0 ≤ farFieldFluxConstant k p.radius := by
    unfold farFieldFluxConstant farFieldKernelConstant farFieldLowerConstant radiationKernelConstant
    positivity
  have hN : 0 ≤ (∫ y : Position, ‖p.current y‖) ^ 2 := sq_nonneg _
  have hex : ∀ᵐ x ∂volume, x ∈ currentExterior p → exteriorElectric k p x = electricVolumeField k p x :=
    (ae_restrict_iff' (currentExterior p).isOpen.measurableSet).mp (electricExterior_eq_ae k p)
  filter_upwards [hex, smoothElectricSource_eq_ae k p hp, smoothMagneticSource_eq_ae k p hp]
    with x hx he hm
  by_cases hinner : ‖x‖ ≤ r
  · rw [sourceEnergyWeight_zero_inner r hr x hinner, zero_mul, zero_div, zero_mul, sub_self, abs_zero]
    unfold farFieldWorkErrorConstant
    positivity
  have hs : 0 < ‖x‖ := hr.trans (lt_of_not_ge hinner)
  have hsr : r ≤ ‖x‖ := (lt_of_not_ge hinner).le
  have hxs : x ∈ currentExterior p := by change p.radius + 1 < ‖x‖; linarith
  rw [he, hm, ← hx hxs, ← magneticExterior_eq_pointwise_far k p x (by linarith)]
  have heq : sourceEnergyWeight r x * (pairing (exteriorElectric k p x)
      (cross (exteriorMagnetic k p x) (complexify (radialDirection x)))).re -
        sourceEnergyWeight r x / ‖x‖ ^ 2 * ‖compactCurrentFarField k p (radialDirection x)‖ ^ 2 =
      (sourceEnergyWeight r x / ‖x‖ ^ 2) * (‖x‖ ^ 2 * (pairing (exteriorElectric k p x)
        (cross (exteriorMagnetic k p x) (complexify (radialDirection x)))).re -
          ‖compactCurrentFarField k p (radialDirection x)‖ ^ 2) := by field_simp
  rw [heq, abs_mul, abs_of_nonneg (div_nonneg (sourceEnergyWeight_nonneg r hr x) (sq_nonneg _))]
  have hb := exterior_poynting_farField_error k p x (hfar.trans hsr)
  have hw := sourceEnergyWeight_le r M hr hMb x
  calc
    _ ≤ ((M / r) / ‖x‖ ^ 2) *
        (farFieldFluxConstant k p.radius / ‖x‖ * (∫ y : Position, ‖p.current y‖) ^ 2) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hw (sq_nonneg _)) hb (abs_nonneg _)
        (div_nonneg (div_nonneg hM hr.le) (sq_nonneg _))
    _ = farFieldWorkErrorConstant k p M / r / ‖x‖ ^ 3 := by unfold farFieldWorkErrorConstant; ring
    _ ≤ farFieldWorkErrorConstant k p M / r / r ^ 3 := by
      apply div_le_div_of_nonneg_left (div_nonneg (mul_nonneg (mul_nonneg hM hC) hN) hr.le)
        (pow_pos hr 3) (pow_le_pow_left₀ hr.le hsr 3)
    _ = _ := by ring

theorem smoothPhysicalSource_farField_work_error (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (M : ℝ) (hM : 0 ≤ M)
    (hMb : ∀ s : ℝ, transitionDerivative s ≤ M) (r : ℝ) (hr : 0 < r)
    (hfar : 2 * p.radius + 2 ≤ r) :
    |k * (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im -
      ∫ n : UnitSphere, ‖compactCurrentFarField k p n‖ ^ 2 ∂sphereArea| ≤
        (32 * Real.pi / 3) * farFieldWorkErrorConstant k p M / r := by
  let A : Position → ℝ := fun n => ‖compactCurrentFarField k p n‖ ^ 2
  have hA : Continuous A := (compactCurrentFarField_continuous k p).norm.pow 2
  have hf := smoothPhysicalSource_radial_flux_integrable k p hp r hr
  have hg := sourceEnergyWeight_direction_integrable r hr A hA
  rw [smoothPhysicalSource_radial_energy k p hp r hr (by linarith [p.radius_nonneg]),
    ← sourceEnergyWeight_direction_integral r hr A, ← integral_sub hf hg]
  apply integral_compact_ball_abs_bound _ (hf.sub hg) r _ hr
  · intro x hx
    change sourceEnergyWeight r x * _ - sourceEnergyWeight r x / ‖x‖ ^ 2 * A (radialDirection x) = 0
    rw [sourceEnergyWeight_zero_outer r hr x hx.le, zero_mul, zero_div, zero_mul, sub_self]
  · exact smoothPhysicalSource_weighted_farField_error k p hp M hM hMb r hr hfar

/-- Exact radiation/work identity with the genuine Haar surface measure.
Conversion to the original theta/phi scattering integral remains separate. -/
theorem smoothPhysicalSource_farField_work (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) :
    k * (∫ x : Position, pairing (p.current x) (electricVolumeField k p x)).im =
      ∫ n : UnitSphere, ‖compactCurrentFarField k p n‖ ^ 2 ∂sphereArea := by
  have heq : (∫ x : Position, pairing (p.current x) (electricVolumeField k p x)) =
      ∫ x : Position, pairing (p.current x) (smoothElectricSource k p x) := by
    apply integral_congr_ae
    filter_upwards [smoothElectricSource_eq_ae k p hp] with x hx
    rw [hx]
  rw [heq]
  obtain ⟨M, hM, hMb⟩ := transitionDerivative_global_bound
  have hbound (s : ℝ) : transitionDerivative s ≤ M :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMb s)
  have ht : Tendsto (fun r : ℝ => (32 * Real.pi / 3) * farFieldWorkErrorConstant k p M / r)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((32 * Real.pi / 3) * farFieldWorkErrorConstant k p M)
  have hevent : ∀ᶠ r : ℝ in atTop,
      |k * (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im -
        ∫ n : UnitSphere, ‖compactCurrentFarField k p n‖ ^ 2 ∂sphereArea| ≤
          (32 * Real.pi / 3) * farFieldWorkErrorConstant k p M / r := by
    filter_upwards [eventually_ge_atTop (2 * p.radius + 2)] with r hr
    exact smoothPhysicalSource_farField_work_error k p hp M hM hbound r (by linarith [p.radius_nonneg]) hr
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (ge_of_tendsto ht hevent) (abs_nonneg _)))

end OQ7Prescribed
