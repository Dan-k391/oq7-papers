import work.ExteriorSphereContinuity
import PrescribedExtinction.FarFieldFlux
import PrescribedExtinction.FarFieldRadial

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Filter Set
open scoped Topology

/-- Impedance-normalized physical outward flux on the actual sphere of
radius r, divided by the common incident intensity. -/
def exteriorSphereFlux (k : ℝ) (p : CompactPolarization) (r : ℝ) : ℝ :=
  ∫ n : UnitSphere, r ^ 2 * (pairing (exteriorElectric k p (r • (n : Position)))
    (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re ∂sphereArea

theorem exteriorSphereFlux_integrable (k : ℝ) (p : CompactPolarization)
    (r : ℝ) (hr : 2 * p.radius + 2 ≤ r) :
    Integrable (fun n : UnitSphere => r ^ 2 * (pairing (exteriorElectric k p (r • (n : Position)))
      (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re) sphereArea := by
  have hE := exteriorElectric_sphere_continuous k p r hr
  have hH := exteriorMagnetic_sphere_continuous k p r hr
  have hC : Continuous (fun n : UnitSphere =>
      cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position))) := by
    unfold cross
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
    apply continuous_pi
    intro i
    have hh (j : Fin 3) := (vectorCoordinate j).continuous.comp hH
    have hn (j : Fin 3) : Continuous (fun n : UnitSphere => complexify (n : Position) j) :=
      (vectorCoordinate j).continuous.comp (complexify_continuous.comp continuous_subtype_val)
    fin_cases i
    · exact ((hh 1).mul (hn 2)).sub ((hh 2).mul (hn 1))
    · exact ((hh 2).mul (hn 0)).sub ((hh 0).mul (hn 2))
    · exact ((hh 0).mul (hn 1)).sub ((hh 1).mul (hn 0))
  have hp : Continuous (fun n : UnitSphere => r ^ 2 *
      (pairing (exteriorElectric k p (r • (n : Position)))
        (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re) := by
    have hreal : Continuous (fun n : UnitSphere =>
        (inner ℂ (exteriorElectric k p (r • (n : Position)))
          (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re) :=
      Complex.continuous_re.comp (hE.inner hC)
    simpa only [pairing_eq_inner] using hreal.const_mul (r ^ 2)
  exact hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem exteriorSphereFlux_farField_error (k : ℝ) (p : CompactPolarization)
    (r : ℝ) (hr : 2 * p.radius + 2 ≤ r) :
    |exteriorSphereFlux k p r - (∫ n : UnitSphere, ‖compactCurrentFarField k p n‖ ^ 2 ∂sphereArea)| ≤
      4 * Real.pi * (farFieldFluxConstant k p.radius / r * (∫ y : Position, ‖p.current y‖) ^ 2) := by
  have hrpos : 0 < r := by linarith [p.radius_nonneg]
  have hnorm (n : UnitSphere) : ‖r • (n : Position)‖ = r := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, unitSphere_norm]
  have hCF : Continuous (fun n : UnitSphere => ‖compactCurrentFarField k p n‖ ^ 2) :=
    (((compactCurrentFarField_continuous k p).comp continuous_subtype_val).norm.pow 2)
  have hF : Integrable (fun n : UnitSphere => ‖compactCurrentFarField k p n‖ ^ 2) sphereArea :=
    hCF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold exteriorSphereFlux
  rw [← integral_sub (exteriorSphereFlux_integrable k p r hr) hF]
  have hb : ∀ n : UnitSphere,
      |r ^ 2 * (pairing (exteriorElectric k p (r • (n : Position)))
        (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re -
          ‖compactCurrentFarField k p n‖ ^ 2| ≤
        farFieldFluxConstant k p.radius / r * (∫ y : Position, ‖p.current y‖) ^ 2 := by
    intro n
    have h := exterior_poynting_farField_error k p (r • (n : Position)) (by rw [hnorm]; exact hr)
    rw [hnorm, radialDirection_positive_smul r hrpos n] at h
    exact h
  let d : UnitSphere → ℝ := fun n => r ^ 2 * (pairing (exteriorElectric k p (r • (n : Position)))
    (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re - ‖compactCurrentFarField k p n‖ ^ 2
  have h : ‖∫ n : UnitSphere, d n ∂sphereArea‖ ≤
      ∫ _ : UnitSphere, farFieldFluxConstant k p.radius / r * (∫ y : Position, ‖p.current y‖) ^ 2 ∂sphereArea := by
    apply norm_integral_le_of_norm_le (integrable_const _)
    exact ae_of_all _ fun n => by simpa only [d, Real.norm_eq_abs] using hb n
  simpa only [d, Real.norm_eq_abs, integral_const, smul_eq_mul, sphereArea_real_univ] using h

/-- The actual all-angle outward Poynting power converges to the full
sphere-area squared far-field integral, with every radius sufficiently large. -/
theorem exteriorSphereFlux_tendsto (k : ℝ) (p : CompactPolarization) :
    Tendsto (exteriorSphereFlux k p) atTop
      (𝓝 (∫ n : UnitSphere, ‖compactCurrentFarField k p n‖ ^ 2 ∂sphereArea)) := by
  have ht : Tendsto (fun r : ℝ =>
      4 * Real.pi * (farFieldFluxConstant k p.radius / r * (∫ y : Position, ‖p.current y‖) ^ 2)) atTop (𝓝 0) := by
    have he : (fun r : ℝ => 4 * Real.pi * (farFieldFluxConstant k p.radius / r * (∫ y : Position, ‖p.current y‖) ^ 2)) =
        fun r => (4 * Real.pi * farFieldFluxConstant k p.radius * (∫ y : Position, ‖p.current y‖) ^ 2) * r⁻¹ := by
      funext r; ring
    rw [he]
    simpa only [mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
      (4 * Real.pi * farFieldFluxConstant k p.radius * (∫ y : Position, ‖p.current y‖) ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun r => norm_nonneg _))
    (eventually_ge_atTop (2 * p.radius + 2) |>.mono ?_) ht
  intro r hr
  simpa only [Real.norm_eq_abs] using exteriorSphereFlux_farField_error k p r hr

end OQ7Prescribed
