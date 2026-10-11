import PrescribedExtinction.SphericalProduct

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

theorem sphereDirection_continuous : Continuous (fun p : ℝ × ℝ => sphereDirection p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [sphereDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] <;> fun_prop

theorem sphereDirection_norm (θ φ : ℝ) : ‖sphereDirection θ φ‖ = 1 := by
  nlinarith [sphereDirection_unit θ φ, norm_nonneg (sphereDirection θ φ)]

theorem sphericalPoint_radialDirection (p : Fin 3 → ℝ) (hp : 0 < p 0) :
    radialDirection (WithLp.toLp 2 (sphericalPoint p)) = sphereDirection (p 1) (p 2) := by
  rw [sphericalPoint_toLp]
  exact radialDirection_positive_smul (p 0) hp
    ⟨sphereDirection (p 1) (p 2), by simpa [UnitSphere] using sphereDirection_norm (p 1) (p 2)⟩

theorem sphericalPoint_weighted_jacobian (p : Fin 3 → ℝ) (hp : p ∈ sphericalDomain)
    (A : Position → ℝ) :
    (p 0)^2 * Real.sin (p 1) *
      (sourceEnergyWeight 1 (WithLp.toLp 2 (sphericalPoint p)) /
        ‖WithLp.toLp 2 (sphericalPoint p)‖^2 * A (radialDirection (WithLp.toLp 2 (sphericalPoint p)))) =
      transitionDerivative (p 0 - 1) * (Real.sin (p 1) * A (sphereDirection (p 1) (p 2))) := by
  rw [sphericalPoint_radialDirection p hp.1]
  simp only [sourceEnergyWeight, sphericalPoint_norm, abs_of_pos hp.1, div_one]
  field_simp [hp.1.ne']

theorem transitionDerivative_radial_unit_mass :
    (∫ r in Ioi (0 : ℝ), transitionDerivative (r - 1)) = 1 := by
  have h := transition_radial_integral 1 1 (by norm_num) (by norm_num) (fun _ => 1)
  simp only [div_one, mul_one] at h
  rw [h]
  have hs := transition_radial_rescale 1 1 (by norm_num) (fun _ => 1)
  simpa only [div_one, mul_one, one_mul, inv_one, transitionDerivative_integral] using hs

theorem sphereArea_integral_angular_product (A : Position → ℝ) :
    (∫ n : UnitSphere, A n ∂sphereArea) =
      ∫ p in Ioo (0 : ℝ) Real.pi ×ˢ Ioo (-Real.pi) Real.pi,
        Real.sin p.1 * A (sphereDirection p.1 p.2) := by
  rw [← sourceEnergyWeight_direction_integral 1 (by norm_num) A, integral_spherical_actual]
  have he : (∫ p in sphericalDomain, (p 0)^2 * Real.sin (p 1) *
      (sourceEnergyWeight 1 (WithLp.toLp 2 (sphericalPoint p)) /
        ‖WithLp.toLp 2 (sphericalPoint p)‖^2 * A (radialDirection (WithLp.toLp 2 (sphericalPoint p))))) =
      ∫ p in sphericalDomain,
        transitionDerivative (p 0 - 1) * (Real.sin (p 1) * A (sphereDirection (p 1) (p 2))) :=
    setIntegral_congr_fun sphericalDomain_measurableSet (fun p hp => sphericalPoint_weighted_jacobian p hp A)
  rw [he, sphericalDomain_product_integral (fun p : ℝ × (ℝ × ℝ) =>
    transitionDerivative (p.1 - 1) * (Real.sin p.2.1 * A (sphereDirection p.2.1 p.2.2)))]
  rw [show (volume : Measure (ℝ × (ℝ × ℝ))) = volume.prod volume from Measure.volume_eq_prod _ _]
  rw [setIntegral_prod_mul (fun r : ℝ => transitionDerivative (r - 1))
    (fun p : ℝ × ℝ => Real.sin p.1 * A (sphereDirection p.1 p.2)),
    transitionDerivative_radial_unit_mass, one_mul]

theorem sphereArea_integral_angular_centered (A : Position → ℝ) (hA : Continuous A) :
    (∫ n : UnitSphere, A n ∂sphereArea) =
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (-Real.pi)..Real.pi,
        Real.sin θ * A (sphereDirection θ φ) := by
  rw [sphereArea_integral_angular_product]
  have hc : Continuous (fun p : ℝ × ℝ => Real.sin p.1 * A (sphereDirection p.1 p.2)) :=
    (Real.continuous_sin.comp continuous_fst).mul (hA.comp sphereDirection_continuous)
  have hi : IntegrableOn (fun p : ℝ × ℝ => Real.sin p.1 * A (sphereDirection p.1 p.2))
      (Ioo 0 Real.pi ×ˢ Ioo (-Real.pi) Real.pi) volume :=
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod _ _,
    setIntegral_prod _ hi]
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  dsimp only
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem sphereDirection_periodic (θ : ℝ) : Function.Periodic (sphereDirection θ) (2 * Real.pi) := by
  intro φ
  ext i
  fin_cases i <;> simp [sphereDirection, Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem sphereArea_integral_original_angles (A : Position → ℝ) (hA : Continuous A) :
    (∫ n : UnitSphere, A n ∂sphereArea) =
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        A (sphereDirection θ φ) * Real.sin θ := by
  rw [sphereArea_integral_angular_centered A hA]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hp : Function.Periodic (fun φ => Real.sin θ * A (sphereDirection θ φ)) (2 * Real.pi) := by
    intro φ
    dsimp only
    rw [sphereDirection_periodic θ φ]
  have he := hp.intervalIntegral_add_eq (-Real.pi) 0
  simp only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro φ _
  ring

end OQ7Prescribed
