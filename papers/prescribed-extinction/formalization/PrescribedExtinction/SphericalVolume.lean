import PrescribedExtinction.SphericalDomain

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

theorem sphericalDomain_measurableSet : MeasurableSet sphericalDomain := by
  unfold sphericalDomain
  measurability

theorem sphericalPoint_image_ae_eq_univ : sphericalPoint '' sphericalDomain =ᵐ[volume] univ := by
  have hs : (sphericalPoint '' sphericalDomain)ᶜ ⊆ LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) := by
    intro x hx
    change x 1 = 0
    by_contra hn
    exact hx (sphericalPoint_image_of_second_ne_zero x hn)
  have hm : volume (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) : Set (Fin 3 → ℝ)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have he := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => f ![0, 1, 0]) h
    simp at he
  rw [ae_eq_univ]
  exact le_antisymm ((measure_mono hs).trans (le_of_eq hm)) bot_le

theorem integral_spherical_actual (f : Position → ℝ) :
    (∫ x : Position, f x) = ∫ p in sphericalDomain,
      (p 0) ^ 2 * Real.sin (p 1) * f (WithLp.toLp 2 (sphericalPoint p)) := by
  have hv := (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding f
  rw [← hv]
  rw [← setIntegral_univ]
  rw [← setIntegral_congr_set sphericalPoint_image_ae_eq_univ]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume sphericalDomain_measurableSet
    (fun p _ => (sphericalPoint_hasFDerivAt p).hasFDerivWithinAt) sphericalPoint_injOn]
  apply setIntegral_congr_fun sphericalDomain_measurableSet
  intro p hp
  change |(sphericalDerivative p).det| * f (WithLp.toLp 2 (sphericalPoint p)) =
    (p 0) ^ 2 * Real.sin (p 1) * f (WithLp.toLp 2 (sphericalPoint p))
  rw [sphericalDerivative_det, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1).le)]

end OQ7Prescribed
