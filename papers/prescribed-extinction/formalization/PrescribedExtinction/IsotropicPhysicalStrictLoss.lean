import PrescribedExtinction.IsotropicPhysicalPowers
import PrescribedExtinction.NormalizedWork
import PrescribedExtinction.ExtinctionReciprocity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem bodyIncidentCurrent_ne_zero (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    bodyIncidentCurrent k B σ ≠ 0 := by
  intro hz
  have h := activeProjectedIncident_sine_factorization k B σ (Real.pi / 2)
  rw [hz, map_zero, Real.sin_pi_div_two, Complex.ofReal_one, one_smul] at h
  exact normalizedIncidentDrive_ne_zero k B σ h.symm

theorem isotropicSusceptibilityOperator_imaginary_bound (B : TwoLayerBody) (ν θ : ℝ)
    (α β : ℂ) (hα : 0 ≤ α.im) (hβ : 0 ≤ β.im) (f : BodyCurrentL2 B) :
    ν * ‖f‖ ^ 2 ≤ (inner ℂ f (isotropicSusceptibilityOperator B ν θ α β f)).im := by
  let J := isotropicSusceptibilityOperator B ν θ α β
  have hi := L2.integrable_inner (𝕜 := ℂ) (f : VectorL2) (J f : VectorL2)
  have hii := L2.integrable_inner (𝕜 := ℂ) (f : VectorL2) (f : VectorL2)
  have hself (x : Position) : (inner ℂ ((f : VectorL2) x) ((f : VectorL2) x)).re = ‖(f : VectorL2) x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) ((f : VectorL2) x)
  have hs : ∫ x : Position, ‖(f : VectorL2) x‖ ^ 2 = ‖f‖ ^ 2 := by
    have hre := (Complex.reCLM.integral_comp_comm hii).symm
    change (∫ x : Position, inner ℂ ((f : VectorL2) x) ((f : VectorL2) x)).re =
      ∫ x : Position, (inner ℂ ((f : VectorL2) x) ((f : VectorL2) x)).re at hre
    rw [show (fun x => ‖(f : VectorL2) x‖ ^ 2) =
      (fun x => (inner ℂ ((f : VectorL2) x) ((f : VectorL2) x)).re) from funext (fun x => (hself x).symm),
      ← hre]
    change (inner ℂ (f : VectorL2) (f : VectorL2)).re = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hnorm : Integrable (fun x : Position => ‖(f : VectorL2) x‖ ^ 2) volume := by
    have hn := hii.re
    change Integrable (fun x : Position => (inner ℂ ((f : VectorL2) x) ((f : VectorL2) x)).re) volume at hn
    simpa only [hself] using hn
  have hm : ν * ‖f‖ ^ 2 ≤ ∫ x : Position, (inner ℂ ((f : VectorL2) x) ((J f : VectorL2) x)).im := by
    rw [← hs, ← integral_const_mul]
    apply integral_mono_ae (hnorm.const_mul ν) hi.im
    filter_upwards [isotropicSusceptibilityOperator_coe B ν θ α β f] with x hx
    change ν * ‖(f : VectorL2) x‖ ^ 2 ≤ (inner ℂ ((f : VectorL2) x) ((J f : VectorL2) x)).im
    rw [hx]
    by_cases hxa : x 2 < B.absorberThickness
    · simp only [hxa, ite_true, isotropicRankOneBody]
      rw [susceptibility_quadratic_im, quadratic_layer_im, squareNorm_eq_norm_sq]
      exact le_add_of_nonneg_right (mul_nonneg hα (Complex.normSq_nonneg _))
    · simp only [hxa, ite_false, isotropicRankOneBody]
      rw [susceptibility_quadratic_im, quadratic_layer_im, squareNorm_eq_norm_sq]
      exact le_add_of_nonneg_right (mul_nonneg hβ (Complex.normSq_nonneg _))
  have him := (Complex.imCLM.integral_comp_comm hi).symm
  change (∫ x : Position, inner ℂ ((f : VectorL2) x) ((J f : VectorL2) x)).im =
    ∫ x : Position, (inner ℂ ((f : VectorL2) x) ((J f : VectorL2) x)).im at him
  rw [← him] at hm
  exact hm

theorem physicalPerturbedAbsorption_pos (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (ν θ : ℝ) (hν : 0 < ν) (α β : ℂ) (hα : 0 ≤ α.im) (hβ : 0 ≤ β.im)
    (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    0 < physicalPerturbedAbsorption k B σ ν θ α β := by
  have he : physicalRestrictedElectric k B σ ν θ α β ≠ 0 := by
    intro hz
    have h := physicalRestrictedElectric_equation k B σ ν θ α β hL
    rw [hz, map_zero] at h
    exact bodyIncidentCurrent_ne_zero k B σ h.symm
  have hb := isotropicSusceptibilityOperator_imaginary_bound B ν θ α β hα hβ
    (physicalRestrictedElectric k B σ ν θ α β)
  exact mul_pos hk ((mul_pos hν (sq_pos_of_pos (norm_pos_iff.mpr he))).trans_le hb)

theorem physicalPerturbedExtinction_reciprocity (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (ν θ : ℝ) (α β : ℂ) (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalPerturbedExtinction k B .plus ν θ α β = physicalPerturbedExtinction k B .minus ν θ α β := by
  rw [physicalPerturbedExtinction_eq_original k B .plus ν θ α β hL,
    physicalPerturbedExtinction_eq_original k B .minus ν θ α β hL]
  exact physicalVolume_extinction_reciprocity k hk (isotropicRankOneBody B ν θ α β)
    (layerPermittivity_reciprocal _ _ _ _) (layerPermittivity_reciprocal _ _ _ _) _ _
    (physicalPerturbedCurrent_physicalVolumeEquation k B .plus ν θ α β hL)
    (physicalPerturbedCurrent_physicalVolumeEquation k B .minus ν θ α β hL)

theorem physicalPerturbedAbsorption_le_extinction (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (ν θ : ℝ) (α β : ℂ) (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalPerturbedAbsorption k B σ ν θ α β ≤ physicalPerturbedExtinction k B σ ν θ α β := by
  rw [physicalPerturbedExtinction_eq_original k B σ ν θ α β hL,
    physicalPerturbedAbsorption_eq_original k B σ ν θ α β hL]
  exact physicalVolume_absorption_le_extinction k hk (isotropicRankOneBody B ν θ α β) σ _
    (physicalPerturbedCurrent_physicalVolumeEquation k B σ ν θ α β hL)

theorem physicalPerturbedAsymmetry_lt_one (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (ν θ : ℝ) (hν : 0 < ν) (α β : ℂ) (hα : 0 ≤ α.im) (hβ : 0 ≤ β.im)
    (hL : IsUnit (physicalElectricOperator k B ν θ α β))
    (hX : 0 < physicalPerturbedExtinction k B .plus ν θ α β) :
    physicalPerturbedAsymmetry k B ν θ α β < 1 := by
  have hp := physicalPerturbedAbsorption_pos k hk B .plus ν θ hν α β hα hβ hL
  have hm := physicalPerturbedAbsorption_pos k hk B .minus ν θ hν α β hα hβ hL
  have hpe := physicalPerturbedAbsorption_le_extinction k hk B .plus ν θ α β hL
  have hme := physicalPerturbedAbsorption_le_extinction k hk B .minus ν θ α β hL
  rw [← physicalPerturbedExtinction_reciprocity k hk B ν θ α β hL] at hme
  unfold physicalPerturbedAsymmetry
  apply (div_lt_one hX).mpr
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end OQ7Prescribed
