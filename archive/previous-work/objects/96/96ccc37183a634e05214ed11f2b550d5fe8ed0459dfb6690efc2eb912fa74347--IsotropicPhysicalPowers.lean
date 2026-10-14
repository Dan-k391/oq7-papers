import work.IsotropicPhysicalBody

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem physicalPerturbedExtinction_eq_original (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (ν θ : ℝ) (α β : ℂ) (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalPerturbedExtinction k B σ ν θ α β =
      extinction k (isotropicRankOneBody B ν θ α β) σ
        (volumeTotalElectric k σ (bodyCurrentPolarization B (physicalPerturbedCurrent k B σ ν θ α β))) := by
  rw [volumeExtinction_current_work k _ σ _
    (physicalPerturbedCurrent_physicalVolumeEquation k B σ ν θ α β hL)]
  change physicalPerturbedExtinction k B σ ν θ α β =
    k * (∫ x in B.domain, pairing (incidentElectric k σ x)
      ((bodyCurrentPolarization B (physicalPerturbedCurrent k B σ ν θ α β)).current x)).im
  rw [bodyCurrent_incident_work]
  rfl

theorem physicalPerturbedAbsorption_eq_original (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (ν θ : ℝ) (α β : ℂ) (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalPerturbedAbsorption k B σ ν θ α β =
      absorption k (isotropicRankOneBody B ν θ α β)
        (volumeTotalElectric k σ (bodyCurrentPolarization B (physicalPerturbedCurrent k B σ ν θ α β))) := by
  have hp := volumeAbsorption_body_inner k (isotropicRankOneBody B ν θ α β) σ
    (physicalPerturbedCurrent k B σ ν θ α β)
    (physicalPerturbedCurrent_physicalVolumeEquation k B σ ν θ α β hL)
  unfold physicalPerturbedAbsorption
  rw [physicalRestrictedElectric_eq_total k B σ ν θ α β hL]
  exact hp.symm

theorem physicalPerturbedAsymmetry_eq_original (k : ℝ) (B : TwoLayerBody)
    (ν θ : ℝ) (α β : ℂ) (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalPerturbedAsymmetry k B ν θ α β = normalizedAsymmetry k (isotropicRankOneBody B ν θ α β)
      (volumeTotalElectric k .plus (bodyCurrentPolarization B (physicalPerturbedCurrent k B .plus ν θ α β)))
      (volumeTotalElectric k .minus (bodyCurrentPolarization B (physicalPerturbedCurrent k B .minus ν θ α β))) := by
  unfold physicalPerturbedAsymmetry normalizedAsymmetry
  rw [physicalPerturbedExtinction_eq_original k B .plus ν θ α β hL,
    physicalPerturbedAbsorption_eq_original k B .plus ν θ α β hL,
    physicalPerturbedAbsorption_eq_original k B .minus ν θ α β hL]

end OQ7Prescribed
