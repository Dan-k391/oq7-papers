import PrescribedExtinction.PhysicalPerturbedResponse
import PrescribedExtinction.PhysicalRankOneExtinctionBracket

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OQ7Prescribed
open MeasureTheory
open scoped Ring

theorem physicalElectricOperator_zero_isUnit (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : IsUnit (physicalElectricOperator k B 0 θ α β) := by
  rw [← rankOneElectricUnit_val k hk B θ α β hα hβ]
  exact Units.isUnit _

theorem physicalPerturbedCurrent_zero_eq_active (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    physicalPerturbedCurrent k B σ 0 θ α β = activeInjection B (basisR 0) (rotatedAxis θ)
      (activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ) := by
  let K := bodyOutgoingOperator k B
  let J := activeInjection B (basisR 0) (rotatedAxis θ)
  let P := activeProjection B (basisR 0) (rotatedAxis θ)
  let C := activeForwardMaterial B α β
  let D := activeInverseMaterial B α β
  let e := activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  have he : e.toContinuousLinearMap = P ∘L K ∘L J - D := by
    apply ContinuousLinearMap.ext
    intro q
    exact activeMaterialEquiv_apply k hk B (basisR 0) (rotatedAxis θ) α β hα hβ q
  have hαn : α ≠ 0 := by intro hz; simpa [hz] using hα
  have hβn : β ≠ 0 := by intro hz; simpa [hz] using hβ
  have hInv : Ring.inverse (physicalElectricOperator k B 0 θ α β) = woodburyElectricInverse K J P e := by
    rw [← rankOneElectricUnit_val k hk B θ α β hα hβ, Ring.inverse_unit]
    rfl
  have h := woodburySusceptibility_inverse_apply K J P C D
    (activeForwardMaterial_inverse_right B α β hαn hβn) e he (bodyIncidentCurrent k B σ)
  unfold physicalPerturbedCurrent physicalRestrictedElectric
  rw [hInv]
  change J (C (P (woodburyElectricInverse K J P e (bodyIncidentCurrent k B σ)))) +
    (Complex.I * (0 : ℂ)) • woodburyElectricInverse K J P e (bodyIncidentCurrent k B σ) =
      J (e.symm (-P (bodyIncidentCurrent k B σ)))
  rw [mul_zero, zero_smul, add_zero, map_neg, map_neg]
  exact h

theorem physicalPerturbedExtinction_zero_eq_original (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    physicalPerturbedExtinction k B σ 0 θ α β = rankOneRotationExtinction k hk B σ θ α β hα hβ := by
  unfold physicalPerturbedExtinction
  rw [physicalPerturbedCurrent_zero_eq_active]
  unfold rankOneRotationExtinction rankOnePhysicalElectric
  rw [activePhysicalExtinction_work, activeProjection_inner]

theorem physicalPerturbedAbsorption_zero_eq_original (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (σ : Direction) (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    physicalPerturbedAbsorption k B σ 0 θ α β =
      absorption k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
        (rankOnePhysicalElectric k hk B σ θ α β hα hβ) := by
  unfold physicalPerturbedAbsorption
  rw [physicalRestrictedElectric_eq_total k B σ 0 θ α β (physicalElectricOperator_zero_isUnit k hk B θ α β hα hβ),
    physicalPerturbedCurrent_zero_eq_active]
  unfold rankOnePhysicalElectric
  exact (volumeAbsorption_body_inner k (rankOneBody B (basisR 0) (rotatedAxis θ) α β) σ _
    (activePhysicalSolution_physicalVolumeEquation k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ)).symm

theorem physicalPerturbedAsymmetry_zero_eq_original (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    physicalPerturbedAsymmetry k B 0 θ α β =
      normalizedAsymmetry k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
        (rankOnePhysicalElectric k hk B .plus θ α β hα hβ)
        (rankOnePhysicalElectric k hk B .minus θ α β hα hβ) := by
  unfold physicalPerturbedAsymmetry normalizedAsymmetry
  rw [physicalPerturbedAbsorption_zero_eq_original, physicalPerturbedAbsorption_zero_eq_original,
    physicalPerturbedExtinction_zero_eq_original]
  rfl

end OQ7Prescribed
