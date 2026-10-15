import PrescribedExtinction.BoundedWoodbury
import PrescribedExtinction.RotationContinuity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
local notation "ScalarVolumeL2" => Lp ℂ 2 (volume : Measure Position)

def activeForwardMaterial (B : TwoLayerBody) (α β : ℂ) :
    ScalarBodyCurrentL2 B →L[ℂ] ScalarBodyCurrentL2 B := activeInverseMaterial B α⁻¹ β⁻¹

theorem activeForwardMaterial_coe (B : TwoLayerBody) (α β : ℂ) (q : ScalarBodyCurrentL2 B) :
    (activeForwardMaterial B α β q : ScalarVolumeL2) =ᵐ[volume]
      fun x => if x 2 < B.absorberThickness then α * (q : ScalarVolumeL2) x else β * (q : ScalarVolumeL2) x := by
  simpa only [activeForwardMaterial, inv_inv] using activeInverseMaterial_coe B α⁻¹ β⁻¹ q

theorem activeForwardMaterial_inverse_right (B : TwoLayerBody) (α β : ℂ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    activeForwardMaterial B α β ∘L activeInverseMaterial B α β =
      ContinuousLinearMap.id ℂ (ScalarBodyCurrentL2 B) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [activeForwardMaterial_coe B α β (activeInverseMaterial B α β q),
    activeInverseMaterial_coe B α β q] with x hC hD
  change (activeForwardMaterial B α β (activeInverseMaterial B α β q) : ScalarVolumeL2) x = (q : ScalarVolumeL2) x
  rw [hC, hD]
  by_cases hx : x 2 < B.absorberThickness <;> simp [hx, hα, hβ, mul_assoc]

theorem activeForwardMaterial_inverse_left (B : TwoLayerBody) (α β : ℂ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    activeInverseMaterial B α β ∘L activeForwardMaterial B α β =
      ContinuousLinearMap.id ℂ (ScalarBodyCurrentL2 B) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [activeInverseMaterial_coe B α β (activeForwardMaterial B α β q),
    activeForwardMaterial_coe B α β q] with x hD hC
  change (activeInverseMaterial B α β (activeForwardMaterial B α β q) : ScalarVolumeL2) x = (q : ScalarVolumeL2) x
  rw [hD, hC]
  by_cases hx : x 2 < B.absorberThickness <;> simp [hx, hα, hβ, mul_assoc]

def rankOneSusceptibilityOperator (B : TwoLayerBody) (θ : ℝ) (α β : ℂ) :
    BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  activeInjection B (basisR 0) (rotatedAxis θ) ∘L activeForwardMaterial B α β ∘L
    activeProjection B (basisR 0) (rotatedAxis θ)

def isotropicSusceptibilityOperator (B : TwoLayerBody) (ν θ : ℝ) (α β : ℂ) :
    BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  rankOneSusceptibilityOperator B θ α β + (Complex.I * (ν : ℂ)) • ContinuousLinearMap.id ℂ (BodyCurrentL2 B)

def physicalElectricOperator (k : ℝ) (B : TwoLayerBody) (ν θ : ℝ) (α β : ℂ) :
    BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  ContinuousLinearMap.id ℂ (BodyCurrentL2 B) - bodyOutgoingOperator k B ∘L isotropicSusceptibilityOperator B ν θ α β

def rankOneElectricUnit (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (θ : ℝ) (α β : ℂ)
    (hα : 0 < α.im) (hβ : 0 < β.im) : (BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B)ˣ := by
  have hαn : α ≠ 0 := by intro hz; simpa [hz] using hα
  have hβn : β ≠ 0 := by intro hz; simpa [hz] using hβ
  refine woodburyElectricUnit (bodyOutgoingOperator k B) (activeInjection B (basisR 0) (rotatedAxis θ))
    (activeProjection B (basisR 0) (rotatedAxis θ)) (activeForwardMaterial B α β) (activeInverseMaterial B α β)
    (activeForwardMaterial_inverse_right B α β hαn hβn) (activeForwardMaterial_inverse_left B α β hαn hβn)
    (activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ) ?_
  apply ContinuousLinearMap.ext
  intro q
  exact activeMaterialEquiv_apply k hk B (basisR 0) (rotatedAxis θ) α β hα hβ q

theorem rankOneElectricUnit_val (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (θ : ℝ) (α β : ℂ)
    (hα : 0 < α.im) (hβ : 0 < β.im) :
    (rankOneElectricUnit k hk B θ α β hα hβ : BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B) =
      physicalElectricOperator k B 0 θ α β := by
  simp only [rankOneElectricUnit, woodburyElectricUnit, woodburyElectricOperator,
    physicalElectricOperator, isotropicSusceptibilityOperator, rankOneSusceptibilityOperator,
    Complex.ofReal_zero, mul_zero]
  apply ContinuousLinearMap.ext
  intro f
  change f - bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ)
      (activeForwardMaterial B α β (activeProjection B (basisR 0) (rotatedAxis θ) f))) =
    f - bodyOutgoingOperator k B (activeInjection B (basisR 0) (rotatedAxis θ)
      (activeForwardMaterial B α β (activeProjection B (basisR 0) (rotatedAxis θ) f)) + (0 : ℂ) • f)
  rw [zero_smul, add_zero]

theorem physicalElectricOperator_joint_continuous (k : ℝ) (B : TwoLayerBody) (α β : ℂ) :
    Continuous (fun x : ℝ × ℝ => physicalElectricOperator k B x.1 x.2 α β) := by
  have hJ : Continuous (fun x : ℝ × ℝ => activeInjection B (basisR 0) (rotatedAxis x.2)) :=
    (activeInjection_rotation_continuous B).comp continuous_snd
  have hP : Continuous (fun x : ℝ × ℝ => activeProjection B (basisR 0) (rotatedAxis x.2)) :=
    (activeProjection_rotation_continuous B).comp continuous_snd
  have hS : Continuous (fun x : ℝ × ℝ => isotropicSusceptibilityOperator B x.1 x.2 α β) :=
    (hJ.clm_comp (continuous_const.clm_comp hP)).add
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).smul continuous_const)
  exact continuous_const.sub (continuous_const.clm_comp hS)

end OQ7Prescribed
