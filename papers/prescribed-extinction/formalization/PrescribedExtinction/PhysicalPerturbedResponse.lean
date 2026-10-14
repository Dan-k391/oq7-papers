import PrescribedExtinction.PhysicalElectricWoodbury
import PrescribedExtinction.PhysicalAbsorptionWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology Ring

def physicalRestrictedElectric (k : ℝ) (B : TwoLayerBody) (σ : Direction) (ν θ : ℝ) (α β : ℂ) : BodyCurrentL2 B :=
  Ring.inverse (physicalElectricOperator k B ν θ α β) (bodyIncidentCurrent k B σ)

def physicalPerturbedCurrent (k : ℝ) (B : TwoLayerBody) (σ : Direction) (ν θ : ℝ) (α β : ℂ) : BodyCurrentL2 B :=
  isotropicSusceptibilityOperator B ν θ α β (physicalRestrictedElectric k B σ ν θ α β)

theorem physicalRestrictedElectric_equation (k : ℝ) (B : TwoLayerBody) (σ : Direction) (ν θ : ℝ) (α β : ℂ)
    (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalElectricOperator k B ν θ α β (physicalRestrictedElectric k B σ ν θ α β) = bodyIncidentCurrent k B σ := by
  have h := congrArg (fun T : BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B => T (bodyIncidentCurrent k B σ))
    (Ring.mul_inverse_cancel (physicalElectricOperator k B ν θ α β) hL)
  exact h

theorem physicalRestrictedElectric_eq_total (k : ℝ) (B : TwoLayerBody) (σ : Direction) (ν θ : ℝ) (α β : ℂ)
    (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    physicalRestrictedElectric k B σ ν θ α β = bodyIncidentCurrent k B σ +
      bodyOutgoingOperator k B (physicalPerturbedCurrent k B σ ν θ α β) := by
  have h := physicalRestrictedElectric_equation k B σ ν θ α β hL
  change physicalRestrictedElectric k B σ ν θ α β - bodyOutgoingOperator k B (physicalPerturbedCurrent k B σ ν θ α β) = _ at h
  exact sub_eq_iff_eq_add.mp h

theorem isotropicSusceptibilityOperator_joint_continuous (B : TwoLayerBody) (α β : ℂ) :
    Continuous (fun x : ℝ × ℝ => isotropicSusceptibilityOperator B x.1 x.2 α β) := by
  have hJ : Continuous (fun x : ℝ × ℝ => activeInjection B (basisR 0) (rotatedAxis x.2)) :=
    (activeInjection_rotation_continuous B).comp continuous_snd
  have hP : Continuous (fun x : ℝ × ℝ => activeProjection B (basisR 0) (rotatedAxis x.2)) :=
    (activeProjection_rotation_continuous B).comp continuous_snd
  exact (hJ.clm_comp (continuous_const.clm_comp hP)).add
    ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).smul continuous_const)

theorem physicalRestrictedElectric_joint_continuousAt (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (x : ℝ × ℝ) (hL : IsUnit (physicalElectricOperator k B x.1 x.2 α β)) :
    ContinuousAt (fun y : ℝ × ℝ => physicalRestrictedElectric k B σ y.1 y.2 α β) x := by
  rcases hL with ⟨u, hu⟩
  have hinv : ContinuousAt (fun y : ℝ × ℝ => Ring.inverse (physicalElectricOperator k B y.1 y.2 α β)) x := by
    have hi := NormedRing.inverse_continuousAt (R := BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B) u
    rw [hu] at hi
    exact hi.comp (f := fun y : ℝ × ℝ => physicalElectricOperator k B y.1 y.2 α β)
      (physicalElectricOperator_joint_continuous k B α β).continuousAt
  exact hinv.clm_apply continuousAt_const

theorem physicalPerturbedCurrent_joint_continuousAt (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (x : ℝ × ℝ) (hL : IsUnit (physicalElectricOperator k B x.1 x.2 α β)) :
    ContinuousAt (fun y : ℝ × ℝ => physicalPerturbedCurrent k B σ y.1 y.2 α β) x :=
  (isotropicSusceptibilityOperator_joint_continuous B α β).continuousAt.clm_apply
    (physicalRestrictedElectric_joint_continuousAt k B σ α β x hL)

def physicalPerturbedExtinction (k : ℝ) (B : TwoLayerBody) (σ : Direction) (ν θ : ℝ) (α β : ℂ) : ℝ :=
  k * (inner ℂ (bodyIncidentCurrent k B σ) (physicalPerturbedCurrent k B σ ν θ α β)).im

def physicalPerturbedAbsorption (k : ℝ) (B : TwoLayerBody) (σ : Direction) (ν θ : ℝ) (α β : ℂ) : ℝ :=
  k * (inner ℂ (physicalRestrictedElectric k B σ ν θ α β) (physicalPerturbedCurrent k B σ ν θ α β)).im

def physicalPerturbedAsymmetry (k : ℝ) (B : TwoLayerBody) (ν θ : ℝ) (α β : ℂ) : ℝ :=
  |physicalPerturbedAbsorption k B .plus ν θ α β - physicalPerturbedAbsorption k B .minus ν θ α β| /
    physicalPerturbedExtinction k B .plus ν θ α β

theorem physicalPerturbedExtinction_joint_continuousAt (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (x : ℝ × ℝ) (hL : IsUnit (physicalElectricOperator k B x.1 x.2 α β)) :
    ContinuousAt (fun y : ℝ × ℝ => physicalPerturbedExtinction k B σ y.1 y.2 α β) x :=
  continuousAt_const.mul (Complex.continuous_im.continuousAt.comp
    (continuousAt_const.inner (physicalPerturbedCurrent_joint_continuousAt k B σ α β x hL)))

theorem physicalPerturbedAbsorption_joint_continuousAt (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (α β : ℂ) (x : ℝ × ℝ) (hL : IsUnit (physicalElectricOperator k B x.1 x.2 α β)) :
    ContinuousAt (fun y : ℝ × ℝ => physicalPerturbedAbsorption k B σ y.1 y.2 α β) x :=
  continuousAt_const.mul (Complex.continuous_im.continuousAt.comp
    ((physicalRestrictedElectric_joint_continuousAt k B σ α β x hL).inner
      (physicalPerturbedCurrent_joint_continuousAt k B σ α β x hL)))

theorem physicalPerturbedAsymmetry_joint_continuousAt (k : ℝ) (B : TwoLayerBody)
    (α β : ℂ) (x : ℝ × ℝ) (hL : IsUnit (physicalElectricOperator k B x.1 x.2 α β))
    (hX : physicalPerturbedExtinction k B .plus x.1 x.2 α β ≠ 0) :
    ContinuousAt (fun y : ℝ × ℝ => physicalPerturbedAsymmetry k B y.1 y.2 α β) x :=
  ((physicalPerturbedAbsorption_joint_continuousAt k B .plus α β x hL).sub
    (physicalPerturbedAbsorption_joint_continuousAt k B .minus α β x hL)).abs.div
      (physicalPerturbedExtinction_joint_continuousAt k B .plus α β x hL) hX

end OQ7Prescribed
