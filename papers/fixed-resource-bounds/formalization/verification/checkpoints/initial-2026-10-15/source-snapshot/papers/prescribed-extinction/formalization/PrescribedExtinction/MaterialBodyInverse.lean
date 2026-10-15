import PrescribedExtinction.BodyCurrentSpace
import PrescribedExtinction.TwoPieceL2
import PrescribedExtinction.TensorLossCoercivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical

/-- Data proved from strict physical tensor loss, rather than assumed scattering data. -/
structure SusceptibilityInverseData (T : Tensor) where
  inverse : Vector ≃L[ℂ] Vector
  forward_eq : ∀ v : Vector, inverse v = tensorMap (T - 1) v
  loss : ℝ
  loss_pos : 0 < loss
  negative_imaginary_bound : ∀ v : Vector, loss * ‖v‖ ^ 2 ≤ -(inner ℂ v (inverse.symm v)).im

def admissibleSusceptibilityInverseData (P Q : ℝ) (T : Tensor)
    (hT : MaterialAdmissible P Q T) : SusceptibilityInverseData T := by
  have hn : Nonempty (SusceptibilityInverseData T) := by
    obtain ⟨c, hc, e, he, _, hi⟩ := admissible_susceptibility_bounded_inverse P Q T hT
    exact ⟨⟨e, he, c / (‖tensorMap (T - 1)‖ + 1) ^ 2, by positivity, hi⟩⟩
  exact Classical.choice hn

def bodyAbsorberSlice (B : TwoLayerBody) : Set Position := {x | x 2 < B.absorberThickness}

theorem bodyAbsorberSlice_measurable (B : TwoLayerBody) : MeasurableSet (bodyAbsorberSlice B) :=
  (isOpen_lt (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Position →L[ℝ] ℝ).continuous
    continuous_const).measurableSet

def bodyInverseSusceptibility (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) : BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  twoPieceSupportedOperator volume B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
    a.inverse.symm.toContinuousLinearMap b.inverse.symm.toContinuousLinearMap

theorem bodyInverseSusceptibility_coe (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) (f : BodyCurrentL2 B) :
    (bodyInverseSusceptibility B a b f : VectorL2) =ᵐ[volume]
      fun x => if x 2 < B.absorberThickness then a.inverse.symm ((f : VectorL2) x)
        else b.inverse.symm ((f : VectorL2) x) :=
  twoPieceSupportedOperator_coe _ _ _ _ _ _ _

def materialBodyCoercivity (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) : ℝ := min a.loss b.loss

theorem materialBodyCoercivity_pos (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) : 0 < materialBodyCoercivity B a b :=
  lt_min a.loss_pos b.loss_pos

theorem bodyInverseSusceptibility_negative_imaginary_bound (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) (f : BodyCurrentL2 B) :
    materialBodyCoercivity B a b * ‖f‖ ^ 2 ≤ -(inner ℂ f (bodyInverseSusceptibility B a b f)).im := by
  apply twoPieceSupportedOperator_negative_imaginary_bound
  · intro v
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖v‖)).trans
      (a.negative_imaginary_bound v)
  · intro v
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg ‖v‖)).trans
      (b.negative_imaginary_bound v)

/-- T_k - chi^{-1}, on the actual finite body. Its inverse norm bound has no aperture factor. -/
def materialBodyOperator (k : ℝ) (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) : BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  bodyOutgoingOperator k B - bodyInverseSusceptibility B a b

theorem materialBodyOperator_imaginary_coercive (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) (f : BodyCurrentL2 B) :
    materialBodyCoercivity B a b * ‖f‖ ^ 2 ≤ (inner ℂ f (materialBodyOperator k B a b f)).im := by
  have ht := bodyOutgoingOperator_im_nonneg k hk B f
  have hj := bodyInverseSusceptibility_negative_imaginary_bound B a b f
  change _ ≤ (inner ℂ f (bodyOutgoingOperator k B f - bodyInverseSusceptibility B a b f)).im
  rw [inner_sub_right, Complex.sub_im]
  linarith

def materialBodyEquiv (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) : BodyCurrentL2 B ≃L[ℂ] BodyCurrentL2 B :=
  complexImaginaryCoerciveEquiv (materialBodyOperator k B a b) (materialBodyCoercivity B a b)
    (materialBodyCoercivity_pos B a b) (materialBodyOperator_imaginary_coercive k hk B a b)

theorem materialBodyEquiv_apply (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) (f : BodyCurrentL2 B) :
    materialBodyEquiv k hk B a b f = materialBodyOperator k B a b f := rfl

theorem materialBodyEquiv_inverse_norm_le (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) :
    ‖(materialBodyEquiv k hk B a b).symm.toContinuousLinearMap‖ ≤ 1 / min a.loss b.loss :=
  complexImaginaryCoerciveEquiv_inverse_norm_le _ _ _ _

end OQ7Prescribed
