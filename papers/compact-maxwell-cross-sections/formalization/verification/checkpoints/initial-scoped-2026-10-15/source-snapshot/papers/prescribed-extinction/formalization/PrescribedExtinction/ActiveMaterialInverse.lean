import PrescribedExtinction.ActiveCurrentSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

def activeScalarLoss (α : ℂ) : ℝ := α.im / Complex.normSq α

theorem activeScalarLoss_pos (α : ℂ) (hα : 0 < α.im) : 0 < activeScalarLoss α := by
  have hne : α ≠ 0 := by intro hz; simpa [hz] using hα
  exact div_pos hα (Complex.normSq_pos.mpr hne)

theorem scalarInverse_negative_imaginary (α z : ℂ) :
    -(inner ℂ z (α⁻¹ • z)).im = activeScalarLoss α * ‖z‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change -(α⁻¹ * ((‖z‖ : ℝ) : ℂ) ^ 2).im = _
  simp [activeScalarLoss, pow_two, Complex.mul_im, Complex.mul_re, Complex.inv_im]
  ring

def activeInverseMaterial (B : TwoLayerBody) (α β : ℂ) :
    ScalarBodyCurrentL2 B →L[ℂ] ScalarBodyCurrentL2 B :=
  twoPieceSupportedOperator volume B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
    (α⁻¹ • ContinuousLinearMap.id ℂ ℂ) (β⁻¹ • ContinuousLinearMap.id ℂ ℂ)

def activeMaterialCoercivity (α β : ℂ) : ℝ := min (activeScalarLoss α) (activeScalarLoss β)

theorem activeMaterialCoercivity_pos (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    0 < activeMaterialCoercivity α β := lt_min (activeScalarLoss_pos α hα) (activeScalarLoss_pos β hβ)

theorem activeInverseMaterial_negative_imaginary_bound (B : TwoLayerBody) (α β : ℂ)
    (q : ScalarBodyCurrentL2 B) :
    activeMaterialCoercivity α β * ‖q‖ ^ 2 ≤ -(inner ℂ q (activeInverseMaterial B α β q)).im := by
  apply twoPieceSupportedOperator_negative_imaginary_bound
  · intro z
    change _ ≤ -(inner ℂ z (α⁻¹ • z)).im
    rw [scalarInverse_negative_imaginary]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · intro z
    change _ ≤ -(inner ℂ z (β⁻¹ • z)).im
    rw [scalarInverse_negative_imaginary]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)

/-- The exact scalar-current compression of the physical three-dimensional operator. -/
def activeMaterialOperator (k : ℝ) (B : TwoLayerBody) (u v : Position) (α β : ℂ) :
    ScalarBodyCurrentL2 B →L[ℂ] ScalarBodyCurrentL2 B :=
  activeProjection B u v ∘L bodyOutgoingOperator k B ∘L activeInjection B u v -
    activeInverseMaterial B α β

theorem activeMaterialOperator_imaginary_coercive (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (u v : Position) (α β : ℂ) (q : ScalarBodyCurrentL2 B) :
    activeMaterialCoercivity α β * ‖q‖ ^ 2 ≤ (inner ℂ q (activeMaterialOperator k B u v α β q)).im := by
  have ht := activeProjectedOutgoing_im_nonneg k hk B u v q
  have hm := activeInverseMaterial_negative_imaginary_bound B α β q
  change _ ≤ (inner ℂ q (activeProjection B u v (bodyOutgoingOperator k B (activeInjection B u v q)) -
    activeInverseMaterial B α β q)).im
  rw [inner_sub_right, Complex.sub_im]
  linarith

def activeMaterialEquiv (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (u v : Position) (α β : ℂ)
    (hα : 0 < α.im) (hβ : 0 < β.im) : ScalarBodyCurrentL2 B ≃L[ℂ] ScalarBodyCurrentL2 B :=
  complexImaginaryCoerciveEquiv (activeMaterialOperator k B u v α β) (activeMaterialCoercivity α β)
    (activeMaterialCoercivity_pos α β hα hβ) (activeMaterialOperator_imaginary_coercive k hk B u v α β)

theorem activeMaterialEquiv_apply (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (u v : Position) (α β : ℂ)
    (hα : 0 < α.im) (hβ : 0 < β.im) (q : ScalarBodyCurrentL2 B) :
    activeMaterialEquiv k hk B u v α β hα hβ q = activeMaterialOperator k B u v α β q := rfl

theorem activeMaterialEquiv_inverse_norm_le (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (u v : Position) (α β : ℂ)
    (hα : 0 < α.im) (hβ : 0 < β.im) :
    ‖(activeMaterialEquiv k hk B u v α β hα hβ).symm.toContinuousLinearMap‖ ≤
      1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β) :=
  complexImaginaryCoerciveEquiv_inverse_norm_le _ _ _ _

end OQ7Prescribed
