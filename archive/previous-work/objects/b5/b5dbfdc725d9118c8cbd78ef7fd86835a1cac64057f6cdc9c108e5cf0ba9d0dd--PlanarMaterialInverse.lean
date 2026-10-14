import work.PlanarScalarWork
import work.PlanarLayerCompression

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarActiveOutgoing_im_nonneg (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (q : PlanarCurrentL2 L) : 0 ≤ (inner ℂ q (planarActiveOutgoing k hk L hL h θ q)).im := by
  unfold planarActiveOutgoing
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right, Complex.add_im,
    ContinuousLinearMap.adjoint_inner_right]
  exact add_nonneg (planarScalarOutgoing_im_nonneg k hk L hL _)
    (planarScalarOutgoing_im_nonneg k hk L hL _)

def planarInverseMaterial (L h : ℝ) (α β : ℂ) : PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L :=
  twoPieceSupportedOperator volume (Icc 0 L) (Iio h) measurableSet_Iio
    (α⁻¹ • ContinuousLinearMap.id ℂ ℂ) (β⁻¹ • ContinuousLinearMap.id ℂ ℂ)

theorem planarInverseMaterial_negative_imaginary_bound (L h : ℝ) (α β : ℂ) (q : PlanarCurrentL2 L) :
    activeMaterialCoercivity α β * ‖q‖ ^ 2 ≤ -(inner ℂ q (planarInverseMaterial L h α β q)).im := by
  apply twoPieceSupportedOperator_negative_imaginary_bound
  · intro z
    change _ ≤ -(inner ℂ z (α⁻¹ • z)).im
    rw [scalarInverse_negative_imaginary]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · intro z
    change _ ≤ -(inner ℂ z (β⁻¹ • z)).im
    rw [scalarInverse_negative_imaginary]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)

def planarActiveMaterialOperator (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ) (α β : ℂ) :
    PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L :=
  planarActiveOutgoing k hk L hL h θ - planarInverseMaterial L h α β

theorem planarActiveMaterialOperator_imaginary_coercive (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L)
    (h θ : ℝ) (α β : ℂ) (q : PlanarCurrentL2 L) :
    activeMaterialCoercivity α β * ‖q‖ ^ 2 ≤ (inner ℂ q (planarActiveMaterialOperator k hk L hL h θ α β q)).im := by
  have ht := planarActiveOutgoing_im_nonneg k hk L hL h θ q
  have hm := planarInverseMaterial_negative_imaginary_bound L h α β q
  change _ ≤ (inner ℂ q (planarActiveOutgoing k hk L hL h θ q - planarInverseMaterial L h α β q)).im
  rw [inner_sub_right, Complex.sub_im]
  linarith

def planarActiveMaterialEquiv (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : PlanarCurrentL2 L ≃L[ℂ] PlanarCurrentL2 L :=
  complexImaginaryCoerciveEquiv (planarActiveMaterialOperator k hk L hL h θ α β)
    (activeMaterialCoercivity α β) (activeMaterialCoercivity_pos α β hα hβ)
    (planarActiveMaterialOperator_imaginary_coercive k hk L hL h θ α β)

theorem planarActiveMaterialEquiv_inverse_norm_le (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    ‖(planarActiveMaterialEquiv k hk L hL h θ α β hα hβ).symm.toContinuousLinearMap‖ ≤
      1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β) :=
  complexImaginaryCoerciveEquiv_inverse_norm_le _ _ _ _

end OQ7Prescribed
