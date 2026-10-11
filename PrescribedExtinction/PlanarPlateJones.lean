import PrescribedExtinction.PlanarPlateChannels

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem losslessPlateCartesian_boundary (k : ℝ) (hk : 0 < k) (h : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (θ : ℝ) (Ex Ey Hx Hy : ℂ) :
    (losslessPlateXLayer k h j hj θ Ex Ey Hx Hy).electric (h + plateDesignThickness k j) =
        ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2) * Ex +
          2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * Ey ∧
    (losslessPlateYLayer k h j hj θ Ex Ey Hx Hy).electric (h + plateDesignThickness k j) =
        2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * Ex -
          ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2) * Ey ∧
    (losslessPlateXLayer k h j hj θ Ex Ey Hx Hy).magnetic (h + plateDesignThickness k j) =
        ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2) * Hx +
          2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * Hy ∧
    (losslessPlateYLayer k h j hj θ Ex Ey Hx Hy).magnetic (h + plateDesignThickness k j) =
        2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * Hx -
          ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2) * Hy := by
  have ha := losslessPlateDesign_active_field_boundary k hk j hj
    ((Real.cos θ : ℂ) * Ex + (Real.sin θ : ℂ) * Ey)
    ((Real.cos θ : ℂ) * Hx + (Real.sin θ : ℂ) * Hy)
  have hv := losslessPlateDesign_vacuum_field_boundary k hk j hj
    (-(Real.sin θ : ℂ) * Ex + (Real.cos θ : ℂ) * Ey)
    (-(Real.sin θ : ℂ) * Hx + (Real.cos θ : ℂ) * Hy)
  simp only [losslessPlateXLayer, losslessPlateYLayer, losslessPlateActiveLayer, losslessPlateVacuumLayer,
    PlanarLayerField.add, PlanarLayerField.const_mul, homogeneousPlanarLayerField, add_sub_cancel_left]
  rw [ha.1, hv.1, ha.2, hv.2]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem losslessPlateCartesian_current_rankOne (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (θ : ℝ)
    (Ex Ey Hx Hy : ℂ) (z : ℝ) :
    (losslessPlateXLayer k h j hj θ Ex Ey Hx Hy).current z =
      (Real.cos θ : ℂ) * ((plateDesignPermittivity j - 1 : ℝ) : ℂ) *
        (losslessPlateActiveLayer k h j hj θ Ex Ey Hx Hy).electric z ∧
    (losslessPlateYLayer k h j hj θ Ex Ey Hx Hy).current z =
      (Real.sin θ : ℂ) * ((plateDesignPermittivity j - 1 : ℝ) : ℂ) *
        (losslessPlateActiveLayer k h j hj θ Ex Ey Hx Hy).electric z := by
  simp only [losslessPlateXLayer, losslessPlateYLayer, losslessPlateActiveLayer, losslessPlateVacuumLayer,
    PlanarLayerField.add, PlanarLayerField.const_mul, homogeneousPlanarLayerField,
    plateDesignPermittivity, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one,
    one_pow, sub_self, zero_mul, mul_zero, add_zero]
  constructor <;> ring

theorem losslessPlateCartesian_active_projection (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (θ : ℝ)
    (Ex Ey Hx Hy : ℂ) (z : ℝ) :
    (Real.cos θ : ℂ) * (losslessPlateXLayer k h j hj θ Ex Ey Hx Hy).electric z +
      (Real.sin θ : ℂ) * (losslessPlateYLayer k h j hj θ Ex Ey Hx Hy).electric z =
        (losslessPlateActiveLayer k h j hj θ Ex Ey Hx Hy).electric z := by
  have hc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  simp only [losslessPlateXLayer, losslessPlateYLayer, PlanarLayerField.add, PlanarLayerField.const_mul]
  linear_combination (losslessPlateActiveLayer k h j hj θ Ex Ey Hx Hy).electric z * hc

end OQ7Prescribed
