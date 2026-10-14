import PrescribedExtinction.PlanarLosslessPlate
import PrescribedExtinction.PlanarLayerField
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open scoped Matrix

theorem losslessPlateDesign_active_field_boundary (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j)
    (E H : ℂ) :
    OQ7.electricField k (plateDesignIndex j : ℂ) E H (plateDesignThickness k j) = E ∧
    OQ7.magneticField k (plateDesignIndex j : ℂ) E H (plateDesignThickness k j) = H := by
  have he := OQ7.homogeneousField_transfer k (plateDesignIndex j : ℂ) E H (plateDesignThickness k j)
  rw [losslessPlateDesign_active_transfer k hk j hj, Matrix.one_mulVec] at he
  constructor
  · exact (congrArg (fun v : Fin 2 → ℂ => v 0) he).symm
  · exact (congrArg (fun v : Fin 2 → ℂ => v 1) he).symm

theorem losslessPlateDesign_vacuum_field_boundary (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j)
    (E H : ℂ) :
    OQ7.electricField k 1 E H (plateDesignThickness k j) = -E ∧
    OQ7.magneticField k 1 E H (plateDesignThickness k j) = -H := by
  have he := OQ7.homogeneousField_transfer k 1 E H (plateDesignThickness k j)
  rw [losslessPlateDesign_vacuum_transfer k hk j hj, Matrix.neg_mulVec, Matrix.one_mulVec] at he
  constructor
  · exact (congrArg (fun v : Fin 2 → ℂ => v 0) he).symm
  · exact (congrArg (fun v : Fin 2 → ℂ => v 1) he).symm

def losslessPlateActiveLayer (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (θ : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  homogeneousPlanarLayerField k h _ h (plateDesignIndex j : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans (plateDesignIndex_gt_one j hj))))
    ((Real.cos θ : ℂ) * Ex + (Real.sin θ : ℂ) * Ey)
    ((Real.cos θ : ℂ) * Hx + (Real.sin θ : ℂ) * Hy)

def losslessPlateVacuumLayer (k h : ℝ) (j : ℕ) (θ : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  homogeneousPlanarLayerField k h _ h 1 (by norm_num)
    (-(Real.sin θ : ℂ) * Ex + (Real.cos θ : ℂ) * Ey)
    (-(Real.sin θ : ℂ) * Hx + (Real.cos θ : ℂ) * Hy)

def losslessPlateXLayer (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (θ : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  ((losslessPlateActiveLayer k h j hj θ Ex Ey Hx Hy).const_mul (Real.cos θ : ℂ)).add
    ((losslessPlateVacuumLayer k h j θ Ex Ey Hx Hy).const_mul (-(Real.sin θ : ℂ)))

def losslessPlateYLayer (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (θ : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  ((losslessPlateActiveLayer k h j hj θ Ex Ey Hx Hy).const_mul (Real.sin θ : ℂ)).add
    ((losslessPlateVacuumLayer k h j θ Ex Ey Hx Hy).const_mul (Real.cos θ : ℂ))

theorem losslessPlateCartesian_initial (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (θ : ℝ) (Ex Ey Hx Hy : ℂ) :
    (losslessPlateXLayer k h j hj θ Ex Ey Hx Hy).electric h = Ex ∧
    (losslessPlateYLayer k h j hj θ Ex Ey Hx Hy).electric h = Ey ∧
    (losslessPlateXLayer k h j hj θ Ex Ey Hx Hy).magnetic h = Hx ∧
    (losslessPlateYLayer k h j hj θ Ex Ey Hx Hy).magnetic h = Hy := by
  have hc : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  simp only [losslessPlateXLayer, losslessPlateYLayer, losslessPlateActiveLayer, losslessPlateVacuumLayer,
    PlanarLayerField.add, PlanarLayerField.const_mul, homogeneousPlanarLayerField,
    sub_self, OQ7.electricField, OQ7.magneticField, Complex.ofReal_zero, mul_zero,
    Complex.cos_zero, Complex.sin_zero, mul_one, zero_div, add_zero, zero_add]
  constructor
  · linear_combination Ex * hc
  constructor
  · linear_combination Ey * hc
  constructor
  · linear_combination Hx * hc
  · linear_combination Hy * hc

end OQ7Prescribed
