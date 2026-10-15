import PrescribedExtinction.PlanarPlateJones
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! An arbitrary-angle lossless plate with literal homogeneous Maxwell fields.
The coefficient parametrization realizes the precise Jones matrix used by the
generalized manuscript without assuming an abstract scattering plate exists. -/
noncomputable section
namespace GeneralizedResearch
namespace PlanarPlateBridge
open OQ7Prescribed
open scoped Matrix

def coeffU (t : ℝ) : ℝ := Real.sqrt ((1 + t) / 2)
def coeffV (t : ℝ) : ℝ := -Real.sqrt ((1 - t) / 2)
def s (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
def principal (t : ℝ) : Fin 2 → ℝ := ![coeffU t, coeffV t]
def perpendicular (t : ℝ) : Fin 2 → ℝ := ![-coeffV t, coeffU t]
def H (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t, -s t; -s t, -t]
def V (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := -H t
def susceptibility (j : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (plateDesignPermittivity j - 1) • Matrix.vecMulVec (principal t) (principal t)
def tensor (j : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := 1 + susceptibility j t

theorem coefficient_properties {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    coeffU t ^ 2 = (1 + t) / 2 ∧ coeffV t ^ 2 = (1 - t) / 2 ∧
    coeffU t ^ 2 + coeffV t ^ 2 = 1 ∧ coeffU t ^ 2 - coeffV t ^ 2 = t ∧
    2 * coeffU t * coeffV t = -s t := by
  have hu : coeffU t ^ 2 = (1 + t) / 2 := Real.sq_sqrt (by linarith)
  have hv : coeffV t ^ 2 = (1 - t) / 2 := by
    unfold coeffV
    rw [neg_sq, Real.sq_sqrt (by linarith)]
  have hp : coeffU t * (-coeffV t) = s t / 2 := by
    unfold coeffU coeffV s
    rw [neg_neg, ← Real.sqrt_mul (by linarith : 0 ≤ (1 + t) / 2)]
    have heq : ((1 + t) / 2) * ((1 - t) / 2) = (1 - t ^ 2) / 4 := by ring
    rw [heq, Real.sqrt_div (by nlinarith) 4]
    norm_num
  exact ⟨hu, hv, by linarith, by linarith, by linarith⟩

theorem coefficient_complex {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (coeffU t : ℂ) ^ 2 + (coeffV t : ℂ) ^ 2 = 1 ∧
    (coeffU t : ℂ) ^ 2 - (coeffV t : ℂ) ^ 2 = (t : ℂ) ∧
    2 * (coeffU t : ℂ) * (coeffV t : ℂ) = -(s t : ℂ) := by
  have hp := coefficient_properties ht0 ht1
  exact ⟨by exact_mod_cast hp.2.2.1, by exact_mod_cast hp.2.2.2.1,
    by exact_mod_cast hp.2.2.2.2⟩

def activeLayer (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  homogeneousPlanarLayerField k h _ h (plateDesignIndex j : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt
      ((by norm_num : (0 : ℝ) < 1).trans (plateDesignIndex_gt_one j hj))))
    ((coeffU t : ℂ) * Ex + (coeffV t : ℂ) * Ey)
    ((coeffU t : ℂ) * Hx + (coeffV t : ℂ) * Hy)

def vacuumLayer (k h : ℝ) (j : ℕ) (t : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  homogeneousPlanarLayerField k h _ h 1 (by norm_num)
    (-(coeffV t : ℂ) * Ex + (coeffU t : ℂ) * Ey)
    (-(coeffV t : ℂ) * Hx + (coeffU t : ℂ) * Hy)

def xLayer (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  ((activeLayer k h j hj t Ex Ey Hx Hy).const_mul (coeffU t : ℂ)).add
    ((vacuumLayer k h j t Ex Ey Hx Hy).const_mul (-(coeffV t : ℂ)))

def yLayer (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (Ex Ey Hx Hy : ℂ) :
    PlanarLayerField k h (h + plateDesignThickness k j) :=
  ((activeLayer k h j hj t Ex Ey Hx Hy).const_mul (coeffV t : ℂ)).add
    ((vacuumLayer k h j t Ex Ey Hx Hy).const_mul (coeffU t : ℂ))

theorem initial_boundary (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (Ex Ey Hx Hy : ℂ) :
    (xLayer k h j hj t Ex Ey Hx Hy).electric h = Ex ∧
    (yLayer k h j hj t Ex Ey Hx Hy).electric h = Ey ∧
    (xLayer k h j hj t Ex Ey Hx Hy).magnetic h = Hx ∧
    (yLayer k h j hj t Ex Ey Hx Hy).magnetic h = Hy := by
  have hc := (coefficient_complex ht0 ht1).1
  simp only [xLayer, yLayer, activeLayer, vacuumLayer, PlanarLayerField.add,
    PlanarLayerField.const_mul, homogeneousPlanarLayerField, sub_self,
    OQ7.electricField, OQ7.magneticField, Complex.ofReal_zero, mul_zero,
    Complex.cos_zero, Complex.sin_zero, mul_one, zero_div, add_zero, zero_add]
  constructor
  · linear_combination Ex * hc
  constructor
  · linear_combination Ey * hc
  constructor
  · linear_combination Hx * hc
  · linear_combination Hy * hc

theorem final_boundary (k : ℝ) (hk : 0 < k) (h : ℝ) (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (Ex Ey Hx Hy : ℂ) :
    (xLayer k h j hj t Ex Ey Hx Hy).electric (h + plateDesignThickness k j) =
      (t : ℂ) * Ex - (s t : ℂ) * Ey ∧
    (yLayer k h j hj t Ex Ey Hx Hy).electric (h + plateDesignThickness k j) =
      -(s t : ℂ) * Ex - (t : ℂ) * Ey ∧
    (xLayer k h j hj t Ex Ey Hx Hy).magnetic (h + plateDesignThickness k j) =
      (t : ℂ) * Hx - (s t : ℂ) * Hy ∧
    (yLayer k h j hj t Ex Ey Hx Hy).magnetic (h + plateDesignThickness k j) =
      -(s t : ℂ) * Hx - (t : ℂ) * Hy := by
  have hc := coefficient_complex ht0 ht1
  have ha := losslessPlateDesign_active_field_boundary k hk j hj
    ((coeffU t : ℂ) * Ex + (coeffV t : ℂ) * Ey)
    ((coeffU t : ℂ) * Hx + (coeffV t : ℂ) * Hy)
  have hv := losslessPlateDesign_vacuum_field_boundary k hk j hj
    (-(coeffV t : ℂ) * Ex + (coeffU t : ℂ) * Ey)
    (-(coeffV t : ℂ) * Hx + (coeffU t : ℂ) * Hy)
  simp only [xLayer, yLayer, activeLayer, vacuumLayer, PlanarLayerField.add,
    PlanarLayerField.const_mul, homogeneousPlanarLayerField, add_sub_cancel_left]
  rw [ha.1, hv.1, ha.2, hv.2]
  constructor
  · linear_combination Ex * hc.2.1 + Ey * hc.2.2
  constructor
  · linear_combination Ex * hc.2.2 - Ey * hc.2.1
  constructor
  · linear_combination Hx * hc.2.1 + Hy * hc.2.2
  · linear_combination Hx * hc.2.2 - Hy * hc.2.1

theorem active_projection (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (Ex Ey Hx Hy : ℂ) (z : ℝ) :
    (coeffU t : ℂ) * (xLayer k h j hj t Ex Ey Hx Hy).electric z +
      (coeffV t : ℂ) * (yLayer k h j hj t Ex Ey Hx Hy).electric z =
        (activeLayer k h j hj t Ex Ey Hx Hy).electric z := by
  have hc := (coefficient_complex ht0 ht1).1
  simp only [xLayer, yLayer, PlanarLayerField.add, PlanarLayerField.const_mul]
  linear_combination (activeLayer k h j hj t Ex Ey Hx Hy).electric z * hc

theorem current_rankOne (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) (t : ℝ)
    (Ex Ey Hx Hy : ℂ) (z : ℝ) :
    (xLayer k h j hj t Ex Ey Hx Hy).current z =
      (coeffU t : ℂ) * ((plateDesignPermittivity j - 1 : ℝ) : ℂ) *
        (activeLayer k h j hj t Ex Ey Hx Hy).electric z ∧
    (yLayer k h j hj t Ex Ey Hx Hy).current z =
      (coeffV t : ℂ) * ((plateDesignPermittivity j - 1 : ℝ) : ℂ) *
        (activeLayer k h j hj t Ex Ey Hx Hy).electric z := by
  simp only [xLayer, yLayer, activeLayer, vacuumLayer, PlanarLayerField.add,
    PlanarLayerField.const_mul, homogeneousPlanarLayerField, plateDesignPermittivity,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one,
    one_pow, sub_self, zero_mul, mul_zero, add_zero]
  constructor <;> ring

theorem constitutive_current (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (Ex Ey Hx Hy : ℂ) (z : ℝ) :
    ![(xLayer k h j hj t Ex Ey Hx Hy).current z,
      (yLayer k h j hj t Ex Ey Hx Hy).current z] =
      (fun i l => (susceptibility j t i l : ℂ)) *ᵥ
        ![(xLayer k h j hj t Ex Ey Hx Hy).electric z,
          (yLayer k h j hj t Ex Ey Hx Hy).electric z] := by
  have ha := active_projection k h j hj ht0 ht1 Ex Ey Hx Hy z
  have hc := current_rankOne k h j hj t Ex Ey Hx Hy z
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, susceptibility, principal]
  · rw [hc.1, ← ha]
    push_cast
    ring
  · rw [hc.2, ← ha]
    push_cast
    ring

theorem tensor_symmetric (j : ℕ) (t : ℝ) : (tensor j t).transpose = tensor j t := by
  ext i l
  simp only [tensor, susceptibility, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hil : i = l
  · subst l
    rfl
  · rw [ite_eq_right hil, ite_eq_right (Ne.symm hil)]
    ring

theorem susceptibility_posSemidef (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    (susceptibility j t).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (principal t)
  simp only [star_trivial] at h
  exact h.smul (le_of_lt (plateDesignPermittivity_pos_susceptibility j hj))

theorem tensor_j1 {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    tensor 1 t = (1 / 2 : ℝ) • ((5 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - 3 • V t) := by
  have hp := coefficient_properties ht0 ht1
  have hj : plateDesignPermittivity 1 = 4 := by
    norm_num [plateDesignPermittivity, plateDesignIndex]
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [tensor, susceptibility, principal, H, V, hj]
  all_goals nlinarith [hp.1, hp.2.1, hp.2.2.2.2]

theorem projection_sum {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    Matrix.vecMulVec (principal t) (principal t) +
      Matrix.vecMulVec (perpendicular t) (perpendicular t) =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hc := (coefficient_properties ht0 ht1).2.2.1
  ext i l
  fin_cases i <;> fin_cases l <;> simp [principal, perpendicular]
  all_goals nlinarith

theorem tensor_spectral_decomposition {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    tensor j t = plateDesignPermittivity j • Matrix.vecMulVec (principal t) (principal t) +
      Matrix.vecMulVec (perpendicular t) (perpendicular t) := by
  unfold tensor susceptibility
  rw [← projection_sum ht0 ht1]
  module

/-- Real tensor eigenvalues lie between 1 and the chosen principal cap. -/
theorem tensor_bounds (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) {P : ℝ} (hP : plateDesignPermittivity j ≤ P) :
    (tensor j t - 1).PosSemidef ∧ (P • (1 : Matrix (Fin 2) (Fin 2) ℝ) - tensor j t).PosSemidef := by
  have hprincipal := Matrix.posSemidef_vecMulVec_self_star (principal t)
  have hperpendicular := Matrix.posSemidef_vecMulVec_self_star (perpendicular t)
  simp only [star_trivial] at hprincipal hperpendicular
  have hP1 : 1 ≤ P := by
    have hp := plateDesignPermittivity_pos_susceptibility j hj
    linarith
  constructor
  · simpa only [tensor, add_sub_cancel_left] using susceptibility_posSemidef j hj t
  · have heq : P • (1 : Matrix (Fin 2) (Fin 2) ℝ) - tensor j t =
        (P - plateDesignPermittivity j) • Matrix.vecMulVec (principal t) (principal t) +
          (P - 1) • Matrix.vecMulVec (perpendicular t) (perpendicular t) := by
      rw [tensor_spectral_decomposition ht0 ht1, ← projection_sum ht0 ht1]
      module
    rw [heq]
    exact (hprincipal.smul (sub_nonneg.mpr hP)).add
      (hperpendicular.smul (sub_nonneg.mpr hP1))

theorem tensor_bounds_j1 {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (tensor 1 t - 1).PosSemidef ∧
      ((4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - tensor 1 t).PosSemidef :=
  tensor_bounds 1 (by norm_num) ht0 ht1
    (by norm_num [plateDesignPermittivity, plateDesignIndex])

theorem exists_tensor_within_cap {P : ℝ} (hP : 1 < P) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    ∃ j : ℕ, 1 ≤ j ∧ (tensor j t - 1).PosSemidef ∧
      (P • (1 : Matrix (Fin 2) (Fin 2) ℝ) - tensor j t).PosSemidef := by
  obtain ⟨j, hj, hcap⟩ := exists_plateDesign_within_cap P hP
  exact ⟨j, hj, tensor_bounds j hj ht0 ht1 hcap⟩

theorem design_j1 (k : ℝ) : plateDesignIndex 1 = 2 ∧
    plateDesignPermittivity 1 = 4 ∧ plateDesignThickness k 1 = Real.pi / k := by
  norm_num [plateDesignIndex, plateDesignPermittivity, plateDesignThickness]

def principal3 (t : ℝ) : Fin 3 → ℝ := ![coeffU t, coeffV t, 0]
def perpendicular3 (t : ℝ) : Fin 3 → ℝ := ![-coeffV t, coeffU t, 0]
def vertical3 : Fin 3 → ℝ := ![0, 0, 1]
def tensor3 (j : ℕ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + (plateDesignPermittivity j - 1) • Matrix.vecMulVec (principal3 t) (principal3 t)

/-- The longitudinal permittivity is exactly vacuum, with no mixed entries. -/
theorem tensor3_components (j : ℕ) (t : ℝ) :
    tensor3 j t =
      !![tensor j t 0 0, tensor j t 0 1, 0;
         tensor j t 1 0, tensor j t 1 1, 0;
         0, 0, 1] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [tensor3, tensor, susceptibility, principal3, principal]

theorem tensor3_symmetric (j : ℕ) (t : ℝ) : (tensor3 j t).transpose = tensor3 j t := by
  ext i l
  simp only [tensor3, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hil : i = l
  · subst l
    rfl
  · rw [ite_eq_right hil, ite_eq_right (Ne.symm hil)]
    ring

theorem projection3_sum {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    Matrix.vecMulVec (principal3 t) (principal3 t) +
      Matrix.vecMulVec (perpendicular3 t) (perpendicular3 t) +
      Matrix.vecMulVec vertical3 vertical3 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hc := (coefficient_properties ht0 ht1).2.2.1
  ext i l
  fin_cases i <;> fin_cases l <;> simp [principal3, perpendicular3, vertical3]
  all_goals nlinarith

theorem tensor3_spectral_decomposition {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    tensor3 j t =
      plateDesignPermittivity j • Matrix.vecMulVec (principal3 t) (principal3 t) +
      Matrix.vecMulVec (perpendicular3 t) (perpendicular3 t) +
      Matrix.vecMulVec vertical3 vertical3 := by
  unfold tensor3
  rw [← projection3_sum ht0 ht1]
  module

/-- All three real principal permittivities satisfy the specified material cap. -/
theorem tensor3_bounds (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) {P : ℝ} (hP : plateDesignPermittivity j ≤ P) :
    (tensor3 j t - 1).PosSemidef ∧
      (P • (1 : Matrix (Fin 3) (Fin 3) ℝ) - tensor3 j t).PosSemidef := by
  have hprincipal := Matrix.posSemidef_vecMulVec_self_star (principal3 t)
  have hperpendicular := Matrix.posSemidef_vecMulVec_self_star (perpendicular3 t)
  have hvertical := Matrix.posSemidef_vecMulVec_self_star vertical3
  simp only [star_trivial] at hprincipal hperpendicular hvertical
  have hp := plateDesignPermittivity_pos_susceptibility j hj
  have hP1 : 1 ≤ P := by linarith
  constructor
  · simpa only [tensor3, add_sub_cancel_left] using hprincipal.smul (le_of_lt hp)
  · have heq : P • (1 : Matrix (Fin 3) (Fin 3) ℝ) - tensor3 j t =
        (P - plateDesignPermittivity j) • Matrix.vecMulVec (principal3 t) (principal3 t) +
          (P - 1) • Matrix.vecMulVec (perpendicular3 t) (perpendicular3 t) +
          (P - 1) • Matrix.vecMulVec vertical3 vertical3 := by
      rw [tensor3_spectral_decomposition ht0 ht1, ← projection3_sum ht0 ht1]
      module
    rw [heq]
    exact ((hprincipal.smul (sub_nonneg.mpr hP)).add
      (hperpendicular.smul (sub_nonneg.mpr hP1))).add
      (hvertical.smul (sub_nonneg.mpr hP1))

theorem tensor3_bounds_j1 {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (tensor3 1 t - 1).PosSemidef ∧
      ((4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - tensor3 1 t).PosSemidef :=
  tensor3_bounds 1 (by norm_num) ht0 ht1
    (by norm_num [plateDesignPermittivity, plateDesignIndex])

/-- Literal three-dimensional constitutive relation for the transverse plate
fields and their zero longitudinal components. -/
theorem constitutive_current3 (k h : ℝ) (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (Ex Ey Hx Hy : ℂ) (z : ℝ) :
    ![(xLayer k h j hj t Ex Ey Hx Hy).current z,
      (yLayer k h j hj t Ex Ey Hx Hy).current z, 0] =
      (fun i l => ((tensor3 j t - 1) i l : ℂ)) *ᵥ
        ![(xLayer k h j hj t Ex Ey Hx Hy).electric z,
          (yLayer k h j hj t Ex Ey Hx Hy).electric z, 0] := by
  have ha := active_projection k h j hj ht0 ht1 Ex Ey Hx Hy z
  have hc := current_rankOne k h j hj t Ex Ey Hx Hy z
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tensor3, principal3]
  · rw [hc.1, ← ha]
    push_cast
    ring
  · rw [hc.2, ← ha]
    push_cast
    ring

end PlanarPlateBridge
end GeneralizedResearch
