import GeneralizedResearch.MiddleCertificate

/-! Literal original Proposition 6.1 orthogonal-input sharpness construction,
including zero/full-extinction endpoints and either sign of forward overlap. -/
noncomputable section
open scoped Matrix
namespace GeneralizedResearch
namespace OrthogonalSharpness
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
def a : Fin 3 → ℝ := ![1, 0, 0]
def b : Fin 3 → ℝ := ![0, 1, 0]
def s (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
def S (t : ℝ) : Mat3 := !![0, t, 0; t, 0, s t; 0, s t, 0]
def S0 : Mat3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
def defectVector (t : ℝ) : Fin 3 → ℝ := ![s t, 0, -t]

theorem s_sq {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) : (s t) ^ 2 = 1 - t ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem S_symmetric (t : ℝ) : (S t).transpose = S t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]

theorem gram_defect {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (1 : Mat3) - (S t).transpose * S t =
      Matrix.vecMulVec (defectVector t) (defectVector t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, defectVector, Matrix.vecMulVec, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals nlinarith [s_sq ht0 ht1]

theorem contraction {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    ((1 : Mat3) - (S t).transpose * S t).PosSemidef := by
  rw [gram_defect ht0 ht1]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.vecMulVec, Matrix.conjTranspose_apply, mul_comm]
  · intro v
    simp [defectVector, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (s t * v 0 - t * v 2)]

theorem S0_symmetric : S0.transpose = S0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [S0]

theorem S0_square : S0 ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S0, pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem reversal : S0 *ᵥ a = b := by
  ext i
  fin_cases i <;> simp [S0, a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem unit_orthogonal : a ⬝ᵥ a = 1 ∧ b ⬝ᵥ b = 1 ∧ a ⬝ᵥ b = 0 := by
  norm_num [a, b, dotProduct, Fin.sum_univ_three]

theorem forward_overlap (t : ℝ) : (S0 *ᵥ a) ⬝ᵥ (S t *ᵥ a) = t := by
  simp [S0, S, a, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem absorption_difference {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (S t *ᵥ b) ⬝ᵥ (S t *ᵥ b) - (S t *ᵥ a) ⬝ᵥ (S t *ᵥ a) = 1 - t ^ 2 := by
  simp [S, a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  nlinarith [s_sq ht0 ht1]

theorem orthogonal_sharpness {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (S t).transpose = S t ∧ ((1 : Mat3) - (S t).transpose * S t).PosSemidef ∧
      S0.transpose = S0 ∧ S0 ^ 2 = 1 ∧ S0 *ᵥ a = b ∧
      a ⬝ᵥ a = 1 ∧ b ⬝ᵥ b = 1 ∧ a ⬝ᵥ b = 0 ∧
      (S0 *ᵥ a) ⬝ᵥ (S t *ᵥ a) = t ∧
      (S t *ᵥ b) ⬝ᵥ (S t *ᵥ b) - (S t *ᵥ a) ⬝ᵥ (S t *ᵥ a) = 1 - t ^ 2 :=
  ⟨S_symmetric t, contraction ht0 ht1, S0_symmetric, S0_square, reversal,
    unit_orthogonal.1, unit_orthogonal.2.1, unit_orthogonal.2.2,
    forward_overlap t, absorption_difference ht0 ht1⟩

#print axioms orthogonal_sharpness
end OrthogonalSharpness
end GeneralizedResearch
