import GeneralizedResearch.MiddleCertificate

/-! # Explicit three-channel reciprocal equality operator

All matrices and inputs are actual finite real matrices and vectors. The
background is also explicitly a symmetric orthogonal matrix, and maps the
first input to its paired time reverse. -/
noncomputable section
open scoped Matrix
namespace GeneralizedResearch
namespace ThirdBranch
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

structure Parameters where
  rho : ℝ
  r : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  rho_le_r : rho ≤ r
  r_le_one : r ≤ 1

namespace Parameters

def x (p : Parameters) : ℝ := Real.sqrt (p.r ^ 2 - p.rho ^ 2)
def y (p : Parameters) : ℝ := Real.sqrt (1 - p.r ^ 2)
def a : Fin 3 → ℝ := ![1, 0, 0]
def b (p : Parameters) : Fin 3 → ℝ := ![p.rho, p.x, p.y]
def S (p : Parameters) : Mat3 :=
  !![p.rho / p.r, p.x / p.r, 0; p.x / p.r, -p.rho / p.r, 0; 0, 0, 0]
def S0 (p : Parameters) : Mat3 :=
  !![p.rho, p.x, p.y;
    p.x, 1 - p.x ^ 2 / (1 - p.rho), -p.x * p.y / (1 - p.rho);
    p.y, -p.x * p.y / (1 - p.rho), 1 - p.y ^ 2 / (1 - p.rho)]

theorem r_pos (p : Parameters) : 0 < p.r := p.rho_pos.trans_le p.rho_le_r
theorem x_sq (p : Parameters) : p.x ^ 2 = p.r ^ 2 - p.rho ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [p.r_pos, p.rho_pos, p.rho_le_r]
theorem y_sq (p : Parameters) : p.y ^ 2 = 1 - p.r ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [p.r_pos, p.r_le_one]

theorem input_norms (p : Parameters) : a ⬝ᵥ a = 1 ∧ p.b ⬝ᵥ p.b = 1 := by
  simp [a, b, dotProduct, Fin.sum_univ_three]
  nlinarith [p.x_sq, p.y_sq]

theorem input_overlap (p : Parameters) : a ⬝ᵥ p.b = p.rho := by
  simp [a, b, dotProduct, Fin.sum_univ_three]

theorem S_symmetric (p : Parameters) : p.S.transpose = p.S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]

theorem S_gram (p : Parameters) : p.S.transpose * p.S =
    !![1, 0, 0; 0, 1, 0; 0, 0, 0] := by
  have hr := p.r_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [hr] <;> nlinarith [p.x_sq]

theorem S_contraction (p : Parameters) : ((1 : Mat3) - p.S.transpose * p.S).PosSemidef := by
  rw [p.S_gram]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro v
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 2)]

theorem S0_symmetric (p : Parameters) : p.S0.transpose = p.S0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S0]

theorem S0_square (p : Parameters) : p.S0 ^ 2 = 1 := by
  have hd : 1 - p.rho ≠ 0 := (sub_pos.mpr p.rho_lt_one).ne'
  have hxy : p.x ^ 2 + p.y ^ 2 = 1 - p.rho ^ 2 := by
    nlinarith [p.x_sq, p.y_sq]
  have hxyx := congrArg (fun z : ℝ => z * p.x) hxy
  have hxyy := congrArg (fun z : ℝ => z * p.y) hxy
  have hxyxx := congrArg (fun z : ℝ => z * p.x ^ 2) hxy
  have hxyyy := congrArg (fun z : ℝ => z * p.y ^ 2) hxy
  have hxyxy := congrArg (fun z : ℝ => z * p.x * p.y) hxy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S0, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [hd]
  all_goals nlinarith [hxy, hxyx, hxyy, hxyxx, hxyyy, hxyxy]

theorem background_reversal (p : Parameters) : p.S0 *ᵥ a = p.b := by
  ext i
  fin_cases i <;> simp [S0, a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem S_b (p : Parameters) : p.S *ᵥ p.b = p.r • a := by
  have hr := p.r_pos.ne'
  ext i
  fin_cases i <;> simp [S, b, a, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals field_simp [hr] <;> nlinarith [p.x_sq]

theorem S_a_norm (p : Parameters) : (p.S *ᵥ a) ⬝ᵥ (p.S *ᵥ a) = 1 := by
  have hr := p.r_pos.ne'
  simp [S, a, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  field_simp [hr]
  nlinarith [p.x_sq]

theorem forward_overlap (p : Parameters) : p.b ⬝ᵥ (p.S *ᵥ a) = p.r := by
  have hr := p.r_pos.ne'
  simp [S, b, a, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  field_simp [hr]
  nlinarith [p.x_sq]

theorem absorption_difference (p : Parameters) :
    (p.S *ᵥ a) ⬝ᵥ (p.S *ᵥ a) -
      (p.S *ᵥ p.b) ⬝ᵥ (p.S *ᵥ p.b) = 1 - p.r ^ 2 := by
  rw [p.S_a_norm, p.S_b]
  simp [a, dotProduct, Fin.sum_univ_three, pow_two]

/-- Every parameter in the complete closed third branch has an explicit
reciprocal contraction, a lossless reciprocal background, unit paired inputs,
the exact signed forward overlap, and the claimed equality difference. -/
theorem third_branch_attainment (p : Parameters) :
    p.S.transpose = p.S ∧ ((1 : Mat3) - p.S.transpose * p.S).PosSemidef ∧
      p.S0.transpose = p.S0 ∧ p.S0 ^ 2 = 1 ∧ p.S0 *ᵥ a = p.b ∧
      a ⬝ᵥ a = 1 ∧ p.b ⬝ᵥ p.b = 1 ∧ a ⬝ᵥ p.b = p.rho ∧
      p.b ⬝ᵥ (p.S *ᵥ a) = p.r ∧
      (p.S *ᵥ a) ⬝ᵥ (p.S *ᵥ a) -
        (p.S *ᵥ p.b) ⬝ᵥ (p.S *ᵥ p.b) = 1 - p.r ^ 2 :=
  ⟨p.S_symmetric, p.S_contraction, p.S0_symmetric, p.S0_square,
    p.background_reversal, p.input_norms.1, p.input_norms.2,
    p.input_overlap, p.forward_overlap, p.absorption_difference⟩

#print axioms S0_square
#print axioms third_branch_attainment
end Parameters
end ThirdBranch
end GeneralizedResearch
