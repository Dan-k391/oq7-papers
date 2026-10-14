import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace OQ7Mission.RationalOverlap
open scoped Matrix

/-- Actual real matrices for the exact overlap certificate at alpha = 3/5.
These definitions and the identities below certify this one point only. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def B : Mat2 := (1 / 190 : ℝ) •
  !![139, 17 * Real.sqrt 21; 17 * Real.sqrt 21, 71]

def W : Mat2 := !![9 / 10, 0; 0, -1 / 10]

def Z : Mat2 :=
  !![7 / 8, -17 * Real.sqrt 21 / 168; -17 * Real.sqrt 21 / 168, 3 / 8]

def E : Mat2 := !![0, 1 / 2; 1 / 2, 0]

def nu : ℝ := -19 * Real.sqrt 21 / 42

def H : Mat2 := (1 / 8 : ℝ) •
  !![7, Real.sqrt 21; Real.sqrt 21, 3]

theorem sqrt21_sq : (Real.sqrt 21) ^ 2 = 21 := by
  exact Real.sq_sqrt (by norm_num)

/-- The Lyapunov identity is checked entrywise on the defined matrices. -/
theorem lyapunov_identity : B * Z + Z * B = W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, Z, W, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (ring_nf <;> nlinarith [sqrt21_sq])

theorem determinant_Z : Z.det = 19 / 168 := by
  norm_num [Z, Matrix.det_fin_two]
  ring_nf
  nlinarith [sqrt21_sq]

theorem H_identity : H = Z - nu • E := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H, Z, nu, E] <;> ring

/-- Explicit square of the positive square root used in the certificate. -/
theorem B_square : B ^ 2 =
    !![2539 / 3610, 357 * Real.sqrt 21 / 3610;
       357 * Real.sqrt 21 / 3610, 1111 / 3610] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (ring_nf <;> nlinarith [sqrt21_sq])

theorem complement_identity : (1 : Mat2) - B ^ 2 =
    (357 / 3610 : ℝ) • !![3, -Real.sqrt 21; -Real.sqrt 21, 7] := by
  rw [B_square]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

/-- Complementary slackness for this actual matrix pair. -/
theorem complementary_slackness : H * ((1 : Mat2) - B ^ 2) = 0 := by
  rw [complement_identity]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (ring_nf <;> nlinarith [sqrt21_sq])

theorem weighted_trace : (W * B).trace = 59 / 95 := by
  norm_num [W, B, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem contrast : 2 * (3 / 5 : ℝ) * (B ^ 2) 0 1 =
    1071 * Real.sqrt 21 / 9025 := by
  rw [B_square]
  norm_num
  ring

private theorem B_hermitian : B.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B, Matrix.conjTranspose_apply]

private theorem Z_hermitian : Z.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z, Matrix.conjTranspose_apply]

private theorem H_hermitian : H.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]

theorem B_quadratic_form (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (B *ᵥ v) =
      (139 / 190 : ℝ) * (v 0 + 17 * Real.sqrt 21 / 139 * v 1) ^ 2 +
      (20 / 139 : ℝ) * (v 1) ^ 2 := by
  simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf
  nlinarith [sqrt21_sq]

theorem B_posSemidef : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg B_hermitian
  intro v
  rw [B_quadratic_form]
  positivity

theorem Z_quadratic_form (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (Z *ᵥ v) =
      (7 / 8 : ℝ) * (v 0 - 17 * Real.sqrt 21 / 147 * v 1) ^ 2 +
      (19 / 147 : ℝ) * (v 1) ^ 2 := by
  simp [Z, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf
  nlinarith [sqrt21_sq]

theorem Z_posSemidef : Z.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Z_hermitian
  intro v
  rw [Z_quadratic_form]
  positivity

theorem H_quadratic_form (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (H *ᵥ v) =
      (1 / 56 : ℝ) * (7 * v 0 + Real.sqrt 21 * v 1) ^ 2 := by
  simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf
  nlinarith [sqrt21_sq]

theorem H_posSemidef : H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg H_hermitian
  intro v
  rw [H_quadratic_form]
  positivity

theorem complement_quadratic_form (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (((1 : Mat2) - B ^ 2) *ᵥ v) =
      (119 / 3610 : ℝ) * (3 * v 0 - Real.sqrt 21 * v 1) ^ 2 := by
  rw [complement_identity]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf
  nlinarith [sqrt21_sq]

/-- The contraction inequality B^2 <= I, stated in the matrix PSD order. -/
theorem B_square_contraction : ((1 : Mat2) - B ^ 2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [complement_identity]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro v
    rw [complement_quadratic_form]
    positivity

theorem B_square_posSemidef : (B ^ 2).PosSemidef := B_posSemidef.pow 2

/-- An assumption-free certificate for the one explicitly defined overlap
point. This does not assert a global optimum or a physical realization. -/
theorem exact_certificate :
    B.PosSemidef ∧ (B ^ 2).PosSemidef ∧ ((1 : Mat2) - B ^ 2).PosSemidef ∧
    Z.PosSemidef ∧ H.PosSemidef ∧ B * Z + Z * B = W ∧
    Z.det = 19 / 168 ∧ H = Z - nu • E ∧
    H * ((1 : Mat2) - B ^ 2) = 0 ∧ (W * B).trace = 59 / 95 ∧
    2 * (3 / 5 : ℝ) * (B ^ 2) 0 1 = 1071 * Real.sqrt 21 / 9025 := by
  exact ⟨B_posSemidef, B_square_posSemidef, B_square_contraction,
    Z_posSemidef, H_posSemidef, lyapunov_identity, determinant_Z,
    H_identity, complementary_slackness, weighted_trace, contrast⟩

/-- The positive trace pairing with Z is evaluated by its exact two-square
decomposition. The matrix M need not be symmetric for this identity. -/
theorem trace_Z_mul (M : Mat2) :
    (Z * M).trace =
      (7 / 8 : ℝ) *
        (star ![1, -17 * Real.sqrt 21 / 147] ⬝ᵥ
          (M *ᵥ ![1, -17 * Real.sqrt 21 / 147])) +
      (19 / 147 : ℝ) * M 1 1 := by
  simp [Z, Matrix.trace_fin_two, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]
  ring_nf
  simp only [sqrt21_sq]
  ring

theorem trace_Z_mul_nonneg {M : Mat2} (hM : M.PosSemidef) :
    0 ≤ (Z * M).trace := by
  rw [trace_Z_mul]
  have hv := hM.dotProduct_mulVec_nonneg ![1, -17 * Real.sqrt 21 / 147]
  have hd : 0 ≤ M 1 1 := hM.diag_nonneg
  positivity

/-- The positive trace pairing with the rank-one dual slack H. -/
theorem trace_H_mul (M : Mat2) :
    (H * M).trace =
      (1 / 56 : ℝ) *
        (star ![7, Real.sqrt 21] ⬝ᵥ (M *ᵥ ![7, Real.sqrt 21])) := by
  simp [H, Matrix.trace_fin_two, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]
  ring_nf
  simp only [sqrt21_sq]
  ring

theorem trace_H_mul_nonneg {M : Mat2} (hM : M.PosSemidef) :
    0 ≤ (H * M).trace := by
  rw [trace_H_mul]
  have hv := hM.dotProduct_mulVec_nonneg ![7, Real.sqrt 21]
  positivity

/-- The exact dual-certificate identity for arbitrary real symmetric matrices.
The three trace terms on the left are the relaxation slack, contraction slack,
and square-root displacement. -/
theorem dual_trace_identity (A Q : Mat2) (hA : A.IsHermitian)
    (hQ : Q.IsHermitian) :
    (Z * (Q - A ^ 2)).trace + (H * ((1 : Mat2) - Q)).trace +
      (Z * ((A - B) ^ 2)).trace =
    nu * (Q 0 1 - (B ^ 2) 0 1) + 59 / 95 - (W * A).trace := by
  have hAoff : A 1 0 = A 0 1 := by simpa using hA.apply 0 1
  have hQoff : Q 1 0 = Q 0 1 := by simpa using hQ.apply 0 1
  simp [B, Z, H, nu, W, pow_two, Matrix.trace_fin_two, Matrix.mul_apply,
    Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, hAoff, hQoff]
  ring_nf
  simp only [sqrt21_sq]
  ring

/-- The exact upper bound for the real symmetric lifted SDP at the rational
target tr(W A) = 59/95. All positivity assumptions are on the optimization
variables, and the bound is derived from the explicit certificate above. -/
theorem rational_SDP_upper_bound (A Q : Mat2) (hA : A.IsHermitian)
    (hQ : Q.IsHermitian) (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (W * A).trace = 59 / 95) :
    2 * (3 / 5 : ℝ) * Q 0 1 ≤ 1071 * Real.sqrt 21 / 9025 := by
  have hD : (A - B).IsHermitian := hA.sub B_hermitian
  have hDD : ((A - B) ^ 2).PosSemidef := by
    simpa only [pow_two, hD.eq] using
      Matrix.posSemidef_conjTranspose_mul_self (A - B)
  have hn := add_nonneg
    (add_nonneg (trace_Z_mul_nonneg hrelax) (trace_H_mul_nonneg hcontract))
    (trace_Z_mul_nonneg hDD)
  rw [dual_trace_identity A Q hA hQ, htarget] at hn
  have hnu : nu < 0 := by
    have hs : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
    dsimp [nu]
    nlinarith
  have hentry : Q 0 1 ≤ (B ^ 2) 0 1 := by nlinarith
  calc
    2 * (3 / 5 : ℝ) * Q 0 1 ≤ 2 * (3 / 5 : ℝ) * (B ^ 2) 0 1 := by
      exact mul_le_mul_of_nonneg_left hentry (by norm_num)
    _ = 1071 * Real.sqrt 21 / 9025 := contrast

/-- The relaxation at the rational target attains this upper bound at A=B,
Q=B^2. This is an optimization statement for the stated real matrix SDP,
not a canonical reduction or a realization theorem for a physical structure. -/
theorem rational_SDP_attainment :
    ∃ A Q : Mat2, A.IsHermitian ∧ Q.IsHermitian ∧
      (Q - A ^ 2).PosSemidef ∧ ((1 : Mat2) - Q).PosSemidef ∧
      (W * A).trace = 59 / 95 ∧
      2 * (3 / 5 : ℝ) * Q 0 1 = 1071 * Real.sqrt 21 / 9025 := by
  refine ⟨B, B ^ 2, B_hermitian, B_square_posSemidef.1, ?_,
    B_square_contraction, weighted_trace, contrast⟩
  simpa using (Matrix.PosSemidef.zero : (0 : Mat2).PosSemidef)

/-- The upper bound also holds in the original square-root matrix variables,
where the lifted matrix is fixed to Q=A^2. -/
theorem rational_square_upper_bound (A : Mat2) (hA : A.IsHermitian)
    (hcontract : ((1 : Mat2) - A ^ 2).PosSemidef)
    (htarget : (W * A).trace = 59 / 95) :
    2 * (3 / 5 : ℝ) * (A ^ 2) 0 1 ≤ 1071 * Real.sqrt 21 / 9025 := by
  have hsq : (A ^ 2).PosSemidef := by
    simpa only [pow_two, hA.eq] using Matrix.posSemidef_conjTranspose_mul_self A
  apply rational_SDP_upper_bound A (A ^ 2) hA hsq.1 _ hcontract htarget
  simpa using (Matrix.PosSemidef.zero : (0 : Mat2).PosSemidef)

#print axioms lyapunov_identity
#print axioms determinant_Z
#print axioms H_identity
#print axioms B_square
#print axioms complement_identity
#print axioms complementary_slackness
#print axioms weighted_trace
#print axioms contrast
#print axioms B_posSemidef
#print axioms Z_posSemidef
#print axioms H_posSemidef
#print axioms B_square_contraction
#print axioms B_square_posSemidef
#print axioms exact_certificate
#print axioms trace_Z_mul
#print axioms trace_Z_mul_nonneg
#print axioms trace_H_mul
#print axioms trace_H_mul_nonneg
#print axioms dual_trace_identity
#print axioms rational_SDP_upper_bound
#print axioms rational_SDP_attainment
#print axioms rational_square_upper_bound
end OQ7Mission.RationalOverlap
