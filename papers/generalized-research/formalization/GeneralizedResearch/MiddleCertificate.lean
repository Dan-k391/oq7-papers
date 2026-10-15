import GeneralizedResearch.MiddleParameters
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # A continuously parameterized positive-matrix certificate

The matrices are written in the eigenbasis of `B₀` from original Theorem 7.1.
The objective is `trace(E Q)` and the extinction is `trace(W B)`. The
hypotheses on arbitrary competitors are exactly symmetry and the two PSD
inequalities `B² ≤ Q ≤ I`. No optimality conclusion occurs in a structure
field or hypothesis. -/

noncomputable section
open scoped Matrix
namespace GeneralizedResearch
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

namespace MiddleParameters

def B (p : MiddleParameters) : Mat2 := !![1, 0; 0, p.lambda]
def W (p : MiddleParameters) : Mat2 :=
  !![(p.rho + p.c) / 2, -p.s / 2; -p.s / 2, (p.rho - p.c) / 2]
def E (p : MiddleParameters) : Mat2 := !![p.s / 2, p.c / 2; p.c / 2, -p.s / 2]
def Z (p : MiddleParameters) : Mat2 :=
  !![(p.rho + p.c) / 4, -p.s / (2 * (1 + p.lambda));
     -p.s / (2 * (1 + p.lambda)), (p.rho - p.c) / (4 * p.lambda)]
def nu (p : MiddleParameters) : ℝ := -p.s / ((1 + p.lambda) * p.c)
def delta (p : MiddleParameters) : ℝ :=
  (p.rho + p.c) / 4 + p.s ^ 2 / (2 * (1 + p.lambda) * p.c)
def H (p : MiddleParameters) : Mat2 := !![p.delta, 0; 0, 0]

theorem B_hermitian (p : MiddleParameters) : p.B.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B, Matrix.conjTranspose_apply]

theorem Z_hermitian (p : MiddleParameters) : p.Z.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z, Matrix.conjTranspose_apply]

theorem H_hermitian (p : MiddleParameters) : p.H.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]

theorem nu_neg (p : MiddleParameters) : p.nu < 0 := by
  dsimp [nu]
  apply div_neg_of_neg_of_pos (neg_neg_of_pos p.s_pos)
  exact mul_pos (by linarith [p.lambda_pos]) p.c_pos

theorem delta_pos (p : MiddleParameters) : 0 < p.delta := by
  dsimp [delta]
  have hl := p.lambda_pos
  have hc := p.c_pos
  have hr := p.rho_pos
  positivity

theorem B_square (p : MiddleParameters) : p.B ^ 2 = !![1, 0; 0, p.lambda ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem lyapunov_identity (p : MiddleParameters) : p.B * p.Z + p.Z * p.B = p.W := by
  have hl : 1 + p.lambda ≠ 0 := by linarith [p.lambda_pos]
  have hl0 := p.lambda_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, Z, W, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [hl, hl0] <;> ring

theorem H_identity (p : MiddleParameters) : p.H = p.Z - p.nu • p.E := by
  have hl : 1 + p.lambda ≠ 0 := by linarith [p.lambda_pos]
  have hl0 := p.lambda_pos.ne'
  have hc0 := p.c_pos.ne'
  have hs := p.stationarity
  rw [← p.s_sq] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Z, nu, E, delta]
  all_goals field_simp [hl, hl0, hc0] <;> nlinarith [hs]

theorem determinant_Z (p : MiddleParameters) :
    p.Z.det = p.denominator * (p.rho - p.c) /
      (16 * p.c * (1 - p.c ^ 2)) := by
  have hden := p.denominator_pos.ne'
  have hc := p.c_pos.ne'
  have hr : p.rho - p.c ≠ 0 := (sub_pos.mpr p.c_lt_rho).ne'
  have hs := p.s_sq
  have hcs : 1 - p.c ^ 2 ≠ 0 := (sub_pos.mpr p.c_sq_lt_one).ne'
  have hsum : 1 + p.lambda ≠ 0 := by linarith [p.lambda_pos]
  have hl0 := p.lambda_pos.ne'
  simp [Z, Matrix.det_fin_two]
  dsimp [lambda, denominator] at *
  field_simp [hden, hc, hr, hcs, hsum, hl0]
  ring_nf
  simp only [hs]
  have hquad : 4 - p.c ^ 2 * 8 + p.c ^ 4 * 4 ≠ 0 := by
    have hpos : 0 < (1 - p.c ^ 2) ^ 2 := sq_pos_of_pos (sub_pos.mpr p.c_sq_lt_one)
    nlinarith
  field_simp [hquad] <;> ring

theorem determinant_Z_pos (p : MiddleParameters) : 0 < p.Z.det := by
  rw [p.determinant_Z]
  exact div_pos
    (mul_pos p.denominator_pos (sub_pos.mpr p.c_lt_rho))
    (mul_pos (mul_pos (by norm_num) p.c_pos) (sub_pos.mpr p.c_sq_lt_one))

def pivot (p : MiddleParameters) : ℝ := (p.rho + p.c) / 4
def off (p : MiddleParameters) : ℝ := -p.s / (2 * (1 + p.lambda))
def remainder (p : MiddleParameters) : ℝ :=
  (p.rho - p.c) / (4 * p.lambda) - p.off ^ 2 / p.pivot

theorem pivot_pos (p : MiddleParameters) : 0 < p.pivot := by
  dsimp [pivot]
  linarith [p.rho_pos, p.c_pos]

theorem remainder_identity (p : MiddleParameters) :
    p.remainder = p.Z.det / p.pivot := by
  have hp : p.rho + p.c ≠ 0 := by linarith [p.rho_pos, p.c_pos]
  simp [remainder, Z, off, pivot, Matrix.det_fin_two]
  field_simp [hp] <;> ring

theorem remainder_pos (p : MiddleParameters) : 0 < p.remainder := by
  rw [p.remainder_identity]
  exact div_pos p.determinant_Z_pos p.pivot_pos

theorem Z_quadratic_form (p : MiddleParameters) (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (p.Z *ᵥ v) =
      p.pivot * (v 0 + p.off / p.pivot * v 1) ^ 2 +
      p.remainder * (v 1) ^ 2 := by
  have hZ : p.Z = !![p.pivot, p.off; p.off, (p.rho - p.c) / (4 * p.lambda)] := rfl
  rw [hZ]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, remainder]
  field_simp [p.pivot_pos.ne'] <;> ring

theorem Z_posSemidef (p : MiddleParameters) : p.Z.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg p.Z_hermitian
  intro v
  rw [p.Z_quadratic_form]
  exact add_nonneg (mul_nonneg p.pivot_pos.le (sq_nonneg _))
    (mul_nonneg p.remainder_pos.le (sq_nonneg _))

theorem H_posSemidef (p : MiddleParameters) : p.H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg p.H_hermitian
  intro v
  simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hp := p.delta_pos
  nlinarith [sq_nonneg (v 0)]

theorem B_square_posSemidef (p : MiddleParameters) : (p.B ^ 2).PosSemidef := by
  simpa only [pow_two, p.B_hermitian.eq] using
    Matrix.posSemidef_conjTranspose_mul_self p.B

theorem B_square_contraction (p : MiddleParameters) : ((1 : Mat2) - p.B ^ 2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_one.sub p.B_square_posSemidef.1
  · intro v
    rw [p.B_square]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hl : 0 ≤ 1 - p.lambda ^ 2 := by
      nlinarith [p.lambda_pos, p.lambda_lt_one]
    nlinarith [sq_nonneg (v 1), mul_nonneg hl (sq_nonneg (v 1))]

theorem complementary_slackness (p : MiddleParameters) :
    p.H * ((1 : Mat2) - p.B ^ 2) = 0 := by
  rw [p.B_square]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.mul_apply, Fin.sum_univ_two]

theorem extinction_value (p : MiddleParameters) : (p.W * p.B).trace = p.r := by
  simpa [B, W, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using
    p.weighted_trace_value

theorem objective_value (p : MiddleParameters) : (p.E * p.B ^ 2).trace = p.h := by
  rw [p.B_square]
  simp [E, h, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Trace positivity is derived from the explicit two-square decomposition. -/
theorem trace_Z_mul (p : MiddleParameters) (M : Mat2) (hM : M.IsHermitian) :
    (p.Z * M).trace = p.pivot *
      (star ![1, p.off / p.pivot] ⬝ᵥ (M *ᵥ ![1, p.off / p.pivot])) +
      p.remainder * M 1 1 := by
  have hMoff : M 1 0 = M 0 1 := by simpa using hM.apply 0 1
  have hZ : p.Z = !![p.pivot, p.off; p.off, (p.rho - p.c) / (4 * p.lambda)] := rfl
  rw [hZ]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, remainder, hMoff]
  field_simp [p.pivot_pos.ne'] <;> ring

theorem trace_Z_mul_nonneg (p : MiddleParameters) {M : Mat2} (hM : M.PosSemidef) :
    0 ≤ (p.Z * M).trace := by
  rw [p.trace_Z_mul M hM.1]
  exact add_nonneg
    (mul_nonneg p.pivot_pos.le (hM.dotProduct_mulVec_nonneg _))
    (mul_nonneg p.remainder_pos.le hM.diag_nonneg)

theorem trace_Z_mul_eq_zero_iff (p : MiddleParameters) {M : Mat2}
    (hM : M.PosSemidef) : (p.Z * M).trace = 0 ↔ M = 0 := by
  constructor
  · intro hzero
    rw [p.trace_Z_mul M hM.1] at hzero
    have hvn := hM.dotProduct_mulVec_nonneg ![1, p.off / p.pivot]
    have hdn : 0 ≤ M 1 1 := hM.diag_nonneg
    have hd0 : M 1 1 = 0 := by
      nlinarith [p.pivot_pos, p.remainder_pos]
    have hv0 : star ![1, p.off / p.pivot] ⬝ᵥ
        (M *ᵥ ![1, p.off / p.pivot]) = 0 := by
      rw [hd0, mul_zero, add_zero] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left p.pivot_pos.ne'
    have he0 : star ![0, 1] ⬝ᵥ (M *ᵥ ![0, 1]) = 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd0]
    have hve := hM.dotProduct_mulVec_zero_iff.mp hv0
    have he := hM.dotProduct_mulVec_zero_iff.mp he0
    have h01 : M 0 1 = 0 := by
      have := congrFun he 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have h00 : M 0 0 = 0 := by
      have := congrFun hve 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h01] using this
    have h10 : M 1 0 = 0 := by simpa [h01] using hM.1.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, hd0]
  · rintro rfl
    simp

theorem trace_H_mul_nonneg (p : MiddleParameters) {M : Mat2} (hM : M.PosSemidef) :
    0 ≤ (p.H * M).trace := by
  simp [H, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  exact mul_nonneg p.delta_pos.le hM.diag_nonneg

theorem dual_trace_identity (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian) :
    (p.Z * (Q - A ^ 2)).trace + (p.H * ((1 : Mat2) - Q)).trace +
      (p.Z * ((A - p.B) ^ 2)).trace =
    p.nu * ((p.E * Q).trace - p.h) + p.r - (p.W * A).trace := by
  have hAoff : A 1 0 = A 0 1 := by simpa using hA.apply 0 1
  have hQoff : Q 1 0 = Q 0 1 := by simpa using hQ.apply 0 1
  rw [p.H_identity, ← p.extinction_value, ← p.objective_value]
  have hl0 := p.lambda_pos.ne'
  have hsum : 1 + p.lambda ≠ 0 := by linarith [p.lambda_pos]
  have hc0 := p.c_pos.ne'
  have hs := p.stationarity
  have hsl := congrArg (fun z : ℝ => z * p.lambda) hs
  have hsll := congrArg (fun z : ℝ => z * p.lambda ^ 2) hs
  simp [B, Z, W, E, nu, pow_two, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, hAoff, hQoff]
  field_simp [hl0, hsum, hc0]
  ring_nf
  simp only [p.s_sq]
  nlinarith [hs, hsl, hsll]

/-- The entire middle-branch lifted SDP upper bound, for every admissible
overlap and middle parameter, rather than just the old rational example. -/
theorem middle_SDP_upper_bound (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (p.W * A).trace = p.r) :
    (p.E * Q).trace ≤ p.h := by
  have hD : (A - p.B).IsHermitian := hA.sub p.B_hermitian
  have hDD : ((A - p.B) ^ 2).PosSemidef := by
    simpa only [pow_two, hD.eq] using
      Matrix.posSemidef_conjTranspose_mul_self (A - p.B)
  have hn := add_nonneg
    (add_nonneg (p.trace_Z_mul_nonneg hrelax) (p.trace_H_mul_nonneg hcontract))
    (p.trace_Z_mul_nonneg hDD)
  rw [p.dual_trace_identity A Q hA hQ, htarget] at hn
  have hnu := p.nu_neg
  nlinarith

theorem middle_SDP_attainment (p : MiddleParameters) :
    ∃ A Q : Mat2, A.IsHermitian ∧ Q.IsHermitian ∧
      (Q - A ^ 2).PosSemidef ∧ ((1 : Mat2) - Q).PosSemidef ∧
      (p.W * A).trace = p.r ∧ (p.E * Q).trace = p.h := by
  refine ⟨p.B, p.B ^ 2, p.B_hermitian, p.B_square_posSemidef.1,
    ?_, p.B_square_contraction, p.extinction_value, p.objective_value⟩
  simpa using (Matrix.PosSemidef.zero : (0 : Mat2).PosSemidef)

/-- Uniqueness of the real compressed middle-branch maximizer. This proves
the positive-definite certificate's equality conditions rather than merely
exhibiting one optimizing pair. The complex auxiliary-block equality bridge
is addressed by the separate literal compression module. -/
theorem middle_SDP_equality (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (p.W * A).trace = p.r)
    (hobj : (p.E * Q).trace = p.h) : A = p.B ∧ Q = p.B ^ 2 := by
  have hD : (A - p.B).IsHermitian := hA.sub p.B_hermitian
  have hDD : ((A - p.B) ^ 2).PosSemidef := by
    simpa only [pow_two, hD.eq] using
      Matrix.posSemidef_conjTranspose_mul_self (A - p.B)
  have h1 := p.trace_Z_mul_nonneg hrelax
  have h2 := p.trace_H_mul_nonneg hcontract
  have h3 := p.trace_Z_mul_nonneg hDD
  have hid := p.dual_trace_identity A Q hA hQ
  rw [htarget, hobj] at hid
  have htDD : (p.Z * ((A - p.B) ^ 2)).trace = 0 := by linarith
  have hDDzero := (p.trace_Z_mul_eq_zero_iff hDD).mp htDD
  have hDzero : A - p.B = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    simpa only [hD.eq, ← pow_two, hDDzero, Matrix.trace_zero]
  have hAB : A = p.B := sub_eq_zero.mp hDzero
  have htR : (p.Z * (Q - A ^ 2)).trace = 0 := by linarith
  have hR := (p.trace_Z_mul_eq_zero_iff hrelax).mp htR
  exact ⟨hAB, (sub_eq_zero.mp hR).trans (congrArg (fun M : Mat2 => M ^ 2) hAB)⟩

#print axioms H_identity
#print axioms determinant_Z
#print axioms Z_posSemidef
#print axioms middle_SDP_upper_bound
#print axioms middle_SDP_attainment
#print axioms middle_SDP_equality

end MiddleParameters
end GeneralizedResearch
