import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Literal complex-channel to real-input-plane compression

This module uses arbitrary finite auxiliary channel sets. Reciprocity is
complex transpose symmetry, and passivity is the actual complex Gram-matrix
inequality. The real relaxation is proved from those hypotheses; it is not
assumed as a property of an abstract channel class. -/
noncomputable section
namespace GeneralizedResearch
namespace RealCompression
open scoped Matrix ComplexOrder

def realPart {m n : Type*} (M : Matrix m n ℂ) : Matrix m n ℝ := M.map Complex.re
def imagPart {m n : Type*} (M : Matrix m n ℂ) : Matrix m n ℝ := M.map Complex.im

theorem realPart_hermitian {n : Type*} {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : (realPart M).IsHermitian := by
  ext i j
  have hij := hM.apply i j
  have hreal := congrArg Complex.re hij
  simpa [realPart, Matrix.conjTranspose_apply] using hreal

theorem realPart_gram {m n : Type*} [Fintype m] (M : Matrix m n ℂ) :
    realPart (M.conjTranspose * M) =
      (realPart M).transpose * realPart M + (imagPart M).transpose * imagPart M := by
  ext i j
  simp [realPart, imagPart, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_re, Finset.sum_add_distrib]

theorem realPart_quadratic {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (x : n → ℝ) :
    star x ⬝ᵥ (realPart M *ᵥ x) =
      (star (fun i => (x i : ℂ)) ⬝ᵥ (M *ᵥ fun i => (x i : ℂ))).re := by
  simp [realPart, Matrix.mulVec, dotProduct, Complex.mul_re,
    Finset.mul_sum]

theorem realPart_posSemidef {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : (realPart M).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realPart_hermitian hM.1)
  intro x
  rw [realPart_quadratic]
  exact (RCLike.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg
    (fun i => (x i : ℂ)))).1

variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
abbrev Channels := Sum (Fin 2) ι

def block (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := S.submatrix Sum.inl Sum.inl
def auxiliary (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) :
    Matrix ι (Fin 2) ℂ := S.submatrix Sum.inr Sum.inl
def B (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ := realPart (block S)
def Q (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  realPart ((S.conjTranspose * S).submatrix Sum.inl Sum.inl)

theorem block_symmetric (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ)
    (hS : S.transpose = S) : (block S).transpose = block S := by
  ext i j
  exact congrFun (congrFun hS (Sum.inl i)) (Sum.inl j)

theorem B_hermitian (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ)
    (hS : S.transpose = S) : (B S).IsHermitian := by
  ext i j
  have hij := congrFun (congrFun (block_symmetric S hS) i) j
  simpa [B, realPart, Matrix.conjTranspose_apply] using congrArg Complex.re hij

theorem compressed_gram_decomposition
    (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) :
    (S.conjTranspose * S).submatrix Sum.inl Sum.inl =
      (block S).conjTranspose * block S +
      (auxiliary S).conjTranspose * auxiliary S := by
  ext i j
  simp [block, auxiliary, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type]

theorem Q_decomposition
    (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ)
    (hS : S.transpose = S) :
    Q S = B S ^ 2 +
      (imagPart (block S)).transpose * imagPart (block S) +
      (realPart (auxiliary S)).transpose * realPart (auxiliary S) +
      (imagPart (auxiliary S)).transpose * imagPart (auxiliary S) := by
  rw [Q, compressed_gram_decomposition]
  have hadd (A D : Matrix (Fin 2) (Fin 2) ℂ) :
      realPart (A + D) = realPart A + realPart D := by
    ext i j
    simp [realPart]
  rw [hadd, realPart_gram, realPart_gram]
  have hBt : (B S).transpose = B S := by
    simpa using (B_hermitian S hS).eq
  rw [show realPart (block S) = B S from rfl, hBt]
  simp only [pow_two]
  abel

/-- Both PSD inequalities of the manuscript's canonical relaxation follow
from literal reciprocal complex matrices, in any finite channel dimension. -/
theorem canonical_PSD_relaxation
    (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ)
    (hS : S.transpose = S)
    (hpass : ((1 : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) -
      S.conjTranspose * S).PosSemidef) :
    (B S).IsHermitian ∧ (Q S).IsHermitian ∧
      (Q S - B S ^ 2).PosSemidef ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) - Q S).PosSemidef := by
  have hdecomp := Q_decomposition S hS
  have him := Matrix.posSemidef_conjTranspose_mul_self (imagPart (block S))
  have hrealAux := Matrix.posSemidef_conjTranspose_mul_self (realPart (auxiliary S))
  have himAux := Matrix.posSemidef_conjTranspose_mul_self (imagPart (auxiliary S))
  have hrelax : (Q S - B S ^ 2).PosSemidef := by
    rw [hdecomp]
    have hid : B S ^ 2 +
        (imagPart (block S)).transpose * imagPart (block S) +
        (realPart (auxiliary S)).transpose * realPart (auxiliary S) +
        (imagPart (auxiliary S)).transpose * imagPart (auxiliary S) - B S ^ 2 =
        (imagPart (block S)).transpose * imagPart (block S) +
        (realPart (auxiliary S)).transpose * realPart (auxiliary S) +
        (imagPart (auxiliary S)).transpose * imagPart (auxiliary S) := by abel
    rw [hid]
    simpa using (him.add hrealAux).add himAux
  have hq : (Q S).IsHermitian := by
    exact realPart_hermitian
      ((Matrix.isHermitian_conjTranspose_mul_self S).submatrix Sum.inl)
  have hi := realPart_posSemidef (hpass.submatrix Sum.inl)
  have hid : realPart
      (((1 : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ) -
        S.conjTranspose * S).submatrix Sum.inl Sum.inl) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) - Q S := by
    ext i j
    simp [realPart, Q, Matrix.one_apply]
    split_ifs <;> norm_num
  rw [hid] at hi
  exact ⟨B_hermitian S hS, hq, hrelax, hi⟩

/-- Equality in the real-input relaxation forces the imaginary input block
and all input-to-auxiliary channels to vanish. -/
theorem no_auxiliary_at_equality
    (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ)
    (hS : S.transpose = S) (heq : Q S = B S ^ 2) :
    imagPart (block S) = 0 ∧ auxiliary S = 0 := by
  have hdecomp := Q_decomposition S hS
  rw [heq] at hdecomp
  have hsum : (imagPart (block S)).transpose * imagPart (block S) +
      (realPart (auxiliary S)).transpose * realPart (auxiliary S) +
      (imagPart (auxiliary S)).transpose * imagPart (auxiliary S) = 0 := by
    apply add_left_cancel (a := B S ^ 2)
    simpa [add_assoc] using hdecomp.symm
  have him := Matrix.posSemidef_conjTranspose_mul_self (imagPart (block S))
  have hrealAux := Matrix.posSemidef_conjTranspose_mul_self (realPart (auxiliary S))
  have himAux := Matrix.posSemidef_conjTranspose_mul_self (imagPart (auxiliary S))
  have ht := congrArg Matrix.trace hsum
  simp only [Matrix.trace_add, Matrix.trace_zero] at ht
  have hti : ((imagPart (block S)).transpose * imagPart (block S)).trace = 0 := by
    have h1 := him.trace_nonneg
    have h2 := hrealAux.trace_nonneg
    have h3 := himAux.trace_nonneg
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2 h3
    simpa using (show ((imagPart (block S)).transpose * imagPart (block S)).trace = 0 by
      linarith)
  have htr : ((realPart (auxiliary S)).transpose * realPart (auxiliary S)).trace = 0 := by
    have h1 := him.trace_nonneg
    have h2 := hrealAux.trace_nonneg
    have h3 := himAux.trace_nonneg
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2 h3
    simpa using (show ((realPart (auxiliary S)).transpose * realPart (auxiliary S)).trace = 0 by
      linarith)
  have htia : ((imagPart (auxiliary S)).transpose * imagPart (auxiliary S)).trace = 0 := by
    have h1 := him.trace_nonneg
    have h2 := hrealAux.trace_nonneg
    have h3 := himAux.trace_nonneg
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2 h3
    simpa using (show ((imagPart (auxiliary S)).transpose * imagPart (auxiliary S)).trace = 0 by
      linarith)
  have hi : imagPart (block S) = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    simpa using hti
  have har : realPart (auxiliary S) = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    simpa using htr
  have hai : imagPart (auxiliary S) = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    simpa using htia
  refine ⟨hi, ?_⟩
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun har i) j
  · exact congrFun (congrFun hai i) j

theorem reverse_auxiliary_vanishes
    (S : Matrix (Channels (ι := ι)) (Channels (ι := ι)) ℂ)
    (hS : S.transpose = S) (heq : Q S = B S ^ 2) :
    S.submatrix Sum.inl Sum.inr = 0 := by
  have ha := (no_auxiliary_at_equality S hS heq).2
  ext i j
  have hsym := congrFun (congrFun hS (Sum.inl i)) (Sum.inr j)
  have haux := congrFun (congrFun ha j) i
  simpa [auxiliary] using hsym.symm.trans haux

#print axioms realPart_gram
#print axioms canonical_PSD_relaxation
#print axioms no_auxiliary_at_equality
#print axioms reverse_auxiliary_vanishes
end RealCompression
end GeneralizedResearch
