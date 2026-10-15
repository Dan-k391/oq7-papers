import GeneralizedResearch.CanonicalMiddle
import GeneralizedResearch.OuterBound
import GeneralizedResearch.ChannelPowers
import GeneralizedResearch.ThirdBranchAttainment
import GeneralizedResearch.OrthogonalSharpness
import Mathlib.Tactic

/-! Actual complex reciprocal channel operators attaining the prescribed-overlap
branches. Positivity is proved for literal complex Gram matrices; it is not
assumed from a real SDP witness without a complexification argument. -/
noncomputable section
namespace GeneralizedResearch
namespace ChannelAttainment
open scoped Matrix ComplexOrder

def complexify {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  fun i j => (A i j : ℂ)

theorem complexify_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp [complexify, Matrix.mul_apply]

theorem complexify_sub {m n : Type*} (A B : Matrix m n ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j
  simp [complexify]

theorem complexify_one {n : Type*} [DecidableEq n] :
    complexify (1 : Matrix n n ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.one_apply, h]

theorem complexify_conjTranspose {m n : Type*} (A : Matrix m n ℝ) :
    (complexify A).conjTranspose = complexify A.transpose := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

theorem complexify_transpose {m n : Type*} (A : Matrix m n ℝ) :
    (complexify A).transpose = complexify A.transpose := rfl

theorem complexify_hermitian {n : Type*} {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : (complexify A).IsHermitian := by
  ext i j
  have h := hA.apply i j
  simpa [complexify, Matrix.conjTranspose_apply] using
    congrArg (fun x : ℝ => (x : ℂ)) h

theorem complexify_quadratic_re {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (z : n → ℂ) :
    (star z ⬝ᵥ (complexify A *ᵥ z)).re =
      star (fun i => (z i).re) ⬝ᵥ (A *ᵥ fun i => (z i).re) +
      star (fun i => (z i).im) ⬝ᵥ (A *ᵥ fun i => (z i).im) := by
  simp [complexify, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im,
    Finset.mul_sum, Finset.sum_add_distrib]

/-- Real PSD matrices remain PSD on genuinely complex vectors. -/
theorem complexify_posSemidef {n : Type*} [Fintype n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : (complexify A).PosSemidef := by
  have hH := complexify_hermitian hA.1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro z
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [complexify_quadratic_re]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hA.dotProduct_mulVec_nonneg _)
  · have h := congrArg Complex.im (hH.star_dotProduct_mulVec_comm z z)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith

theorem complexify_contraction {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ((1 : Matrix n n ℝ) - A.transpose * A).PosSemidef) :
    ((1 : Matrix n n ℂ) - (complexify A).conjTranspose * complexify A).PosSemidef := by
  have h := complexify_posSemidef hA
  simpa only [complexify_sub, complexify_one, complexify_mul, complexify_conjTranspose] using h

abbrev CMat2 := Matrix (Fin 2) (Fin 2) ℂ

def realVector {n : Type*} (x : n → ℝ) : n → ℂ := fun i => (x i : ℂ)

theorem complexify_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (x : n → ℝ) :
    complexify A *ᵥ realVector x = realVector (A *ᵥ x) := by
  ext i
  simp [complexify, realVector, Matrix.mulVec, dotProduct]

theorem realVector_dot {n : Type*} [Fintype n] (x y : n → ℝ) :
    star (realVector x) ⬝ᵥ realVector y = ((x ⬝ᵥ y : ℝ) : ℂ) := by
  simp [realVector, dotProduct]

theorem realVector_power {n : Type*} [Fintype n] (x : n → ℝ) :
    ChannelPowers.power (realVector x) = x ⬝ᵥ x := by
  rw [ChannelPowers.power, realVector_dot, Complex.ofReal_re]

theorem realVector_star {n : Type*} (x : n → ℝ) : star (realVector x) = realVector x := by
  ext i
  simp [realVector]

def pcoef (rho : ℝ) : ℝ := Real.sqrt ((1 + rho) / 2)
def qcoef (rho : ℝ) : ℝ := Real.sqrt ((1 - rho) / 2)

def input (rho : ℝ) : Fin 2 → ℂ :=
  realVector ![pcoef rho, qcoef rho]

def background : CMat2 := !![1, 0; 0, -1]

theorem background_symmetric : background.transpose = background := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [background]

theorem background_unitary : background.conjTranspose * background = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [background, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem reverse_input (rho : ℝ) : ChannelPowers.reverse background (input rho) =
    realVector ![pcoef rho, -qcoef rho] := by
  ext i
  fin_cases i <;> simp [ChannelPowers.reverse, background, input, realVector,
    Matrix.vecHead, Matrix.vecTail]

theorem input_power {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    ChannelPowers.power (input rho) = 1 := by
  have hp : pcoef rho ^ 2 = (1 + rho) / 2 := Real.sq_sqrt (by linarith)
  have hq : qcoef rho ^ 2 = (1 - rho) / 2 := Real.sq_sqrt (by linarith)
  rw [input, realVector_power]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ← sq, hp, hq]
  ring

theorem input_overlap {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    ‖star (input rho) ⬝ᵥ ChannelPowers.reverse background (input rho)‖ = rho := by
  have hp : pcoef rho ^ 2 = (1 + rho) / 2 := Real.sq_sqrt (by linarith)
  have hq : qcoef rho ^ 2 = (1 - rho) / 2 := Real.sq_sqrt (by linarith)
  have he : star (input rho) ⬝ᵥ ChannelPowers.reverse background (input rho) = (rho : ℂ) := by
    rw [reverse_input, input, realVector_dot]
    congr 1
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_neg, ← sq, hp, hq]
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]

theorem canonical_forward_re {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1)
    (S : CMat2) (hS : S.transpose = S) :
    (ChannelPowers.forward S background (input rho)).re =
      (1 + rho) / 2 * (S 0 0).re - (1 - rho) / 2 * (S 1 1).re := by
  have hp : pcoef rho ^ 2 = (1 + rho) / 2 := Real.sq_sqrt (by linarith)
  have hq : qcoef rho ^ 2 = (1 - rho) / 2 := Real.sq_sqrt (by linarith)
  have hoff : S 1 0 = S 0 1 := congrFun (congrFun hS 0) 1
  have he : background *ᵥ input rho = realVector ![pcoef rho, -qcoef rho] := by
    ext i
    fin_cases i <;> simp [background, input, realVector, Matrix.vecHead, Matrix.vecTail]
  rw [ChannelPowers.forward, he]
  simp only [input, realVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, hoff]
  rw [← hp, ← hq]
  ring

theorem real_input_output_power (S : CMat2) (x y : ℝ) :
    ChannelPowers.power (S *ᵥ realVector ![x, y]) =
      x ^ 2 * ((S.conjTranspose * S) 0 0).re +
      2 * x * y * ((S.conjTranspose * S) 0 1).re +
      y ^ 2 * ((S.conjTranspose * S) 1 1).re := by
  have hoff : ((S.conjTranspose * S) 1 0).re = ((S.conjTranspose * S) 0 1).re := by
    have h := congrArg Complex.re ((Matrix.isHermitian_conjTranspose_mul_self S).apply 0 1)
    simpa using h
  rw [ChannelPowers.gram_power]
  simp only [realVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, hoff]
  ring

theorem canonical_signed_difference (S : CMat2) (rho : ℝ) :
    ChannelPowers.absorption S (input rho) -
      ChannelPowers.absorption S (ChannelPowers.reverse background (input rho)) =
      -4 * pcoef rho * qcoef rho * ((S.conjTranspose * S) 0 1).re := by
  simp only [ChannelPowers.absorption]
  rw [reverse_input, input, real_input_output_power, real_input_output_power]
  ring

theorem root_product {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    2 * pcoef rho * qcoef rho = Real.sqrt (1 - rho ^ 2) := by
  have hp : pcoef rho ^ 2 = (1 + rho) / 2 := Real.sq_sqrt (by linarith)
  have hq : qcoef rho ^ 2 = (1 - rho) / 2 := Real.sq_sqrt (by linarith)
  have hR : 0 ≤ 1 - rho ^ 2 := by nlinarith
  have hprod : 0 ≤ 2 * pcoef rho * qcoef rho := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have he : (2 * pcoef rho * qcoef rho) ^ 2 = 1 - rho ^ 2 := by
    rw [mul_pow, mul_pow, hp, hq]
    ring
  nlinarith [Real.sq_sqrt hR, Real.sqrt_nonneg (1 - rho ^ 2)]

theorem canonical_abs_difference {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1)
    (S : CMat2) :
    |ChannelPowers.absorption S (input rho) -
      ChannelPowers.absorption S (ChannelPowers.reverse background (input rho))| =
      2 * Real.sqrt (1 - rho ^ 2) * |((S.conjTranspose * S) 0 1).re| := by
  rw [canonical_signed_difference]
  have hid : -4 * pcoef rho * qcoef rho = -2 * Real.sqrt (1 - rho ^ 2) := by
    nlinarith [root_product h0 h1]
  rw [hid, abs_mul]
  have hab : |-2 * Real.sqrt (1 - rho ^ 2)| = 2 * Real.sqrt (1 - rho ^ 2) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hab]

/-- A literal finite complex channel system, with its actual reference reversal. -/
def FiniteAttainment (rho r delta : ℝ) : Prop :=
  ∃ n : ℕ, ∃ S S0 : Matrix (Fin n) (Fin n) ℂ, ∃ u : Fin n → ℂ,
    S.transpose = S ∧ ((1 : Matrix (Fin n) (Fin n) ℂ) - S.conjTranspose * S).PosSemidef ∧
    S0.transpose = S0 ∧ S0.conjTranspose * S0 = 1 ∧
    ChannelPowers.power u = 1 ∧
    ‖star u ⬝ᵥ ChannelPowers.reverse S0 u‖ = rho ∧
    (ChannelPowers.forward S S0 u).re = r ∧
    |ChannelPowers.absorption S u - ChannelPowers.absorption S (ChannelPowers.reverse S0 u)| = delta

def phase (t : ℝ) : ℂ := ⟨t, Real.sqrt (1 - t ^ 2)⟩

theorem phase_unit {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    star (phase t) * phase t = 1 := by
  have hb : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hn : Complex.normSq (phase t) = 1 := by
    rw [phase, Complex.normSq_mk]
    rw [← sq, ← sq, Real.sq_sqrt hb]
    ring
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hn]
  rfl

def firstScatterer (rho r : ℝ) : CMat2 :=
  phase (2 * r / rho) • complexify OuterBound.P

theorem first_symmetric (rho r : ℝ) :
    (firstScatterer rho r).transpose = firstScatterer rho r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstScatterer, complexify, OuterBound.P]

theorem first_gram {rho r : ℝ} (h0 : 0 < rho) (hr0 : 0 ≤ r) (hr1 : r ≤ rho / 2) :
    (firstScatterer rho r).conjTranspose * firstScatterer rho r = complexify OuterBound.P := by
  have ht0 : 0 ≤ 2 * r / rho := div_nonneg (by linarith) h0.le
  have ht1 : 2 * r / rho ≤ 1 := by rw [div_le_one h0]; linarith
  have hP : (complexify OuterBound.P).conjTranspose = complexify OuterBound.P :=
    (complexify_hermitian OuterBound.P_hermitian).eq
  have hPsq : complexify OuterBound.P * complexify OuterBound.P = complexify OuterBound.P := by
    rw [← complexify_mul, ← pow_two, OuterBound.P_square]
  rw [firstScatterer, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, phase_unit ht0 ht1, one_smul, hP, hPsq]

theorem first_passive {rho r : ℝ} (h0 : 0 < rho) (hr0 : 0 ≤ r) (hr1 : r ≤ rho / 2) :
    ((1 : CMat2) - (firstScatterer rho r).conjTranspose * firstScatterer rho r).PosSemidef := by
  rw [first_gram h0 hr0 hr1]
  have h := complexify_posSemidef OuterBound.P_contraction
  simpa only [complexify_sub, complexify_one] using h

theorem first_forward {rho r : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    (ChannelPowers.forward (firstScatterer rho r) background (input rho)).re = r := by
  rw [canonical_forward_re h0 h1 _ (first_symmetric rho r)]
  simp [firstScatterer, complexify, OuterBound.P, phase, Complex.mul_re]
  field_simp [h0.ne']
  ring

theorem first_difference {rho r : ℝ} (h0 : 0 < rho) (h1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ rho / 2) :
    |ChannelPowers.absorption (firstScatterer rho r) (input rho) -
      ChannelPowers.absorption (firstScatterer rho r)
        (ChannelPowers.reverse background (input rho))| = Real.sqrt (1 - rho ^ 2) := by
  rw [canonical_abs_difference h0 h1, first_gram h0 hr0 hr1]
  norm_num [complexify, OuterBound.P]
  ring

/-- Complete first-branch equality construction, including both transitions. -/
theorem first_branch_attainment {rho r : ℝ} (h0 : 0 < rho) (h1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ rho / 2) :
    FiniteAttainment rho r (Real.sqrt (1 - rho ^ 2)) :=
  ⟨2, firstScatterer rho r, background, input rho, first_symmetric rho r,
    first_passive h0 hr0 hr1, background_symmetric, background_unitary,
    input_power h0 h1, input_overlap h0 h1, first_forward h0 h1,
    first_difference h0 h1 hr0 hr1⟩

def middleReal (p : MiddleParameters) : Mat2 := p.O * p.B * p.O.transpose
def middleScatterer (p : MiddleParameters) : CMat2 := complexify (middleReal p)

theorem middleReal_hermitian (p : MiddleParameters) : (middleReal p).IsHermitian := by
  simpa [middleReal] using Matrix.isHermitian_conjTranspose_mul_mul p.O.transpose p.B_hermitian

theorem middleReal_rotated (p : MiddleParameters) :
    p.O.transpose * middleReal p * p.O = p.B := by
  calc
    _ = (p.O.transpose * p.O) * p.B * (p.O.transpose * p.O) := by
      simp [middleReal, Matrix.mul_assoc]
    _ = p.B := by rw [p.O_transpose_mul]; simp

theorem middleReal_gram (p : MiddleParameters) :
    (middleReal p).transpose * middleReal p = p.O * p.B ^ 2 * p.O.transpose := by
  have ht : (middleReal p).transpose = middleReal p := (middleReal_hermitian p).eq
  rw [ht]
  calc
    _ = p.O * p.B * (p.O.transpose * p.O) * p.B * p.O.transpose := by
      simp [middleReal, Matrix.mul_assoc]
    _ = _ := by rw [p.O_transpose_mul]; simp [Matrix.mul_assoc, pow_two]

theorem middleReal_contraction (p : MiddleParameters) :
    ((1 : Mat2) - (middleReal p).transpose * middleReal p).PosSemidef := by
  have h := p.B_square_contraction.mul_mul_conjTranspose_same p.O
  have hid : (1 : Mat2) - (middleReal p).transpose * middleReal p =
      p.O * ((1 : Mat2) - p.B ^ 2) * p.O.transpose := by
    rw [middleReal_gram]
    simp [Matrix.mul_sub, Matrix.sub_mul, p.O_mul_transpose]
  rw [hid]
  simpa using h

theorem middle_weighted_trace (p : MiddleParameters) :
    (p.canonicalW * middleReal p).trace = p.r := by
  have h := p.trace_rotation p.canonicalW (middleReal p)
  rw [p.rotated_W, middleReal_rotated] at h
  exact h.symm.trans p.extinction_value

theorem middle_gram_offdiag (p : MiddleParameters) :
    (((middleReal p).transpose * middleReal p) 0 1) = p.h := by
  let G := (middleReal p).transpose * middleReal p
  have hG : G.IsHermitian := by
    simpa [G] using Matrix.isHermitian_conjTranspose_mul_self (middleReal p)
  have hrot : p.O.transpose * G * p.O = p.B ^ 2 := by
    dsimp only [G]
    rw [middleReal_gram]
    calc
      _ = (p.O.transpose * p.O) * p.B ^ 2 * (p.O.transpose * p.O) := by
        simp [Matrix.mul_assoc]
      _ = _ := by rw [p.O_transpose_mul]; simp
  have h := p.trace_rotation MiddleParameters.canonicalE G
  rw [p.rotated_E, hrot] at h
  exact (MiddleParameters.canonical_objective G hG).symm.trans (h.symm.trans p.objective_value)

theorem middle_symmetric (p : MiddleParameters) :
    (middleScatterer p).transpose = middleScatterer p := by
  have h : (middleReal p).transpose = middleReal p := (middleReal_hermitian p).eq
  rw [middleScatterer, complexify_transpose, h]

theorem middle_passive (p : MiddleParameters) :
    ((1 : CMat2) - (middleScatterer p).conjTranspose * middleScatterer p).PosSemidef :=
  complexify_contraction _ (middleReal_contraction p)

theorem middle_forward (p : MiddleParameters) :
    (ChannelPowers.forward (middleScatterer p) background (input p.rho)).re = p.r := by
  rw [canonical_forward_re p.rho_pos p.rho_lt_one _ (middle_symmetric p)]
  simp only [middleScatterer, complexify, Complex.ofReal_re]
  have h := middle_weighted_trace p
  simp [MiddleParameters.canonicalW, Matrix.trace_fin_two,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h
  convert h using 1
  ring

theorem middle_gram (p : MiddleParameters) :
    (middleScatterer p).conjTranspose * middleScatterer p =
      complexify ((middleReal p).transpose * middleReal p) := by
  rw [middleScatterer, complexify_conjTranspose, complexify_mul]

theorem middle_difference (p : MiddleParameters) :
    |ChannelPowers.absorption (middleScatterer p) (input p.rho) -
      ChannelPowers.absorption (middleScatterer p)
        (ChannelPowers.reverse background (input p.rho))| =
      2 * Real.sqrt (1 - p.rho ^ 2) * p.h := by
  have hh : 0 < p.h := by
    have hl : 0 < 1 - p.lambda ^ 2 := by nlinarith [p.lambda_pos, p.lambda_lt_one]
    exact div_pos (mul_pos hl p.s_pos) (by norm_num)
  rw [canonical_abs_difference p.rho_pos p.rho_lt_one, middle_gram]
  simp only [complexify, Complex.ofReal_re, middle_gram_offdiag, abs_of_pos hh]

/-- The full continuously parameterized complex-channel middle equality family. -/
theorem middle_branch_attainment (p : MiddleParameters) :
    FiniteAttainment p.rho p.r (2 * Real.sqrt (1 - p.rho ^ 2) * p.h) :=
  ⟨2, middleScatterer p, background, input p.rho, middle_symmetric p,
    middle_passive p, background_symmetric, background_unitary,
    input_power p.rho_pos p.rho_lt_one, input_overlap p.rho_pos p.rho_lt_one,
    middle_forward p, middle_difference p⟩

/-- Lifting a concrete real reciprocal equality construction preserves every
complex-channel requirement, including actual reference reversal and powers. -/
theorem real_channel_attainment {n : ℕ} {rho r delta : ℝ}
    (S S0 : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ)
    (hS : S.transpose = S)
    (hpass : ((1 : Matrix (Fin n) (Fin n) ℝ) - S.transpose * S).PosSemidef)
    (hS0 : S0.transpose = S0) (hunit : S0.transpose * S0 = 1)
    (hrev : S0 *ᵥ a = b) (ha : a ⬝ᵥ a = 1)
    (hrel : a ⬝ᵥ b = rho) (hrho : 0 ≤ rho)
    (hforward : b ⬝ᵥ (S *ᵥ a) = r)
    (hdiff : (S *ᵥ a) ⬝ᵥ (S *ᵥ a) - (S *ᵥ b) ⬝ᵥ (S *ᵥ b) = delta)
    (hdelta : 0 ≤ delta) : FiniteAttainment rho r delta := by
  have hreverse : ChannelPowers.reverse (complexify S0) (realVector a) = realVector b := by
    rw [ChannelPowers.reverse, complexify_mulVec, hrev, realVector_star]
  refine ⟨n, complexify S, complexify S0, realVector a, ?_,
    complexify_contraction S hpass, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [complexify_transpose, hS]
  · rw [complexify_transpose, hS0]
  · rw [complexify_conjTranspose, ← complexify_mul, hunit, complexify_one]
  · rw [realVector_power, ha]
  · rw [hreverse, realVector_dot, hrel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrho]
  · rw [ChannelPowers.forward, complexify_mulVec, hrev, complexify_mulVec,
      realVector_dot, hforward, Complex.ofReal_re]
  · simp only [ChannelPowers.absorption, hreverse, complexify_mulVec, realVector_power]
    have hid : 1 - (S *ᵥ a) ⬝ᵥ (S *ᵥ a) -
        (1 - (S *ᵥ b) ⬝ᵥ (S *ᵥ b)) = -delta := by linarith
    rw [hid, abs_neg, abs_of_nonneg hdelta]

/-- The original closed third branch, now as actual complex channel data. -/
theorem third_branch_attainment (p : ThirdBranch.Parameters) :
    FiniteAttainment p.rho p.r (1 - p.r ^ 2) := by
  apply real_channel_attainment p.S p.S0 ThirdBranch.Parameters.a p.b
    p.S_symmetric p.S_contraction p.S0_symmetric
  · rw [p.S0_symmetric, ← pow_two, p.S0_square]
  · exact p.background_reversal
  · exact p.input_norms.1
  · exact p.input_overlap
  · exact p.rho_pos.le
  · exact p.forward_overlap
  · exact p.absorption_difference
  · nlinarith [p.r_pos, p.r_le_one]

theorem power_neg {n : Type*} [Fintype n] (u : n → ℂ) :
    ChannelPowers.power (-u) = ChannelPowers.power u := by
  simp [ChannelPowers.power, dotProduct]

/-- Negating the literal scatterer changes only the signed forward overlap. -/
theorem FiniteAttainment.neg {rho r delta : ℝ} (h : FiniteAttainment rho r delta) :
    FiniteAttainment rho (-r) delta := by
  obtain ⟨n, S, S0, u, hS, hpass, h0, hunit, hu, hover, hforward, hdiff⟩ := h
  refine ⟨n, -S, S0, u, ?_, ?_, h0, hunit, hu, hover, ?_, ?_⟩
  · simp only [Matrix.transpose_neg, hS]
  · simpa only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] using hpass
  · simpa only [ChannelPowers.forward, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] using
      congrArg (fun x : ℝ => -x) hforward
  · simpa only [ChannelPowers.absorption, Matrix.neg_mulVec, power_neg] using hdiff

/-- Orthogonal background reverses attain the complete passivity parabola,
including the zero/full-extinction endpoints. -/
theorem orthogonal_branch_attainment {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    FiniteAttainment 0 t (1 - t ^ 2) := by
  have hrev : OrthogonalSharpness.S0 *ᵥ OrthogonalSharpness.b = OrthogonalSharpness.a := by
    rw [← OrthogonalSharpness.reversal, Matrix.mulVec_mulVec,
      ← pow_two, OrthogonalSharpness.S0_square, Matrix.one_mulVec]
  apply real_channel_attainment (OrthogonalSharpness.S t) OrthogonalSharpness.S0
    OrthogonalSharpness.b OrthogonalSharpness.a
    (OrthogonalSharpness.S_symmetric t) (OrthogonalSharpness.contraction ht0 ht1)
    OrthogonalSharpness.S0_symmetric
  · rw [OrthogonalSharpness.S0_symmetric, ← pow_two, OrthogonalSharpness.S0_square]
  · exact hrev
  · exact OrthogonalSharpness.unit_orthogonal.2.1
  · rw [dotProduct_comm]
    exact OrthogonalSharpness.unit_orthogonal.2.2
  · norm_num
  · simp [OrthogonalSharpness.S, OrthogonalSharpness.a, OrthogonalSharpness.b,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · exact OrthogonalSharpness.absorption_difference ht0 ht1
  · nlinarith

end ChannelAttainment
end GeneralizedResearch

#print axioms GeneralizedResearch.ChannelAttainment.complexify_posSemidef
#print axioms GeneralizedResearch.ChannelAttainment.first_branch_attainment
#print axioms GeneralizedResearch.ChannelAttainment.middle_branch_attainment
#print axioms GeneralizedResearch.ChannelAttainment.third_branch_attainment
#print axioms GeneralizedResearch.ChannelAttainment.FiniteAttainment.neg
#print axioms GeneralizedResearch.ChannelAttainment.orthogonal_branch_attainment
