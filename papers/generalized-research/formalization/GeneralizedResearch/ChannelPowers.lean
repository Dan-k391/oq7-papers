import GeneralizedResearch.RealCompression
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Actual finite-channel reciprocity and passivity parabola

The scatterer and reference are literal complex matrices. Reciprocity,
reference unitarity and passivity are their standard matrix properties;
extinction equality and the bounds are derived. -/
noncomputable section
namespace GeneralizedResearch
namespace ChannelPowers
open scoped Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

def power (u : n → ℂ) : ℝ := (star u ⬝ᵥ u).re
def absorption (S : Matrix n n ℂ) (u : n → ℂ) : ℝ := 1 - power (S *ᵥ u)
def forward (S S0 : Matrix n n ℂ) (u : n → ℂ) : ℂ :=
  star (S0 *ᵥ u) ⬝ᵥ (S *ᵥ u)
def extinction (S S0 : Matrix n n ℂ) (u : n → ℂ) : ℝ :=
  2 * (1 - (forward S S0 u).re)
def reverse (S0 : Matrix n n ℂ) (u : n → ℂ) : n → ℂ := star (S0 *ᵥ u)

theorem power_nonneg (u : n → ℂ) : 0 ≤ power u := by
  exact (RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg u)).1

theorem power_star (u : n → ℂ) : power (star u) = power u := by
  simp [power, dotProduct, Complex.mul_re]

theorem gram_power (S : Matrix n n ℂ) (u : n → ℂ) :
    power (S *ᵥ u) = (star u ⬝ᵥ ((S.conjTranspose * S) *ᵥ u)).re := by
  simp [power, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]

theorem unitary_power (S0 : Matrix n n ℂ)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    power (S0 *ᵥ u) = power u := by
  rw [gram_power, hunit, Matrix.one_mulVec]
  rfl

theorem reverse_formula (S0 : Matrix n n ℂ) (h0 : S0.transpose = S0)
    (u : n → ℂ) : reverse S0 u = S0.conjTranspose *ᵥ star u := by
  ext i
  simp [reverse, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hij := congrFun (congrFun h0 i) j
  change S0 j i = S0 i j at hij
  change star (S0 i j) * star (u j) = star (S0 j i) * star (u j)
  rw [hij]

theorem background_reverse (S0 : Matrix n n ℂ) (h0 : S0.transpose = S0)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    S0 *ᵥ reverse S0 u = star u := by
  rw [reverse_formula S0 h0, Matrix.mulVec_mulVec,
    mul_eq_one_comm.mp hunit, Matrix.one_mulVec]

theorem reverse_involution (S0 : Matrix n n ℂ) (h0 : S0.transpose = S0)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    reverse S0 (reverse S0 u) = u := by
  rw [reverse, background_reverse S0 h0 hunit, star_star]

theorem reverse_power (S0 : Matrix n n ℂ)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    power (reverse S0 u) = power u := by
  rw [reverse, power_star, unitary_power S0 hunit]

theorem forward_reciprocity (S S0 : Matrix n n ℂ)
    (hS : S.transpose = S) (h0 : S0.transpose = S0)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    forward S S0 (reverse S0 u) = forward S S0 u := by
  unfold forward
  rw [background_reverse S0 h0 hunit, star_star, reverse,
    Matrix.dotProduct_mulVec, ← hS, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hS]

theorem extinction_reciprocity (S S0 : Matrix n n ℂ)
    (hS : S.transpose = S) (h0 : S0.transpose = S0)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    extinction S S0 (reverse S0 u) = extinction S S0 u := by
  simp [extinction, forward_reciprocity S S0 hS h0 hunit]

theorem contraction_power (S : Matrix n n ℂ)
    (hpass : ((1 : Matrix n n ℂ) - S.conjTranspose * S).PosSemidef)
    (u : n → ℂ) : power (S *ᵥ u) ≤ power u := by
  have h := (RCLike.nonneg_iff.mp (hpass.dotProduct_mulVec_nonneg u)).1
  rw [gram_power]
  simp [Matrix.sub_mulVec, dotProduct_sub, power] at h ⊢
  linarith

theorem residual_power (x y : n → ℂ) (t : ℝ) :
    power (x - (t : ℂ) • y) =
      power x - 2 * t * (star y ⬝ᵥ x).re + t ^ 2 * power y := by
  have hsym : (star x ⬝ᵥ y).re = (star y ⬝ᵥ x).re := by
    simpa using congrArg Complex.re (Matrix.star_dotProduct x y)
  simp [power, star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [hsym]
  ring

/-- One-input absorption is nonnegative and below the exact real-overlap
parabola. The real-overlap interval follows from the same residual square. -/
theorem one_input_parabola (S S0 : Matrix n n ℂ)
    (hunit : S0.conjTranspose * S0 = 1)
    (hpass : ((1 : Matrix n n ℂ) - S.conjTranspose * S).PosSemidef)
    (u : n → ℂ) (hu : power u = 1) :
    -1 ≤ (forward S S0 u).re ∧ (forward S S0 u).re ≤ 1 ∧
      0 ≤ absorption S u ∧
      absorption S u ≤ 1 - (forward S S0 u).re ^ 2 := by
  have hSu := contraction_power S hpass u
  rw [hu] at hSu
  have hS0u := unitary_power S0 hunit u
  rw [hu] at hS0u
  have hres := power_nonneg
    (S *ᵥ u - ((forward S S0 u).re : ℂ) • (S0 *ᵥ u))
  rw [residual_power, hS0u] at hres
  change 0 ≤ power (S *ᵥ u) -
    2 * (forward S S0 u).re * (forward S S0 u).re +
      (forward S S0 u).re ^ 2 * 1 at hres
  dsimp [absorption]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The finite-channel passivity parabola, with actual background reversal
and exact extinction reciprocity, applies to every reciprocal contraction. -/
theorem reciprocal_absorption_parabola (S S0 : Matrix n n ℂ)
    (hS : S.transpose = S) (h0 : S0.transpose = S0)
    (hunit : S0.conjTranspose * S0 = 1)
    (hpass : ((1 : Matrix n n ℂ) - S.conjTranspose * S).PosSemidef)
    (u : n → ℂ) (hu : power u = 1) :
    extinction S S0 (reverse S0 u) = extinction S S0 u ∧
      0 ≤ extinction S S0 u ∧ extinction S S0 u ≤ 4 ∧
      |absorption S u - absorption S (reverse S0 u)| ≤
        extinction S S0 u - (extinction S S0 u) ^ 2 / 4 := by
  have hv : power (reverse S0 u) = 1 := (reverse_power S0 hunit u).trans hu
  obtain ⟨hrlo, hrhi, hAu0, hAu1⟩ := one_input_parabola S S0 hunit hpass u hu
  obtain ⟨_, _, hAv0, hAv1⟩ := one_input_parabola S S0 hunit hpass (reverse S0 u) hv
  rw [forward_reciprocity S S0 hS h0 hunit] at hAv1
  refine ⟨extinction_reciprocity S S0 hS h0 hunit u, ?_, ?_, ?_⟩
  · dsimp [extinction]
    linarith
  · dsimp [extinction]
    linarith
  · rw [abs_le]
    dsimp [extinction]
    constructor <;> nlinarith

#print axioms reverse_involution
#print axioms forward_reciprocity
#print axioms reciprocal_absorption_parabola

end ChannelPowers
end GeneralizedResearch
