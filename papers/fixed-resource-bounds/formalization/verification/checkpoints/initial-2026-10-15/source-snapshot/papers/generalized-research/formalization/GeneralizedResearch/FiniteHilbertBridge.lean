import GeneralizedResearch.ChannelAttainment
import GeneralizedResearch.ChannelCoordinates
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Actual finite matrix equality witnesses embedded into the identical
Euclidean Hilbert channel model used by the arbitrary-dimensional upper bound.
The norms, powers, reference, reversal, reciprocity and extinction are proved
to agree; no informal model correspondence is assumed. -/
noncomputable section
namespace GeneralizedResearch
namespace FiniteHilbertBridge
open scoped Matrix ComplexOrder
open WithLp
variable {n : Type*} [Fintype n] [DecidableEq n]
abbrev H := EuclideanSpace ℂ n
def vector (v : n → ℂ) : H (n := n) := toLp 2 v

theorem inner_coordinates (u v : H (n := n)) :
    inner ℂ u v = star (ofLp u) ⬝ᵥ ofLp v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact dotProduct_comm _ _

theorem inner_vector (u v : n → ℂ) :
    inner ℂ (vector u) (vector v) = star u ⬝ᵥ v := inner_coordinates _ _

theorem norm_sq_coordinates (u : H (n := n)) :
    ‖u‖ ^ 2 = ChannelPowers.power (ofLp u) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_coordinates]
  rfl

def conjugation : ChannelConjugation (H (n := n)) where
  map u := vector (star (ofLp u))
  involution u := by ext i; simp [vector]
  inner_swap u v := by
    simp only [inner_coordinates, vector, ofLp_toLp, star_star]
    rw [dotProduct_comm]

theorem matrix_map (S : Matrix n n ℂ) (u : n → ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S (vector u) = vector (S *ᵥ u) := rfl

theorem matrix_reciprocal (S : Matrix n n ℂ) (hS : S.transpose = S) :
    channelReciprocal conjugation (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S) := by
  intro u v
  change inner ℂ (vector (star (ofLp u))) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S v) =
    inner ℂ (vector (star (ofLp v))) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S u)
  simp only [inner_coordinates, vector, ofLp_toLp, star_star,
    Matrix.ofLp_toEuclideanCLM]
  rw [Matrix.dotProduct_mulVec, ← hS, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hS]

theorem matrix_contraction (S : Matrix n n ℂ)
    (hpass : ((1 : Matrix n n ℂ) - S.conjTranspose * S).PosSemidef) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  have h := ChannelPowers.contraction_power S hpass (ofLp u)
  have h1 := norm_sq_coordinates (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S u)
  have h2 := norm_sq_coordinates u
  rw [Matrix.ofLp_toEuclideanCLM] at h1
  rw [← h1, ← h2] at h
  nlinarith [norm_nonneg u, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S u)]

def matrixIsometry (S0 : Matrix n n ℂ) (hunit : S0.conjTranspose * S0 = 1) :
    H (n := n) →ₗᵢ[ℂ] H (n := n) where
  toLinearMap := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0).toLinearMap
  norm_map' u := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0 u‖ = ‖u‖
    have h := ChannelPowers.unitary_power S0 hunit (ofLp u)
    have h1 := norm_sq_coordinates (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0 u)
    have h2 := norm_sq_coordinates u
    rw [Matrix.ofLp_toEuclideanCLM] at h1
    rw [← h1, ← h2] at h
    nlinarith [norm_nonneg u, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0 u)]

def matrixReference (S0 : Matrix n n ℂ) (hunit : S0.conjTranspose * S0 = 1) :
    H (n := n) ≃ₗᵢ[ℂ] H (n := n) :=
  LinearIsometryEquiv.ofLinearIsometry (matrixIsometry S0 hunit)
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0.conjTranspose).toLinearMap
    (by
      ext u i
      change (S0 *ᵥ (S0.conjTranspose *ᵥ ofLp u)) i = ofLp u i
      rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hunit, Matrix.one_mulVec])
    (by
      ext u i
      change (S0.conjTranspose *ᵥ (S0 *ᵥ ofLp u)) i = ofLp u i
      rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec])

theorem matrixReference_apply (S0 : Matrix n n ℂ)
    (hunit : S0.conjTranspose * S0 = 1) (u : H (n := n)) :
    matrixReference S0 hunit u = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0 u := rfl

theorem matrixReference_CLM (S0 : Matrix n n ℂ) (hunit : S0.conjTranspose * S0 = 1) :
    (matrixReference S0 hunit).toContinuousLinearEquiv.toContinuousLinearMap =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S0 := by ext u; rfl

theorem background_coordinates (S0 : Matrix n n ℂ)
    (hunit : S0.conjTranspose * S0 = 1) (u : n → ℂ) :
    backgroundReverse conjugation (matrixReference S0 hunit) (vector u) =
      vector (ChannelPowers.reverse S0 u) := by
  rw [backgroundReverse, matrixReference_apply, matrix_map]
  rfl

theorem absorption_coordinates (S : Matrix n n ℂ) (u : n → ℂ) :
    channelAbsorption (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) S) (vector u) = ChannelPowers.absorption S u := by
  unfold channelAbsorption ChannelPowers.absorption
  rw [norm_sq_coordinates, Matrix.ofLp_toEuclideanCLM]
  rfl

/-- A finite equality witness in the exact same Hilbert observables and
operator hypotheses as the universal upper bound. -/
def HilbertAttainment (rho r delta : ℝ) : Prop :=
  ∃ (n : ℕ) (C : ChannelConjugation (EuclideanSpace ℂ (Fin n)))
    (S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (S0 : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (u : EuclideanSpace ℂ (Fin n)),
    channelReciprocal C S ∧ channelReciprocal C S0.toContinuousLinearEquiv.toContinuousLinearMap ∧
    ‖S‖ ≤ 1 ∧ ‖u‖ = 1 ∧ ‖inner ℂ u (backgroundReverse C S0 u)‖ = rho ∧
    channelExtinction S S0.toContinuousLinearEquiv.toContinuousLinearMap u = 2 * (1 - r) ∧
    |channelAbsorption S u - channelAbsorption S (backgroundReverse C S0 u)| = delta

theorem finite_attainment_to_hilbert {rho r delta : ℝ}
    (h : ChannelAttainment.FiniteAttainment rho r delta) : HilbertAttainment rho r delta := by
  obtain ⟨n, S, S0, u, hS, hpass, h0, hunit, hu, hover, hforward, hdiff⟩ := h
  refine ⟨n, conjugation, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) S, matrixReference S0 hunit, vector u,
    matrix_reciprocal S hS, ?_, matrix_contraction S hpass, ?_, ?_, ?_, ?_⟩
  · rw [matrixReference_CLM]
    exact matrix_reciprocal S0 h0
  · have hn := norm_sq_coordinates (vector u)
    change ‖vector u‖ ^ 2 = ChannelPowers.power u at hn
    rw [hu] at hn
    nlinarith [norm_nonneg (vector u)]
  · rw [background_coordinates, inner_vector]
    exact hover
  · rw [matrixReference_CLM]
    unfold channelExtinction
    rw [matrix_map, matrix_map, inner_vector]
    change 2 * (1 - (ChannelPowers.forward S S0 u).re) = 2 * (1 - r)
    rw [hforward]
  · rw [background_coordinates, absorption_coordinates, absorption_coordinates]
    exact hdiff

#print axioms finite_attainment_to_hilbert
end FiniteHilbertBridge
end GeneralizedResearch
