import GeneralizedResearch.MainTheorem

/-! Dimension-preserving equality witnesses for the overlap envelope.
The first two branches use two channels and the last uses three. -/
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch
namespace SmallAttainment
open scoped Matrix ComplexOrder
open ChannelAttainment

def At (n : ℕ) (rho r delta : ℝ) : Prop :=
  ∃ S S0 : Matrix (Fin n) (Fin n) ℂ, ∃ u : Fin n → ℂ,
    S.transpose = S ∧ ((1 : Matrix (Fin n) (Fin n) ℂ) - S.conjTranspose * S).PosSemidef ∧
    S0.transpose = S0 ∧ S0.conjTranspose * S0 = 1 ∧
    ChannelPowers.power u = 1 ∧
    ‖star u ⬝ᵥ ChannelPowers.reverse S0 u‖ = rho ∧
    (ChannelPowers.forward S S0 u).re = r ∧
    |ChannelPowers.absorption S u - ChannelPowers.absorption S (ChannelPowers.reverse S0 u)| = delta

theorem first {rho r : ℝ} (h0 : 0 < rho) (h1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ rho / 2) : At 2 rho r (Real.sqrt (1 - rho ^ 2)) :=
  ⟨firstScatterer rho r, background, input rho, first_symmetric rho r,
    first_passive h0 hr0 hr1, background_symmetric, background_unitary,
    input_power h0 h1, input_overlap h0 h1, first_forward h0 h1,
    first_difference h0 h1 hr0 hr1⟩

theorem middle (p : MiddleParameters) :
    At 2 p.rho p.r (2 * Real.sqrt (1 - p.rho ^ 2) * p.h) :=
  ⟨middleScatterer p, background, input p.rho, middle_symmetric p,
    middle_passive p, background_symmetric, background_unitary,
    input_power p.rho_pos p.rho_lt_one, input_overlap p.rho_pos p.rho_lt_one,
    middle_forward p, middle_difference p⟩

theorem real_at {n : ℕ} {rho r delta : ℝ}
    (S S0 : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ)
    (hS : S.transpose = S)
    (hpass : ((1 : Matrix (Fin n) (Fin n) ℝ) - S.transpose * S).PosSemidef)
    (hS0 : S0.transpose = S0) (hunit : S0.transpose * S0 = 1)
    (hrev : S0 *ᵥ a = b) (ha : a ⬝ᵥ a = 1) (hrel : a ⬝ᵥ b = rho) (hrho : 0 ≤ rho)
    (hforward : b ⬝ᵥ (S *ᵥ a) = r)
    (hdiff : (S *ᵥ a) ⬝ᵥ (S *ᵥ a) - (S *ᵥ b) ⬝ᵥ (S *ᵥ b) = delta)
    (hdelta : 0 ≤ delta) : At n rho r delta := by
  have hreverse : ChannelPowers.reverse (complexify S0) (realVector a) = realVector b := by
    rw [ChannelPowers.reverse, complexify_mulVec, hrev, realVector_star]
  refine ⟨complexify S, complexify S0, realVector a, ?_,
    complexify_contraction S hpass, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [complexify_transpose, hS]
  · rw [complexify_transpose, hS0]
  · rw [complexify_conjTranspose, ← complexify_mul, hunit, complexify_one]
  · rw [realVector_power, ha]
  · rw [hreverse, realVector_dot, hrel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrho]
  · rw [ChannelPowers.forward, complexify_mulVec, hrev, complexify_mulVec,
      realVector_dot, hforward, Complex.ofReal_re]
  · simp only [ChannelPowers.absorption, hreverse, complexify_mulVec, realVector_power]
    have hid : 1 - (S *ᵥ a) ⬝ᵥ (S *ᵥ a) - (1 - (S *ᵥ b) ⬝ᵥ (S *ᵥ b)) = -delta := by
      linarith
    rw [hid, abs_neg, abs_of_nonneg hdelta]

theorem third (p : ThirdBranch.Parameters) : At 3 p.rho p.r (1 - p.r ^ 2) := by
  apply real_at p.S p.S0 ThirdBranch.Parameters.a p.b p.S_symmetric p.S_contraction p.S0_symmetric
  · rw [p.S0_symmetric, ← pow_two, p.S0_square]
  · exact p.background_reversal
  · exact p.input_norms.1
  · exact p.input_overlap
  · exact p.rho_pos.le
  · exact p.forward_overlap
  · exact p.absorption_difference
  · nlinarith [p.r_pos, p.r_le_one]

theorem At.neg {n : ℕ} {rho r delta : ℝ} (h : At n rho r delta) : At n rho (-r) delta := by
  obtain ⟨S, S0, u, hS, hpass, h0, hunit, hu, hover, hforward, hdiff⟩ := h
  refine ⟨-S, S0, u, ?_, ?_, h0, hunit, hu, hover, ?_, ?_⟩
  · simp only [Matrix.transpose_neg, hS]
  · simpa only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] using hpass
  · simpa only [ChannelPowers.forward, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] using
      congrArg (fun x : ℝ => -x) hforward
  · simpa only [ChannelPowers.absorption, Matrix.neg_mulVec, power_neg] using hdiff

theorem all_branches (p : OverlapParameters) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ n : ℕ, n ≤ 3 ∧ At n p.rho r (p.envelope r) := by
  unfold OverlapParameters.envelope
  split_ifs with hlo hhi
  · exact ⟨2, by norm_num, first p.rho_pos p.rho_lt_one hr0 hlo⟩
  · let m := p.middle r ⟨lt_of_not_ge hlo, hhi⟩
    have hm := middle m
    have hmr : m.r = r := p.middle_r r _
    rw [hmr] at hm
    exact ⟨2, by norm_num, hm⟩
  · let q : ThirdBranch.Parameters := {
      rho := p.rho, r := r, rho_pos := p.rho_pos, rho_lt_one := p.rho_lt_one,
      rho_le_r := le_of_not_gt hhi, r_le_one := hr1 }
    exact ⟨3, le_rfl, third q⟩

theorem prescribed_extinction (p : OverlapParameters) (X : ℝ) (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    ∃ n : ℕ, n ≤ 3 ∧ At n p.rho (1 - X / 2) (p.envelope |1 - X / 2|) := by
  have hr : |1 - X / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨n, hn, h⟩ := all_branches p |1 - X / 2| (abs_nonneg _) hr
  refine ⟨n, hn, ?_⟩
  by_cases hpos : 0 ≤ 1 - X / 2
  · simpa only [abs_of_nonneg hpos] using h
  · have hneg := h.neg
    have heq : -|1 - X / 2| = 1 - X / 2 := by
      rw [abs_of_neg (lt_of_not_ge hpos), neg_neg]
    rwa [heq] at hneg

def HilbertAt (n : ℕ) (rho r delta : ℝ) : Prop :=
  ∃ (C : ChannelConjugation (EuclideanSpace ℂ (Fin n)))
    (S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (S0 : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (u : EuclideanSpace ℂ (Fin n)),
    channelReciprocal C S ∧ channelReciprocal C S0.toContinuousLinearEquiv.toContinuousLinearMap ∧
    ‖S‖ ≤ 1 ∧ ‖u‖ = 1 ∧ ‖inner ℂ u (backgroundReverse C S0 u)‖ = rho ∧
    channelExtinction S S0.toContinuousLinearEquiv.toContinuousLinearMap u = 2 * (1 - r) ∧
    |channelAbsorption S u - channelAbsorption S (backgroundReverse C S0 u)| = delta

theorem to_hilbert {n : ℕ} {rho r delta : ℝ} (h : At n rho r delta) : HilbertAt n rho r delta := by
  open FiniteHilbertBridge in
    obtain ⟨S, S0, u, hS, hpass, h0, hunit, hu, hover, hforward, hdiff⟩ := h
    refine ⟨conjugation, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) S, matrixReference S0 hunit,
      vector u, matrix_reciprocal S hS, ?_, matrix_contraction S hpass, ?_, ?_, ?_, ?_⟩
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

/-- Exact equality in at most three genuine Hilbert channels. -/
theorem theorem71_dimension (p : OverlapParameters) (X : ℝ) (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    Theorem71Upper.{u} p X ∧
      ∃ n : ℕ, n ≤ 3 ∧ HilbertAt n p.rho (1 - X / 2) (p.envelope |1 - X / 2|) := by
  refine ⟨(theorem71 p X hX0 hX4).1, ?_⟩
  obtain ⟨n, hn, h⟩ := prescribed_extinction p X hX0 hX4
  exact ⟨n, hn, to_hilbert h⟩

end SmallAttainment
end GeneralizedResearch
