import GeneralizedResearch.ChannelEquality
import GeneralizedResearch.FiniteHilbertBridge

/-! The universal reciprocal Hilbert-channel parabola and exact finite-channel
attainment are expressed here in the same observables. The literal three-port
matrix is the separately proved OrthogonalSharpness.S construction. -/
noncomputable section
namespace GeneralizedResearch
namespace ChannelParabola

theorem sharpness {X : ℝ} (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    FiniteHilbertBridge.HilbertAttainment 0 (1 - X / 2) (X - X ^ 2 / 4) := by
  have ht0 : -1 ≤ 1 - X / 2 := by linarith
  have ht1 : 1 - X / 2 ≤ 1 := by linarith
  have h := FiniteHilbertBridge.finite_attainment_to_hilbert
    (ChannelAttainment.orthogonal_branch_attainment ht0 ht1)
  have heq : 1 - (1 - X / 2) ^ 2 = X - X ^ 2 / 4 := by ring
  rwa [heq] at h

/-- Theorem 6.2: arbitrary-reference Hilbert upper bound and exact orthogonal
reversed-input Hilbert sharpness for every X in the closed interval. Equality
and both endpoint behaviors are ChannelEquality.reversed_equality_iff and
ChannelEquality.reversed_endpoint_zero/four. -/
theorem theorem62 {X : ℝ} (hX0 : 0 ≤ X) (hX4 : X ≤ 4) :
    (∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (C : ChannelConjugation E) (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E),
      channelReciprocal C S →
      channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap →
      ‖S‖ ≤ 1 → ∀ u : E, ‖u‖ = 1 →
      channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u = X →
      |channelAbsorption S u - channelAbsorption S (backgroundReverse C S₀ u)| ≤
        X - X ^ 2 / 4) ∧
    FiniteHilbertBridge.HilbertAttainment 0 (1 - X / 2) (X - X ^ 2 / 4) := by
  constructor
  · intro E instNorm instInner C S S₀ hS h₀ hpass u hu hX
    have h := hilbert_reciprocal_absorption_parabola C S S₀ hS h₀ hpass u hu
    simpa only [hX] using h.2.2
  · exact sharpness hX0 hX4

end ChannelParabola
end GeneralizedResearch
