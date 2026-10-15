import GeneralizedResearch.ChannelReciprocity

/-! Equality and endpoint cases for the full Hilbert-channel extinction
parabola. The equal-extinction hypothesis is derived from reciprocity in the
exported reversed-input theorem. -/

noncomputable section
namespace GeneralizedResearch
namespace ChannelEquality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem abs_sub_eq_interval {p q B : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ B)
    (hq0 : 0 ≤ q) (hq : q ≤ B) :
    |p - q| = B ↔ (p = B ∧ q = 0) ∨ (q = B ∧ p = 0) := by
  by_cases hqp : q ≤ p
  · rw [abs_of_nonneg (sub_nonneg.mpr hqp)]
    constructor
    · intro h
      exact Or.inl ⟨by linarith, by linarith⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> linarith
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hqp))]
    constructor
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> linarith

theorem absorption_zero_iff (S : E →L[ℂ] E) (u : E) :
    channelAbsorption S u = 0 ↔ ‖S u‖ = 1 := by
  unfold channelAbsorption
  constructor
  · intro h
    nlinarith [norm_nonneg (S u)]
  · intro h
    simp only [h, one_pow, sub_self]

/-- Complete equality characterization, before specializing the second input
to its reciprocal background reverse. It also remains valid at X=0 and X=4. -/
theorem equal_extinction_equality_iff (S S₀ : E →L[ℂ] E) (u v : E)
    (hu₀ : ‖S₀ u‖ = 1) (hv₀ : ‖S₀ v‖ = 1)
    (huS : ‖S u‖ ≤ 1) (hvS : ‖S v‖ ≤ 1)
    (hX : channelExtinction S S₀ v = channelExtinction S S₀ u) :
    let X := channelExtinction S S₀ u
    |channelAbsorption S u - channelAbsorption S v| = X - X ^ 2 / 4 ↔
      (S u = ((1 - X / 2 : ℝ) : ℂ) • S₀ u ∧ ‖S v‖ = 1) ∨
      (S v = ((1 - X / 2 : ℝ) : ℂ) • S₀ v ∧ ‖S u‖ = 1) := by
  dsimp only
  have hu := channel_passivity_parabola S S₀ u hu₀ huS
  have hv := channel_passivity_parabola S S₀ v hv₀ hvS
  rw [hX] at hv
  rw [abs_sub_eq_interval hu.2.2.1 hu.2.2.2 hv.2.2.1 hv.2.2.2]
  have hueq := channel_parabola_equality_iff S S₀ u hu₀
  have hveq := channel_parabola_equality_iff S S₀ v hv₀
  rw [hX] at hveq
  rw [hueq, hveq, absorption_zero_iff, absorption_zero_iff]

theorem endpoint_zero (S S₀ : E →L[ℂ] E) (u : E)
    (hu₀ : ‖S₀ u‖ = 1) (huS : ‖S u‖ ≤ 1)
    (hX : channelExtinction S S₀ u = 0) : S u = S₀ u ∧ channelAbsorption S u = 0 := by
  have h := channel_passivity_parabola S S₀ u hu₀ huS
  rw [hX] at h
  have hA : channelAbsorption S u = 0 := by nlinarith [h.2.2.1, h.2.2.2]
  have hAe : channelAbsorption S u =
      channelExtinction S S₀ u - channelExtinction S S₀ u ^ 2 / 4 := by
    rw [hX, hA]
    norm_num
  have heq := (channel_parabola_equality_iff S S₀ u hu₀).mp hAe
  simpa only [hX, zero_div, sub_zero, Complex.ofReal_one, one_smul] using And.intro heq hA

theorem endpoint_four (S S₀ : E →L[ℂ] E) (u : E)
    (hu₀ : ‖S₀ u‖ = 1) (huS : ‖S u‖ ≤ 1)
    (hX : channelExtinction S S₀ u = 4) : S u = -S₀ u ∧ channelAbsorption S u = 0 := by
  have h := channel_passivity_parabola S S₀ u hu₀ huS
  rw [hX] at h
  have hA : channelAbsorption S u = 0 := by nlinarith [h.2.2.1, h.2.2.2]
  have hAe : channelAbsorption S u =
      channelExtinction S S₀ u - channelExtinction S S₀ u ^ 2 / 4 := by
    rw [hX, hA]
    norm_num
  have heq := (channel_parabola_equality_iff S S₀ u hu₀).mp hAe
  norm_num only [hX, show (1 : ℝ) - 4 / 2 = -1 by norm_num,
    Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul] at heq
  exact ⟨heq, hA⟩

/-- The signed scattering/absorption reciprocity identity of original
Proposition 6.1 for arbitrary complex Hilbert channels. -/
theorem reciprocal_power_difference (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (u : E) (hu : ‖u‖ = 1) :
    channelAbsorption S u - channelAbsorption S (backgroundReverse C S₀ u) =
      -(channelScattering S S₀.toContinuousLinearEquiv.toContinuousLinearMap u -
        channelScattering S S₀.toContinuousLinearEquiv.toContinuousLinearMap
          (backgroundReverse C S₀ u)) := by
  have hv := (backgroundReverse_norm C S₀ u).trans hu
  have hu₀ := (S₀.norm_map u).trans hu
  have hv₀ := (S₀.norm_map (backgroundReverse C S₀ u)).trans hv
  have hpu := channel_power_identity S S₀.toContinuousLinearEquiv.toContinuousLinearMap u hu₀
  have hpv := channel_power_identity S S₀.toContinuousLinearEquiv.toContinuousLinearMap
    (backgroundReverse C S₀ u) hv₀
  have hX := hilbert_extinction_reciprocity C S S₀ hS h₀ u
  linarith

/-- Literal equation (47), including both possible input orderings, in the
arbitrary-reference reciprocal Hilbert channel model. -/
theorem reversed_equality_iff (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (hpass : ‖S‖ ≤ 1) (u : E) (hu : ‖u‖ = 1) :
    let v := backgroundReverse C S₀ u
    let X := channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u
    |channelAbsorption S u - channelAbsorption S v| = X - X ^ 2 / 4 ↔
      (S u = ((1 - X / 2 : ℝ) : ℂ) • S₀ u ∧ ‖S v‖ = 1) ∨
      (S v = ((1 - X / 2 : ℝ) : ℂ) • S₀ v ∧ ‖S u‖ = 1) := by
  have hv := (backgroundReverse_norm C S₀ u).trans hu
  have hu₀ := (S₀.norm_map u).trans hu
  have hv₀ := (S₀.norm_map (backgroundReverse C S₀ u)).trans hv
  have huS : ‖S u‖ ≤ 1 := (S.le_opNorm u).trans (by rw [hu, mul_one]; exact hpass)
  have hvS : ‖S (backgroundReverse C S₀ u)‖ ≤ 1 :=
    (S.le_opNorm _).trans (by rw [hv, mul_one]; exact hpass)
  exact equal_extinction_equality_iff S S₀.toContinuousLinearEquiv.toContinuousLinearMap
    u (backgroundReverse C S₀ u) hu₀ hv₀ huS hvS
    (hilbert_extinction_reciprocity C S S₀ hS h₀ u)

theorem reversed_endpoint_zero (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (hpass : ‖S‖ ≤ 1) (u : E) (hu : ‖u‖ = 1)
    (hX : channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u = 0) :
    let v := backgroundReverse C S₀ u
    S u = S₀ u ∧ S v = S₀ v ∧ channelAbsorption S u = 0 ∧ channelAbsorption S v = 0 := by
  have hv := (backgroundReverse_norm C S₀ u).trans hu
  have hu₀ := (S₀.norm_map u).trans hu
  have hv₀ := (S₀.norm_map (backgroundReverse C S₀ u)).trans hv
  have huS : ‖S u‖ ≤ 1 := (S.le_opNorm u).trans (by rw [hu, mul_one]; exact hpass)
  have hvS : ‖S (backgroundReverse C S₀ u)‖ ≤ 1 :=
    (S.le_opNorm _).trans (by rw [hv, mul_one]; exact hpass)
  have hXv := (hilbert_extinction_reciprocity C S S₀ hS h₀ u).trans hX
  have hpu := endpoint_zero S S₀.toContinuousLinearEquiv.toContinuousLinearMap u hu₀ huS hX
  have hpv := endpoint_zero S S₀.toContinuousLinearEquiv.toContinuousLinearMap
    (backgroundReverse C S₀ u) hv₀ hvS hXv
  exact ⟨hpu.1, hpv.1, hpu.2, hpv.2⟩

theorem reversed_endpoint_four (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (hpass : ‖S‖ ≤ 1) (u : E) (hu : ‖u‖ = 1)
    (hX : channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u = 4) :
    let v := backgroundReverse C S₀ u
    S u = -S₀ u ∧ S v = -S₀ v ∧ channelAbsorption S u = 0 ∧ channelAbsorption S v = 0 := by
  have hv := (backgroundReverse_norm C S₀ u).trans hu
  have hu₀ := (S₀.norm_map u).trans hu
  have hv₀ := (S₀.norm_map (backgroundReverse C S₀ u)).trans hv
  have huS : ‖S u‖ ≤ 1 := (S.le_opNorm u).trans (by rw [hu, mul_one]; exact hpass)
  have hvS : ‖S (backgroundReverse C S₀ u)‖ ≤ 1 :=
    (S.le_opNorm _).trans (by rw [hv, mul_one]; exact hpass)
  have hXv := (hilbert_extinction_reciprocity C S S₀ hS h₀ u).trans hX
  have hpu := endpoint_four S S₀.toContinuousLinearEquiv.toContinuousLinearMap u hu₀ huS hX
  have hpv := endpoint_four S S₀.toContinuousLinearEquiv.toContinuousLinearMap
    (backgroundReverse C S₀ u) hv₀ hvS hXv
  exact ⟨hpu.1, hpv.1, hpu.2, hpv.2⟩

theorem reversed_scattering_difference_abs (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (u : E) (hu : ‖u‖ = 1) :
    |channelAbsorption S u - channelAbsorption S (backgroundReverse C S₀ u)| =
      |channelScattering S S₀.toContinuousLinearEquiv.toContinuousLinearMap u -
        channelScattering S S₀.toContinuousLinearEquiv.toContinuousLinearMap
          (backgroundReverse C S₀ u)| := by
  rw [reciprocal_power_difference C S S₀ hS h₀ u hu, abs_neg]

end ChannelEquality
end GeneralizedResearch
