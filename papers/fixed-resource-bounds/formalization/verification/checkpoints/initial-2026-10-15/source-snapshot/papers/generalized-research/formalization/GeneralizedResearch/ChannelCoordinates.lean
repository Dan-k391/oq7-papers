import GeneralizedResearch.ChannelReciprocity

/-! Algebra of actual antiunitary channel reversal and removal of a reciprocal
lossless background. These identities support canonical coordinate reduction;
they do not assume a canonical basis or an optimization bound. -/

noncomputable section
namespace GeneralizedResearch
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ChannelConjugation.map_add (C : ChannelConjugation E) (x y : E) :
    C.map (x + y) = C.map x + C.map y := by
  apply ext_inner_left ℂ
  intro z
  calc
    inner ℂ z (C.map (x + y)) = inner ℂ (x + y) (C.map z) := by
      simpa only [C.involution z] using C.inner_swap (C.map z) (x + y)
    _ = inner ℂ x (C.map z) + inner ℂ y (C.map z) := inner_add_left _ _ _
    _ = inner ℂ z (C.map x) + inner ℂ z (C.map y) := by
      rw [← C.inner_swap (C.map z) x, ← C.inner_swap (C.map z) y, C.involution]
    _ = inner ℂ z (C.map x + C.map y) := (inner_add_right _ _ _).symm

theorem ChannelConjugation.map_zero (C : ChannelConjugation E) : C.map 0 = 0 := by
  have h := C.map_add 0 0
  have he : C.map 0 + C.map 0 = C.map 0 + 0 := by simpa using h.symm
  exact add_left_cancel he

theorem ChannelConjugation.map_smul (C : ChannelConjugation E) (a : ℂ) (x : E) :
    C.map (a • x) = star a • C.map x := by
  apply ext_inner_left ℂ
  intro z
  calc
    inner ℂ z (C.map (a • x)) = inner ℂ (a • x) (C.map z) := by
      simpa only [C.involution z] using C.inner_swap (C.map z) (a • x)
    _ = star a * inner ℂ x (C.map z) := inner_smul_left _ _ _
    _ = star a * inner ℂ z (C.map x) := by
      rw [← C.inner_swap (C.map z) x, C.involution]
    _ = inner ℂ z (star a • C.map x) := (inner_smul_right _ _ _).symm

def backgroundConjugation (C : ChannelConjugation E) (S₀ : E ≃ₗᵢ[ℂ] E)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap) :
    ChannelConjugation E where
  map := backgroundReverse C S₀
  involution := backgroundReverse_involution C S₀ h₀
  inner_swap x y := by
    change inner ℂ (C.map (S₀ x)) (C.map (S₀ y)) = inner ℂ y x
    rw [C.inner_swap, S₀.inner_map_map]

def normalizedScatterer (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) : E →L[ℂ] E :=
  S₀.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S

theorem normalizedScatterer_norm_le (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) :
    ‖normalizedScatterer S S₀‖ ≤ ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
  intro u
  change ‖S₀.symm (S u)‖ ≤ ‖S‖ * ‖u‖
  rw [S₀.symm.norm_map]
  exact S.le_opNorm u

theorem normalizedScatterer_reciprocal (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap) :
    channelReciprocal (backgroundConjugation C S₀ h₀) (normalizedScatterer S S₀) := by
  have h (x y : E) : inner ℂ (backgroundReverse C S₀ x) (S₀.symm (S y)) =
      inner ℂ (C.map x) (S y) := by
    have he := S₀.inner_map_map (backgroundReverse C S₀ x) (S₀.symm (S y))
    rw [S₀.apply_symm_apply, reciprocal_background_reverse C S₀ h₀] at he
    exact he.symm
  intro x y
  change inner ℂ (backgroundReverse C S₀ x) (S₀.symm (S y)) =
    inner ℂ (backgroundReverse C S₀ y) (S₀.symm (S x))
  rw [h, h, hS]

theorem normalizedScatterer_absorption (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (u : E) :
    channelAbsorption (normalizedScatterer S S₀) u = channelAbsorption S u := by
  unfold channelAbsorption
  change 1 - ‖S₀.symm (S u)‖ ^ 2 = 1 - ‖S u‖ ^ 2
  rw [S₀.symm.norm_map]

theorem normalizedScatterer_extinction (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (u : E) :
    channelExtinction (normalizedScatterer S S₀) (ContinuousLinearMap.id ℂ E) u =
      channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u := by
  have h := S₀.inner_map_map u (S₀.symm (S u))
  rw [S₀.apply_symm_apply] at h
  unfold channelExtinction
  change 2 * (1 - (inner ℂ u (S₀.symm (S u))).re) =
    2 * (1 - (inner ℂ (S₀ u) (S u)).re)
  rw [h]

end GeneralizedResearch
