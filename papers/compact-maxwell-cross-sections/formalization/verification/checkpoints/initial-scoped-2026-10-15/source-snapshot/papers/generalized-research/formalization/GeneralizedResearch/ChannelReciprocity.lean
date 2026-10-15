import GeneralizedResearch.ChannelPassivity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Complete Hilbert-channel reciprocity. A channel conjugation is specified by
its genuine antiunitary/involution properties. Reciprocal operators satisfy
the corresponding transpose symmetry, not an assumed extinction identity. -/

noncomputable section
namespace GeneralizedResearch
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

structure ChannelConjugation (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  map : E → E
  involution : Function.Involutive map
  inner_swap : ∀ x y, inner ℂ (map x) (map y) = inner ℂ y x

theorem ChannelConjugation.norm_map (C : ChannelConjugation E) (u : E) :
    ‖C.map u‖ = ‖u‖ := by
  have h := congrArg norm (C.inner_swap u u)
  simp [inner_self_eq_norm_sq_to_K, norm_pow] at h
  nlinarith [norm_nonneg (C.map u), norm_nonneg u]

def channelReciprocal (C : ChannelConjugation E) (S : E →L[ℂ] E) : Prop :=
  ∀ x y, inner ℂ (C.map x) (S y) = inner ℂ (C.map y) (S x)

def backgroundReverse (C : ChannelConjugation E) (S₀ : E ≃ₗᵢ[ℂ] E) (u : E) : E :=
  C.map (S₀ u)

theorem reciprocal_background_reverse (C : ChannelConjugation E)
    (S₀ : E ≃ₗᵢ[ℂ] E) (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (u : E) : S₀ (backgroundReverse C S₀ u) = C.map u := by
  apply ext_inner_left ℂ
  intro z
  have h := h₀ (C.map z) (C.map (S₀ u))
  change inner ℂ (C.map (C.map z)) (S₀ (C.map (S₀ u))) =
    inner ℂ (C.map (C.map (S₀ u))) (S₀ (C.map z)) at h
  rw [C.involution z, C.involution (S₀ u), S₀.inner_map_map] at h
  have hC := C.inner_swap (C.map z) u
  rw [C.involution z] at hC
  exact h.trans hC.symm

theorem backgroundReverse_involution (C : ChannelConjugation E)
    (S₀ : E ≃ₗᵢ[ℂ] E) (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap) :
    Function.Involutive (backgroundReverse C S₀) := by
  intro u
  change C.map (S₀ (backgroundReverse C S₀ u)) = u
  rw [reciprocal_background_reverse C S₀ h₀ u, C.involution]

theorem backgroundReverse_norm (C : ChannelConjugation E) (S₀ : E ≃ₗᵢ[ℂ] E) (u : E) :
    ‖backgroundReverse C S₀ u‖ = ‖u‖ := by
  rw [backgroundReverse, C.norm_map, S₀.norm_map]

theorem hilbert_forward_reciprocity (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap) (u : E) :
    inner ℂ (S₀ (backgroundReverse C S₀ u)) (S (backgroundReverse C S₀ u)) =
      inner ℂ (S₀ u) (S u) := by
  rw [reciprocal_background_reverse C S₀ h₀]
  rw [hS u (backgroundReverse C S₀ u)]
  rw [backgroundReverse, C.involution]

theorem hilbert_extinction_reciprocity (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap) (u : E) :
    channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap
      (backgroundReverse C S₀ u) =
    channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u := by
  unfold channelExtinction
  exact congrArg (fun z : ℂ => 2 * (1 - z.re))
    (hilbert_forward_reciprocity C S S₀ hS h₀ u)

theorem hilbert_reciprocal_absorption_parabola (C : ChannelConjugation E)
    (S : E →L[ℂ] E) (S₀ : E ≃ₗᵢ[ℂ] E) (hS : channelReciprocal C S)
    (h₀ : channelReciprocal C S₀.toContinuousLinearEquiv.toContinuousLinearMap)
    (hpass : ‖S‖ ≤ 1) (u : E) (hu : ‖u‖ = 1) :
    let X := channelExtinction S S₀.toContinuousLinearEquiv.toContinuousLinearMap u
    0 ≤ X ∧ X ≤ 4 ∧
      |channelAbsorption S u - channelAbsorption S (backgroundReverse C S₀ u)| ≤
        X - X ^ 2 / 4 := by
  have hv : ‖backgroundReverse C S₀ u‖ = 1 := (backgroundReverse_norm C S₀ u).trans hu
  have hSu : ‖S u‖ ≤ 1 := by
    exact (S.le_opNorm u).trans (by rw [hu, mul_one]; exact hpass)
  have hSv : ‖S (backgroundReverse C S₀ u)‖ ≤ 1 := by
    exact (S.le_opNorm _).trans (by rw [hv, mul_one]; exact hpass)
  have h₀u : ‖S₀.toContinuousLinearEquiv.toContinuousLinearMap u‖ = 1 :=
    (S₀.norm_map u).trans hu
  have h₀v : ‖S₀.toContinuousLinearEquiv.toContinuousLinearMap (backgroundReverse C S₀ u)‖ = 1 :=
    (S₀.norm_map _).trans hv
  have h := channel_passivity_parabola S S₀.toContinuousLinearEquiv.toContinuousLinearMap u h₀u hSu
  exact ⟨h.1, h.2.1, equal_extinction_absorption_difference S
    S₀.toContinuousLinearEquiv.toContinuousLinearMap u (backgroundReverse C S₀ u)
    h₀u h₀v hSu hSv (hilbert_extinction_reciprocity C S S₀ hS h₀ u)⟩

end GeneralizedResearch
