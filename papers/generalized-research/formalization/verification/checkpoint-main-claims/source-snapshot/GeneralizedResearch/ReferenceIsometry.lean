import GeneralizedResearch.CanonicalPair

/-! A reciprocal lossless bounded reference is onto, including in infinite
dimension. Thus the unitary-reference parametrization introduces no stronger
assumption than the manuscript's reciprocal `S0† S0 = I` condition. -/

noncomputable section
namespace GeneralizedResearch
namespace ReferenceIsometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def isometry (A : E →L[ℂ] E) (hn : ∀ u, ‖A u‖ = ‖u‖) : E →ₗᵢ[ℂ] E where
  toLinearMap := A.toLinearMap
  norm_map' := hn

theorem reverse_identity (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hA : channelReciprocal C A) (hn : ∀ u, ‖A u‖ = ‖u‖) (u : E) :
    A (C.map (A u)) = C.map u := by
  apply ext_inner_left ℂ
  intro z
  have h := hA (C.map z) (C.map (A u))
  rw [C.involution z,C.involution (A u)] at h
  have hi : inner ℂ (A u) (A (C.map z)) = inner ℂ u (C.map z) :=
    (isometry A hn).inner_map_map u (C.map z)
  rw [hi] at h
  have hC := C.inner_swap (C.map z) u
  rw [C.involution z] at hC
  exact h.trans hC.symm

theorem surjective (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hA : channelReciprocal C A) (hn : ∀ u, ‖A u‖ = ‖u‖) : Function.Surjective A := by
  intro v
  refine ⟨C.map (A (C.map v)),?_⟩
  rw [reverse_identity C A hA hn,C.involution v]

def equiv (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hA : channelReciprocal C A) (hn : ∀ u, ‖A u‖ = ‖u‖) : E ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective (isometry A hn) (surjective C A hA hn)

theorem equiv_apply (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hA : channelReciprocal C A) (hn : ∀ u, ‖A u‖ = ‖u‖) (u : E) :
    equiv C A hA hn u = A u := rfl

theorem equiv_clm (C : ChannelConjugation E) (A : E →L[ℂ] E)
    (hA : channelReciprocal C A) (hn : ∀ u, ‖A u‖ = ‖u‖) :
    (equiv C A hA hn).toContinuousLinearEquiv.toContinuousLinearMap = A := by
  ext u
  rfl

theorem norm_map_of_adjoint [CompleteSpace E] (A : E →L[ℂ] E)
    (hunit : A.adjoint.comp A = ContinuousLinearMap.id ℂ E) (u : E) : ‖A u‖ = ‖u‖ := by
  have h := A.apply_norm_sq_eq_inner_adjoint_right u
  rw [hunit,ContinuousLinearMap.id_apply,inner_self_eq_norm_sq (𝕜 := ℂ) u] at h
  nlinarith [norm_nonneg (A u),norm_nonneg u]

/-- The literal bounded-operator reference formulation, without assuming its
surjectivity or a preselected canonical basis. -/
theorem full_overlap_upper_clm [CompleteSpace E] (p : OverlapParameters)
    (C : ChannelConjugation E) (S A : E →L[ℂ] E)
    (hS : channelReciprocal C S) (hA : channelReciprocal C A)
    (hunit : A.adjoint.comp A = ContinuousLinearMap.id ℂ E)
    (hpass : ‖S‖ ≤ 1) (u : E) (hu : ‖u‖ = 1)
    (hρ : ‖inner ℂ u (C.map (A u))‖ = p.rho) :
    |channelAbsorption S u - channelAbsorption S (C.map (A u))| ≤
      p.envelope |1 - channelExtinction S A u / 2| := by
  let W := equiv C A hA (norm_map_of_adjoint A hunit)
  have hW : W.toContinuousLinearEquiv.toContinuousLinearMap = A :=
    equiv_clm C A hA _
  have hrec : channelReciprocal C W.toContinuousLinearEquiv.toContinuousLinearMap := by
    rwa [hW]
  have hover : ‖inner ℂ u (backgroundReverse C W u)‖ = p.rho := hρ
  have h := CanonicalPair.full_overlap_upper p C S W hS hrec hpass u hu hover
  rwa [hW] at h

end ReferenceIsometry
end GeneralizedResearch
