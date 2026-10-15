import PrescribedExtinction.SetSupportedL2
import PrescribedExtinction.OutgoingDissipativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

abbrev BodyCurrentL2 (B : TwoLayerBody) := SetSupportedL2 (E := Vector) volume B.domain

instance bodyCurrentL2_completeSpace (B : TwoLayerBody) : CompleteSpace (BodyCurrentL2 B) := by
  let : IsClosed (setSupportedL2 (E := Vector) volume B.domain : Set VectorL2) :=
    setSupportedL2_isClosed volume B.domain (bodyDomain_isOpen B).measurableSet
  exact inferInstance

def bodySupportRadius (B : TwoLayerBody) : ℝ :=
  B.aperture + B.absorberThickness + B.plateThickness

theorem bodySupportRadius_nonneg (B : TwoLayerBody) : 0 ≤ bodySupportRadius B := by
  unfold bodySupportRadius
  linarith [B.aperture_pos, B.absorberThickness_pos, B.plateThickness_pos]

def bodyCurrentInclusionLinear (B : TwoLayerBody) :
    BodyCurrentL2 B →ₗ[ℂ] SupportedVectorL2 (bodySupportRadius B) where
  toFun f := ⟨(f : VectorL2), by
    change ∀ᵐ x ∂volume, x ∉ Metric.closedBall 0 (bodySupportRadius B) → (f : VectorL2) x = 0
    filter_upwards [f.property] with x hx
    intro hxb
    exact hx (fun hxd => hxb (domain_subset_closedBall B hxd))⟩
  map_add' f g := Subtype.ext rfl
  map_smul' z f := Subtype.ext rfl

def bodyCurrentInclusion (B : TwoLayerBody) :
    BodyCurrentL2 B →L[ℂ] SupportedVectorL2 (bodySupportRadius B) :=
  (bodyCurrentInclusionLinear B).mkContinuous 1 fun f => by
    change ‖(f : VectorL2)‖ ≤ 1 * ‖(f : VectorL2)‖
    simp

def bodyOutgoingOperator (k : ℝ) (B : TwoLayerBody) : BodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  setRestrictionCLM volume B.domain (bodyDomain_isOpen B).measurableSet ∘L
    (supportedVectorL2 (bodySupportRadius B)).subtypeL ∘L
      compactOutgoingOperator k (bodySupportRadius B) (bodySupportRadius_nonneg B) ∘L
        bodyCurrentInclusion B

theorem bodyOutgoingOperator_inner (k : ℝ) (B : TwoLayerBody) (f : BodyCurrentL2 B) :
    inner ℂ f (bodyOutgoingOperator k B f) =
      inner ℂ (bodyCurrentInclusion B f)
        (compactOutgoingOperator k (bodySupportRadius B) (bodySupportRadius_nonneg B)
          (bodyCurrentInclusion B f)) := by
  change inner ℂ (f : VectorL2) (setRestrictionCLM volume B.domain (bodyDomain_isOpen B).measurableSet
    (compactOutgoingOperator k (bodySupportRadius B) (bodySupportRadius_nonneg B)
      (bodyCurrentInclusion B f) : VectorL2) : VectorL2) = _
  rw [setRestrictionCLM_inner volume B.domain (bodyDomain_isOpen B).measurableSet f]
  rfl

theorem bodyOutgoingOperator_im_nonneg (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (f : BodyCurrentL2 B) :
    0 ≤ (inner ℂ f (bodyOutgoingOperator k B f)).im := by
  rw [bodyOutgoingOperator_inner]
  exact compactOutgoingOperator_im_nonneg k hk _ _ _

def bodyCurrentPolarization (B : TwoLayerBody) (f : BodyCurrentL2 B) : CompactPolarization where
  current := B.domain.indicator (fun x => (f : VectorL2) x)
  radius := bodySupportRadius B
  radius_nonneg := bodySupportRadius_nonneg B
  memLp := (Lp.memLp (f : VectorL2)).indicator (bodyDomain_isOpen B).measurableSet
  vanish x hx := by
    have hnot : x ∉ B.domain := by
      intro hd
      have hb := domain_subset_closedBall B hd
      have hn : ‖x‖ ≤ bodySupportRadius B := by simpa only [bodySupportRadius, Metric.mem_closedBall, dist_zero_right] using hb
      exact hx.not_ge hn
    simp [hnot]

theorem bodyCurrentPolarization_current_ae (B : TwoLayerBody) (f : BodyCurrentL2 B) :
    (bodyCurrentPolarization B f).current =ᵐ[volume] (f : VectorL2) := by
  filter_upwards [f.property] with x hx
  by_cases hxd : x ∈ B.domain
  · simp [bodyCurrentPolarization, hxd]
  · simp [bodyCurrentPolarization, hxd, hx hxd]

theorem bodyOutgoingOperator_coe (k : ℝ) (B : TwoLayerBody) (f : BodyCurrentL2 B) :
    (bodyOutgoingOperator k B f : VectorL2) =ᵐ[volume]
      B.domain.indicator (electricVolumeField k (bodyCurrentPolarization B f)) := by
  have hcur : (supportedPolarization (bodySupportRadius B) (bodySupportRadius_nonneg B)
      (bodyCurrentInclusion B f)).current =ᵐ[volume] (bodyCurrentPolarization B f).current :=
    (supportedPolarization_current_ae _ _ _).trans (bodyCurrentPolarization_current_ae B f).symm
  have hf : (bodyCurrentPolarization B f).memLp.toLp (bodyCurrentPolarization B f).current = (f : VectorL2) :=
    Lp.ext ((bodyCurrentPolarization B f).memLp.coeFn_toLp.trans (bodyCurrentPolarization_current_ae B f))
  have ho := compactOutgoingOperator_coe k (bodySupportRadius B) (bodySupportRadius_nonneg B) (bodyCurrentInclusion B f)
  filter_upwards [indicatorL2_coe volume B.domain (bodyDomain_isOpen B).measurableSet
    (compactOutgoingOperator k (bodySupportRadius B) (bodySupportRadius_nonneg B)
      (bodyCurrentInclusion B f) : VectorL2), ho] with x hi hx
  change (indicatorL2 volume B.domain (bodyDomain_isOpen B).measurableSet
    (compactOutgoingOperator k (bodySupportRadius B) (bodySupportRadius_nonneg B)
      (bodyCurrentInclusion B f) : VectorL2)) x = _
  rw [hi]
  by_cases hxd : x ∈ B.domain
  · have hxb : x ∈ Metric.closedBall 0 (bodySupportRadius B) := domain_subset_closedBall B hxd
    rw [indicator_of_mem hxd, indicator_of_mem hxd, hx, indicator_of_mem hxb]
    have hr := remainderPotential_congr_current k _ _ hcur
    rw [hr]
    simp only [electricVolumeField, hf]
    rfl
  · simp [indicator_of_notMem hxd]

end OQ7Prescribed
