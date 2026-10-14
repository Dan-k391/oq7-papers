import PrescribedExtinction.SupportedL2Maps
import PrescribedExtinction.ScatteringExistence

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical

abbrev ScalarBodyCurrentL2 (B : TwoLayerBody) := SetSupportedL2 (E := ℂ) volume B.domain

instance scalarBodyCurrentL2_completeSpace (B : TwoLayerBody) : CompleteSpace (ScalarBodyCurrentL2 B) := by
  let : IsClosed (setSupportedL2 (E := ℂ) volume B.domain : Set (Lp ℂ 2 volume)) :=
    by exact setSupportedL2_isClosed (E := ℂ) (volume : Measure Position) B.domain (bodyDomain_isOpen B).measurableSet
  exact inferInstance

def axisEmbedding (u : Position) : ℂ →L[ℂ] Vector :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (complexify u)

theorem axisEmbedding_apply (u : Position) (z : ℂ) : axisEmbedding u z = z • complexify u := rfl

theorem axisEmbedding_adjoint_apply (u : Position) (v : Vector) :
    (axisEmbedding u).adjoint v = axisCoupling u v := by
  have hh := (axisEmbedding u).adjoint_inner_right (1 : ℂ) v
  simpa [axisEmbedding, axisCoupling_eq_inner, RCLike.inner_apply] using hh

theorem axisEmbedding_adjoint_embedding (u : Position) (hu : ‖u‖ ^ 2 = 1) (z : ℂ) :
    (axisEmbedding u).adjoint (axisEmbedding u z) = z := by
  rw [axisEmbedding_adjoint_apply, axisCoupling_eq_inner, axisEmbedding_apply, inner_smul_right]
  have hh : inner ℂ (complexify u) (complexify u) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hn : ‖complexify u‖ = 1 := by nlinarith [complexify_norm_sq u, norm_nonneg (complexify u)]
    rw [hn]
    norm_num
  rw [hh, mul_one]

def activeInjection (B : TwoLayerBody) (u v : Position) :
    ScalarBodyCurrentL2 B →L[ℂ] BodyCurrentL2 B :=
  twoPieceSupportedMap volume B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
    (axisEmbedding u) (axisEmbedding v)

def activeProjection (B : TwoLayerBody) (u v : Position) :
    BodyCurrentL2 B →L[ℂ] ScalarBodyCurrentL2 B :=
  twoPieceSupportedMap volume B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
    (axisEmbedding u).adjoint (axisEmbedding v).adjoint

theorem activeInjection_coe (B : TwoLayerBody) (u v : Position) (q : ScalarBodyCurrentL2 B) :
    (activeInjection B u v q : VectorL2) =ᵐ[volume] fun x =>
      if x 2 < B.absorberThickness then (q : Lp ℂ 2 volume) x • complexify u
        else (q : Lp ℂ 2 volume) x • complexify v :=
  twoPieceSupportedMap_coe _ _ _ _ _ _ _

theorem activeProjection_coe (B : TwoLayerBody) (u v : Position) (p : BodyCurrentL2 B) :
    (activeProjection B u v p : Lp ℂ 2 volume) =ᵐ[volume] fun x =>
      if x 2 < B.absorberThickness then axisCoupling u ((p : VectorL2) x)
        else axisCoupling v ((p : VectorL2) x) := by
  filter_upwards [twoPieceSupportedMap_coe volume B.domain (bodyAbsorberSlice B)
    (bodyAbsorberSlice_measurable B) (axisEmbedding u).adjoint (axisEmbedding v).adjoint p] with x hx
  simpa only [axisEmbedding_adjoint_apply, bodyAbsorberSlice, mem_setOf_eq, activeProjection] using hx

theorem activeInjection_inner (B : TwoLayerBody) (u v : Position)
    (q : ScalarBodyCurrentL2 B) (p : BodyCurrentL2 B) :
    inner ℂ (activeInjection B u v q) p = inner ℂ q (activeProjection B u v p) :=
  twoPieceSupportedMap_adjoint_inner _ _ _ _ _ _ _ _

theorem activeProjection_injection (B : TwoLayerBody) (u v : Position)
    (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1) (q : ScalarBodyCurrentL2 B) :
    activeProjection B u v (activeInjection B u v q) = q := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [activeInjection_coe B u v q,
    activeProjection_coe B u v (activeInjection B u v q)] with x hJ hP
  rw [hP, hJ]
  by_cases hx : x 2 < B.absorberThickness <;> simp only [hx, ite_true, ite_false]
  · simpa only [axisEmbedding_adjoint_apply, axisEmbedding_apply] using axisEmbedding_adjoint_embedding u hu ((q : Lp ℂ 2 volume) x)
  · simpa only [axisEmbedding_adjoint_apply, axisEmbedding_apply] using axisEmbedding_adjoint_embedding v hv ((q : Lp ℂ 2 volume) x)

theorem activeInjection_norm (B : TwoLayerBody) (u v : Position)
    (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1) (q : ScalarBodyCurrentL2 B) :
    ‖activeInjection B u v q‖ = ‖q‖ := by
  have hh := congrArg Complex.re (activeInjection_inner B u v q (activeInjection B u v q))
  rw [activeProjection_injection B u v hu hv] at hh
  have hj : (inner ℂ (activeInjection B u v q) (activeInjection B u v q)).re =
      ‖activeInjection B u v q‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hq : (inner ℂ q q).re = ‖q‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hj, hq] at hh
  nlinarith [norm_nonneg (activeInjection B u v q), norm_nonneg q]

theorem activeProjectedOutgoing_im_nonneg (k : ℝ) (hk : 0 < k) (B : TwoLayerBody)
    (u v : Position) (q : ScalarBodyCurrentL2 B) :
    0 ≤ (inner ℂ q (activeProjection B u v (bodyOutgoingOperator k B (activeInjection B u v q)))).im := by
  rw [← activeInjection_inner]
  exact bodyOutgoingOperator_im_nonneg k hk B _

end OQ7Prescribed
