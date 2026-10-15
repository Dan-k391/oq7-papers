import QuarticMaxwell.SupportBlocks
import QuarticMaxwell.StaticCrossIdentification

/-! The genuine static inverse for a piecewise scalar susceptibility on two
separated supports, and its exact isolated-block interaction equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell.TwoSupportStatic
open OQ7Prescribed SphereResponse SupportBlocks StaticCrossIdentification MeasureTheory Set

theorem indicatorL2_nested_subset (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hsub : D ⊆ E) (f : VectorL2) :
    indicatorL2 volume D hD (indicatorL2 volume E hE f) = indicatorL2 volume D hD f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe volume D hD (indicatorL2 volume E hE f),
    indicatorL2_coe volume E hE f, indicatorL2_coe volume D hD f] with x ho hi hr
  rw [ho, hr]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx, hi, indicator_of_mem (hsub hx)]
  · simp only [indicator_of_notMem hx]

structure ScalarPair where
  left : ℂ
  right : ℂ
  left_loss : 0 < left.im
  right_loss : 0 < right.im

def ScalarPair.cap (P : ScalarPair) : ℝ := max ‖P.left‖ ‖P.right‖
def ScalarPair.loss (P : ScalarPair) : ℝ := min P.left.im P.right.im

theorem ScalarPair.cap_pos (P : ScalarPair) : 0 < P.cap :=
  lt_of_lt_of_le (scalar_norm_pos P.left_loss) (le_max_left _ _)

theorem ScalarPair.loss_pos (P : ScalarPair) : 0 < P.loss :=
  lt_min P.left_loss P.right_loss

def susceptibility (D : Set OQ7Prescribed.Position) (P : ScalarPair) :
    OQ7Prescribed.Position → Vector →L[ℂ] Vector := by
  classical
  exact D.piecewise (scalarSusceptibility P.left) (scalarSusceptibility P.right)

theorem susceptibility_measurable (D : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (P : ScalarPair) :
    AEStronglyMeasurable (susceptibility D P) volume := by
  classical
  unfold susceptibility scalarSusceptibility
  exact (measurable_const.piecewise hD measurable_const).aestronglyMeasurable

theorem susceptibility_cap (D E : Set OQ7Prescribed.Position) (P : ScalarPair) :
    ∀ᵐ x ∂volume, x ∈ D ∪ E → ‖susceptibility D P x‖ ≤ P.cap := by
  classical
  filter_upwards [scalar_cap P.left (D ∪ E), scalar_cap P.right (D ∪ E)] with x hl hr hx
  by_cases hm : x ∈ D
  · have he : ‖susceptibility D P x‖ ≤ ‖P.left‖ := by
      simpa [susceptibility, Set.piecewise, hm] using hl hx
    exact he.trans (le_max_left _ _)
  · have he : ‖susceptibility D P x‖ ≤ ‖P.right‖ := by
      simpa [susceptibility, Set.piecewise, hm] using hr hx
    exact he.trans (le_max_right _ _)

theorem susceptibility_loss (D E : Set OQ7Prescribed.Position) (P : ScalarPair) :
    ∀ᵐ x ∂volume, x ∈ D ∪ E → ∀ v : Vector,
      P.loss * ‖v‖ ^ 2 ≤ (inner ℂ v (susceptibility D P x v)).im := by
  classical
  filter_upwards [scalar_loss P.left (D ∪ E), scalar_loss P.right (D ∪ E)] with x hl hr hx v
  by_cases hm : x ∈ D
  · apply (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖v‖)).trans
    simpa [susceptibility, Set.piecewise, hm] using hl hx v
  · apply (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg ‖v‖)).trans
    simpa [susceptibility, Set.piecewise, hm] using hr hx v

def equiv (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (P : ScalarPair) : DomainL2 (D ∪ E) ≃L[ℂ] DomainL2 (D ∪ E) :=
  StaticInverse.equiv (D ∪ E) (hD.union hE) (susceptibility D P) (susceptibility_measurable D hD P)
    P.cap (susceptibility_cap D E P) P.loss_pos (susceptibility_loss D E P) P.cap_pos

def isolatedEquiv (D : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (χ : ℂ) (hχ : 0 < χ.im) :
    DomainL2 D ≃L[ℂ] DomainL2 D :=
  StaticInverse.equiv D hD (scalarSusceptibility χ) (scalar_measurable χ) ‖χ‖
    (scalar_cap χ D) hχ (scalar_loss χ D) (scalar_norm_pos hχ)

def inverseMaterial (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (P : ScalarPair) : DomainL2 (D ∪ E) →L[ℂ] DomainL2 (D ∪ E) :=
  VolumeInverse.inverseSusceptibility (D ∪ E) (hD.union hE) (susceptibility D P)
    (susceptibility_measurable D hD P) P.cap (susceptibility_cap D E P)
    P.loss_pos (susceptibility_loss D E P)

theorem inverseMaterial_left (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (P : ScalarPair) (p : DomainL2 (D ∪ E)) :
    projectLeft D E hD (inverseMaterial D E hD hE P p) = P.left⁻¹ • projectLeft D E hD p := by
  classical
  let q := inverseMaterial D E hD hE P p
  have hc := TensorMultiplier.inverse_constitutive volume (D ∪ E) (susceptibility D P)
    (susceptibility_measurable D hD P) P.cap (susceptibility_cap D E P) (hD.union hE)
    P.loss_pos (susceptibility_loss D E P) p
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [restriction_coe D (D ∪ E) hD q, restriction_coe D (D ∪ E) hD p,
    Lp.coeFn_smul P.left⁻¹ (projectLeft D E hD p : VectorL2), hc] with x hq hp hs hm
  change (restriction D (D ∪ E) hD q : VectorL2) x =
    (P.left⁻¹ • (projectLeft D E hD p : VectorL2)) x
  rw [hs]
  change _ = P.left⁻¹ • (projectLeft D E hD p : VectorL2) x
  change _ = P.left⁻¹ • (restriction D (D ∪ E) hD p : VectorL2) x
  rw [hq, hp]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx]
    change susceptibility D P x ((q : VectorL2) x) = (p : VectorL2) x at hm
    have he : P.left • (q : VectorL2) x = (p : VectorL2) x := by
      simpa [susceptibility, Set.piecewise, hx, scalarSusceptibility] using hm
    calc
      _ = P.left⁻¹ • (P.left • (q : VectorL2) x) := by
        rw [smul_smul, inv_mul_cancel₀ (scalar_nonzero P.left_loss), one_smul]
      _ = _ := congrArg (fun v => P.left⁻¹ • v) he
  · simp only [indicator_of_notMem hx, smul_zero]

theorem inverseMaterial_right (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hdis : Disjoint D E) (P : ScalarPair) (p : DomainL2 (D ∪ E)) :
    projectRight D E hE (inverseMaterial D E hD hE P p) = P.right⁻¹ • projectRight D E hE p := by
  classical
  let q := inverseMaterial D E hD hE P p
  have hc := TensorMultiplier.inverse_constitutive volume (D ∪ E) (susceptibility D P)
    (susceptibility_measurable D hD P) P.cap (susceptibility_cap D E P) (hD.union hE)
    P.loss_pos (susceptibility_loss D E P) p
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [restriction_coe E (D ∪ E) hE q, restriction_coe E (D ∪ E) hE p,
    Lp.coeFn_smul P.right⁻¹ (projectRight D E hE p : VectorL2), hc] with x hq hp hs hm
  change (restriction E (D ∪ E) hE q : VectorL2) x =
    (P.right⁻¹ • (projectRight D E hE p : VectorL2)) x
  rw [hs]
  change _ = P.right⁻¹ • (restriction E (D ∪ E) hE p : VectorL2) x
  rw [hq, hp]
  by_cases hx : x ∈ E
  · have hxD : x ∉ D := fun hxd => Set.disjoint_left.mp hdis hxd hx
    simp only [indicator_of_mem hx]
    change susceptibility D P x ((q : VectorL2) x) = (p : VectorL2) x at hm
    have he : P.right • (q : VectorL2) x = (p : VectorL2) x := by
      simpa [susceptibility, Set.piecewise, hxD, scalarSusceptibility] using hm
    calc
      _ = P.right⁻¹ • (P.right • (q : VectorL2) x) := by
        rw [smul_smul, inv_mul_cancel₀ (scalar_nonzero P.right_loss), one_smul]
      _ = _ := congrArg (fun v => P.right⁻¹ • v) he
  · simp only [indicator_of_notMem hx, smul_zero]

end QuarticMaxwell.TwoSupportStatic

namespace QuarticMaxwell.TwoSupportStatic
open OQ7Prescribed SphereResponse SupportBlocks StaticCrossIdentification MeasureTheory Set

theorem staticCrossBlock_self (D : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (f : DomainL2 D) :
    staticCrossBlock D D hD f = domainStaticOperator D hD f := by
  apply Subtype.ext
  rw [domainStaticOperator_coe]
  change indicatorL2 volume D hD (staticFourierOperator (f : VectorL2)) =
    supportRestrictionCLM D hD (staticFourierOperator (supportRestrictionCLM D hD (f : VectorL2)))
  rw [supportRestrictionCLM_eq_self]
  rfl

theorem staticCrossBlock_union_split (U D E : Set OQ7Prescribed.Position)
    (hU : MeasurableSet U) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hdis : Disjoint D E) (p : DomainL2 (D ∪ E)) :
    staticCrossBlock U (D ∪ E) hU p = staticCrossBlock U D hU (projectLeft D E hD p) +
      staticCrossBlock U E hU (projectRight D E hE p) := by
  conv_lhs => rw [← support_decomposition D E hD hE hdis p]
  rw [map_add]
  rfl

theorem projectLeft_domainStatic (D E : Set OQ7Prescribed.Position)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (p : DomainL2 (D ∪ E)) :
    projectLeft D E hD (domainStaticOperator (D ∪ E) (hD.union hE) p) =
      staticCrossBlock D (D ∪ E) hD p := by
  apply Subtype.ext
  change indicatorL2 volume D hD (domainStaticOperator (D ∪ E) (hD.union hE) p : VectorL2) = _
  rw [domainStaticOperator_coe]
  change indicatorL2 volume D hD (indicatorL2 volume (D ∪ E) (hD.union hE)
      (staticFourierOperator (supportRestrictionCLM (D ∪ E) (hD.union hE) (p : VectorL2)))) =
    indicatorL2 volume D hD (staticFourierOperator (p : VectorL2))
  rw [supportRestrictionCLM_eq_self]
  exact indicatorL2_nested_subset D (D ∪ E) hD (hD.union hE) subset_union_left _

theorem projectRight_domainStatic (D E : Set OQ7Prescribed.Position)
    (hD : MeasurableSet D) (hE : MeasurableSet E) (p : DomainL2 (D ∪ E)) :
    projectRight D E hE (domainStaticOperator (D ∪ E) (hD.union hE) p) =
      staticCrossBlock E (D ∪ E) hE p := by
  apply Subtype.ext
  change indicatorL2 volume E hE (domainStaticOperator (D ∪ E) (hD.union hE) p : VectorL2) = _
  rw [domainStaticOperator_coe]
  change indicatorL2 volume E hE (indicatorL2 volume (D ∪ E) (hD.union hE)
      (staticFourierOperator (supportRestrictionCLM (D ∪ E) (hD.union hE) (p : VectorL2)))) =
    indicatorL2 volume E hE (staticFourierOperator (p : VectorL2))
  rw [supportRestrictionCLM_eq_self]
  exact indicatorL2_nested_subset E (D ∪ E) hE (hD.union hE) subset_union_right _

theorem isolatedEquiv_apply (D : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (χ : ℂ) (hχ : 0 < χ.im) (p : DomainL2 D) :
    isolatedEquiv D hD χ hχ p = χ⁻¹ • p - domainStaticOperator D hD p := by
  rw [isolatedEquiv, StaticInverse.equiv_apply]
  change VolumeInverse.inverseSusceptibility _ _ _ _ _ _ _ _ _ - domainStaticOperator _ _ _ = _
  rw [scalar_inverse]

theorem equiv_apply (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (P : ScalarPair) (p : DomainL2 (D ∪ E)) :
    equiv D E hD hE P p = inverseMaterial D E hD hE P p - domainStaticOperator (D ∪ E) (hD.union hE) p := by
  rw [equiv, StaticInverse.equiv_apply]
  rfl

theorem left_block_equation (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hdis : Disjoint D E) (P : ScalarPair) (p : DomainL2 (D ∪ E)) :
    projectLeft D E hD (equiv D E hD hE P p) =
      isolatedEquiv D hD P.left P.left_loss (projectLeft D E hD p) -
        staticCrossBlock D E hD (projectRight D E hE p) := by
  rw [equiv_apply, map_sub, inverseMaterial_left, projectLeft_domainStatic,
    staticCrossBlock_union_split D D E hD hD hE hdis, staticCrossBlock_self,
    isolatedEquiv_apply]
  · abel
  · exact hE

theorem right_block_equation (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hdis : Disjoint D E) (P : ScalarPair) (p : DomainL2 (D ∪ E)) :
    projectRight D E hE (equiv D E hD hE P p) =
      isolatedEquiv E hE P.right P.right_loss (projectRight D E hE p) -
        staticCrossBlock E D hE (projectLeft D E hD p) := by
  rw [equiv_apply, map_sub, inverseMaterial_right D E hD hE hdis, projectRight_domainStatic,
    staticCrossBlock_union_split E D E hE hD hE hdis, staticCrossBlock_self,
    isolatedEquiv_apply]
  · abel
  · exact hD

def blockInverse (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (P : ScalarPair) : DomainL2 (D ∪ E) →L[ℂ] DomainL2 (D ∪ E) :=
  diagonal D E hD hE (isolatedEquiv D hD P.left P.left_loss).symm.toContinuousLinearMap
    (isolatedEquiv E hE P.right P.right_loss).symm.toContinuousLinearMap

def interaction (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D) (hE : MeasurableSet E) :
    DomainL2 (D ∪ E) →L[ℂ] DomainL2 (D ∪ E) :=
  offDiagonal D E hD hE (staticCrossBlock D E hD) (staticCrossBlock E D hE)

theorem assembled_equation (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hdis : Disjoint D E) (P : ScalarPair) (p : DomainL2 (D ∪ E)) :
    equiv D E hD hE P p + interaction D E hD hE p =
      diagonal D E hD hE (isolatedEquiv D hD P.left P.left_loss).toContinuousLinearMap
        (isolatedEquiv E hE P.right P.right_loss).toContinuousLinearMap p := by
  apply component_ext D E hD hE hdis
  · rw [map_add, left_block_equation D E hD hE hdis, interaction,
      projectLeft_offDiagonal D E hD hE hdis, projectLeft_diagonal D E hD hE hdis]
    change _ = isolatedEquiv D hD P.left P.left_loss (projectLeft D E hD p)
    abel
  · rw [map_add, right_block_equation D E hD hE hdis, interaction,
      projectRight_offDiagonal D E hD hE hdis, projectRight_diagonal D E hD hE hdis]
    change _ = isolatedEquiv E hE P.right P.right_loss (projectRight D E hE p)
    abel

theorem inverse_interaction_identity (D E : Set OQ7Prescribed.Position) (hD : MeasurableSet D)
    (hE : MeasurableSet E) (hdis : Disjoint D E) (P : ScalarPair) (f : DomainL2 (D ∪ E)) :
    (equiv D E hD hE P).symm f = blockInverse D E hD hE P f +
      blockInverse D E hD hE P (interaction D E hD hE ((equiv D E hD hE P).symm f)) := by
  have h := assembled_equation D E hD hE hdis P ((equiv D E hD hE P).symm f)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  have he := congrArg (blockInverse D E hD hE P) h
  rw [map_add] at he
  have hc := diagonal_inverse_cancel D E hD hE hdis
    (isolatedEquiv D hD P.left P.left_loss) (isolatedEquiv E hE P.right P.right_loss)
    ((equiv D E hD hE P).symm f)
  exact (he.trans hc).symm

end QuarticMaxwell.TwoSupportStatic
