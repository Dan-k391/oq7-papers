import PrescribedExtinction.ScatteringExistence

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical

theorem materialVolumeCurrent_supported (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p) :
    ∀ᵐ x ∂volume, x ∉ B.domain → p.current x = 0 := by
  filter_upwards [hp] with x hx
  intro hxd
  rw [hx, physicalPolarization_indicator, indicator_of_notMem hxd]

def materialVolumeCurrent (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p) : BodyCurrentL2 B :=
  ⟨p.memLp.toLp p.current, by
    change ∀ᵐ x ∂volume, x ∉ B.domain → (p.memLp.toLp p.current) x = 0
    filter_upwards [p.memLp.coeFn_toLp, materialVolumeCurrent_supported k B σ p hp] with x hx hs
    intro hxd
    rw [hx, hs hxd]⟩

theorem materialVolumeCurrent_coe (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p) :
    (materialVolumeCurrent k B σ p hp : VectorL2) =ᵐ[volume] p.current := p.memLp.coeFn_toLp

theorem materialVolumeCurrent_operator_equation (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) :
    materialBodyOperator k B a b (materialVolumeCurrent k B σ p hp) = -bodyIncidentCurrent k B σ := by
  let f := materialVolumeCurrent k B σ p hp
  let q := bodyCurrentPolarization B f
  have hqp : q.current =ᵐ[volume] p.current :=
    (bodyCurrentPolarization_current_ae B f).trans (materialVolumeCurrent_coe k B σ p hp)
  have he := electricVolumeField_congr_current k q p hqp
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [bodyOutgoingOperator_coe k B f, bodyInverseSusceptibility_coe B a b f,
    bodyIncidentCurrent_coe k B σ, materialVolumeCurrent_coe k B σ p hp,
    Lp.coeFn_sub (bodyOutgoingOperator k B f : VectorL2) (bodyInverseSusceptibility B a b f : VectorL2),
    Lp.coeFn_neg (bodyIncidentCurrent k B σ : VectorL2), hp, outgoingElectricField_eq_ae k p,
    f.property] with x hT hJ hI hf hsub hneg hx hout hs
  change ((bodyOutgoingOperator k B f : VectorL2) - (bodyInverseSusceptibility B a b f : VectorL2)) x =
    (-(bodyIncidentCurrent k B σ : VectorL2)) x
  rw [hsub, hneg]
  change (bodyOutgoingOperator k B f : VectorL2) x - (bodyInverseSusceptibility B a b f : VectorL2) x =
    -(bodyIncidentCurrent k B σ : VectorL2) x
  rw [hT, hJ, hI]
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd, he]
    rw [physicalPolarization_indicator, indicator_of_mem hxd] at hx
    change p.current x = if x 2 < B.absorberThickness then
      tensorMap (B.absorberPermittivity - 1) (incidentElectric k σ x + outgoingElectricField k p x)
      else tensorMap (B.platePermittivity - 1) (incidentElectric k σ x + outgoingElectricField k p x) at hx
    rw [hout] at hx
    by_cases hxa : x 2 < B.absorberThickness
    · simp only [hxa, ite_true] at hx ⊢
      have hforward : (f : VectorL2) x = a.inverse (incidentElectric k σ x + electricVolumeField k p x) := by
        rw [a.forward_eq, hf]
        exact hx
      rw [hforward, ContinuousLinearEquiv.symm_apply_apply]
      abel
    · simp only [hxa, ite_false] at hx ⊢
      have hforward : (f : VectorL2) x = b.inverse (incidentElectric k σ x + electricVolumeField k p x) := by
        rw [b.forward_eq, hf]
        exact hx
      rw [hforward, ContinuousLinearEquiv.symm_apply_apply]
      abel
  · rw [indicator_of_notMem hxd, indicator_of_notMem hxd, hs hxd]
    simp

theorem materialVolumeCurrent_eq_solution (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hp : MaterialVolumeEquation k B σ p)
    (a : SusceptibilityInverseData B.absorberPermittivity)
    (b : SusceptibilityInverseData B.platePermittivity) :
    materialVolumeCurrent k B σ p hp = materialBodySolution k hk B σ a b := by
  apply (materialBodyEquiv k hk B a b).injective
  rw [materialBodyEquiv_apply, materialBodyEquiv_apply, materialBodySolution_equation]
  exact materialVolumeCurrent_operator_equation k B σ p hp a b

/-- Uniqueness of the actual compact L² polarization among material-volume solutions. -/
theorem materialVolumeEquation_unique_current (k : ℝ) (hk : 0 < k) (P Q : ℝ) (B : TwoLayerBody)
    (hB : B.admissible P Q) (σ : Direction) (p q : CompactPolarization)
    (hp : MaterialVolumeEquation k B σ p) (hq : MaterialVolumeEquation k B σ q) :
    p.current =ᵐ[volume] q.current := by
  let a := admissibleSusceptibilityInverseData P Q B.absorberPermittivity hB.1
  let b := admissibleSusceptibilityInverseData P Q B.platePermittivity hB.2
  have hf : materialVolumeCurrent k B σ p hp = materialVolumeCurrent k B σ q hq := by
    rw [materialVolumeCurrent_eq_solution k hk B σ p hp a b,
      materialVolumeCurrent_eq_solution k hk B σ q hq a b]
  have hae : (materialVolumeCurrent k B σ p hp : VectorL2) =ᵐ[volume]
      (materialVolumeCurrent k B σ q hq : VectorL2) := by rw [hf]
  exact (materialVolumeCurrent_coe k B σ p hp).symm.trans
    (hae.trans (materialVolumeCurrent_coe k B σ q hq))

end OQ7Prescribed
