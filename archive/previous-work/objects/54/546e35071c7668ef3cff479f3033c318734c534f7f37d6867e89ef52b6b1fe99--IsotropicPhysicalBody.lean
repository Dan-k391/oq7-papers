import work.PhysicalPerturbedResponse

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def isotropicRankOneBody (B : TwoLayerBody) (ν θ : ℝ) (α β : ℂ) : TwoLayerBody :=
  { B with
    absorberPermittivity := layerPermittivity α.re α.im ν (basisR 0)
    platePermittivity := layerPermittivity β.re β.im ν (rotatedAxis θ) }

theorem complex_re_im_coefficient (α : ℂ) : (α.re : ℂ) + Complex.I * (α.im : ℂ) = α := by
  apply Complex.ext <;> simp

theorem isotropicLayer_susceptibility (α : ℂ) (ν : ℝ) (u : Position) :
    layerPermittivity α.re α.im ν u - 1 = α • rankOne u + (Complex.I * (ν : ℂ)) • (1 : Tensor) := by
  unfold layerPermittivity
  rw [complex_re_im_coefficient, add_smul, one_smul]
  abel

theorem tensorMap_add_apply (A B : Tensor) (w : Vector) : tensorMap (A + B) w = tensorMap A w + tensorMap B w := by
  ext i
  simp [tensorMap_apply, tensorApply, Matrix.add_mulVec, PiLp.add_apply]

theorem tensorMap_one_apply (w : Vector) : tensorMap 1 w = w := by
  rw [tensorMap_apply, tensorApply_one]

theorem tensorMap_isotropicLayer (α : ℂ) (ν : ℝ) (u : Position) (w : Vector) :
    tensorMap (layerPermittivity α.re α.im ν u - 1) w =
      (α * axisCoupling u w) • complexify u + (Complex.I * (ν : ℂ)) • w := by
  rw [isotropicLayer_susceptibility, tensorMap_add_apply, tensorMap_smul_apply,
    tensorMap_smul_apply, tensorMap_one_apply, tensorMap_apply, tensorApply_rankOne, smul_smul]

theorem isotropicSusceptibilityOperator_coe (B : TwoLayerBody) (ν θ : ℝ) (α β : ℂ) (f : BodyCurrentL2 B) :
    (isotropicSusceptibilityOperator B ν θ α β f : VectorL2) =ᵐ[volume] fun x =>
      if x 2 < B.absorberThickness then tensorMap ((isotropicRankOneBody B ν θ α β).absorberPermittivity - 1) ((f : VectorL2) x)
        else tensorMap ((isotropicRankOneBody B ν θ α β).platePermittivity - 1) ((f : VectorL2) x) := by
  let q := activeForwardMaterial B α β (activeProjection B (basisR 0) (rotatedAxis θ) f)
  let j := activeInjection B (basisR 0) (rotatedAxis θ) q
  let a := Complex.I * (ν : ℂ)
  filter_upwards [Lp.coeFn_add (j : VectorL2) (a • (f : VectorL2)), Lp.coeFn_smul a (f : VectorL2),
    activeInjection_coe B (basisR 0) (rotatedAxis θ) q,
    activeForwardMaterial_coe B α β (activeProjection B (basisR 0) (rotatedAxis θ) f),
    activeProjection_coe B (basisR 0) (rotatedAxis θ) f] with x ha hs hj hq hp
  change ((j : VectorL2) + a • (f : VectorL2)) x = _
  rw [ha]
  change (j : VectorL2) x + (a • (f : VectorL2)) x = _
  rw [hs, hj]
  change (q : Lp ℂ 2 (volume : Measure Position)) x = _ at hq
  rw [hq, hp]
  dsimp only [isotropicRankOneBody]
  by_cases hx : x 2 < B.absorberThickness <;> simp only [hx, ite_true, ite_false]
  all_goals rw [tensorMap_isotropicLayer]; rfl

theorem physicalPerturbedCurrent_physicalVolumeEquation (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (ν θ : ℝ) (α β : ℂ) (hL : IsUnit (physicalElectricOperator k B ν θ α β)) :
    MaterialVolumeEquation k (isotropicRankOneBody B ν θ α β) σ
      (bodyCurrentPolarization B (physicalPerturbedCurrent k B σ ν θ α β)) := by
  let q := physicalPerturbedCurrent k B σ ν θ α β
  let e := physicalRestrictedElectric k B σ ν θ α β
  let p := bodyCurrentPolarization B q
  have heq : e = bodyIncidentCurrent k B σ + bodyOutgoingOperator k B q :=
    physicalRestrictedElectric_eq_total k B σ ν θ α β hL
  change p.current =ᵐ[volume] polarization (isotropicRankOneBody B ν θ α β) (volumeTotalElectric k σ p)
  rw [physicalPolarization_indicator]
  filter_upwards [isotropicSusceptibilityOperator_coe B ν θ α β e,
    bodyOutgoingOperator_coe k B q, bodyIncidentCurrent_coe k B σ,
    Lp.coeFn_add (bodyIncidentCurrent k B σ : VectorL2) (bodyOutgoingOperator k B q : VectorL2),
    outgoingElectricField_eq_ae k p] with x hq ht hi ha hout
  have hx := congrArg (fun f : BodyCurrentL2 B => (f : VectorL2) x) heq
  change (e : VectorL2) x = ((bodyIncidentCurrent k B σ : VectorL2) + (bodyOutgoingOperator k B q : VectorL2)) x at hx
  rw [ha] at hx
  change (e : VectorL2) x = (bodyIncidentCurrent k B σ : VectorL2) x + (bodyOutgoingOperator k B q : VectorL2) x at hx
  rw [hi, ht] at hx
  change (q : VectorL2) x = _ at hq
  change B.domain.indicator (fun y => (q : VectorL2) y) x = B.domain.indicator _ x
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd, hq]
    rw [indicator_of_mem hxd, indicator_of_mem hxd] at hx
    rw [hx]
    simp only [volumeTotalElectric, hout]
    rfl
  · rw [indicator_of_notMem hxd, indicator_of_notMem hxd]

end OQ7Prescribed
