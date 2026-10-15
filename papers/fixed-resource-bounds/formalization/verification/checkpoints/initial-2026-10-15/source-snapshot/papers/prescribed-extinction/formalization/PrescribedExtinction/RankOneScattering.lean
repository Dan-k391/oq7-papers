import PrescribedExtinction.ActiveMaterialInverse

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical
local notation "ScalarL2" => Lp ℂ 2 (volume : Measure Position)

def rankOneBody (B : TwoLayerBody) (u v : Position) (α β : ℂ) : TwoLayerBody :=
  { B with
    absorberPermittivity := 1 + α • rankOne u
    platePermittivity := 1 + β • rankOne v }

theorem tensorMap_smul_apply (z : ℂ) (T : Tensor) (w : Vector) :
    tensorMap (z • T) w = z • tensorMap T w := by
  ext i
  simp [tensorMap_apply, tensorApply, Matrix.smul_mulVec, PiLp.smul_apply]

theorem rankOneBody_polarization (B : TwoLayerBody) (u v : Position) (α β : ℂ) (E : Field) :
    polarization (rankOneBody B u v α β) E = B.domain.indicator (fun x =>
      if x 2 < B.absorberThickness then (α * axisCoupling u (E x)) • complexify u
        else (β * axisCoupling v (E x)) • complexify v) := by
  rw [physicalPolarization_indicator]
  funext x
  simp only [rankOneBody, TwoLayerBody.domain]
  congr 1
  funext y
  by_cases hy : y 2 < B.absorberThickness <;>
    simp only [hy, ite_true, ite_false, add_sub_cancel_left]
  all_goals rw [tensorMap_smul_apply, tensorMap_apply, tensorApply_rankOne, smul_smul]

theorem activeInverseMaterial_coe (B : TwoLayerBody) (α β : ℂ) (q : ScalarBodyCurrentL2 B) :
    (activeInverseMaterial B α β q : ScalarL2) =ᵐ[volume] fun x : Position =>
      if x 2 < B.absorberThickness then α⁻¹ * (q : ScalarL2) x
        else β⁻¹ * (q : ScalarL2) x :=
  twoPieceSupportedOperator_coe _ _ _ _ _ _ _

def activePhysicalSolution (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ScalarBodyCurrentL2 B :=
  (activeMaterialEquiv k hk B u v α β hα hβ).symm
    (-activeProjection B u v (bodyIncidentCurrent k B σ))

theorem activePhysicalSolution_equation (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    activeMaterialOperator k B u v α β (activePhysicalSolution k hk B σ u v α β hα hβ) =
      -activeProjection B u v (bodyIncidentCurrent k B σ) := by
  rw [← activeMaterialEquiv_apply k hk B u v α β hα hβ]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

theorem activePhysicalSolution_physicalVolumeEquation (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    MaterialVolumeEquation k (rankOneBody B u v α β) σ
      (bodyCurrentPolarization B (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ))) := by
  let q := activePhysicalSolution k hk B σ u v α β hα hβ
  let f := activeInjection B u v q
  let p := bodyCurrentPolarization B f
  let Tq := activeProjection B u v (bodyOutgoingOperator k B f)
  let Iq := activeProjection B u v (bodyIncidentCurrent k B σ)
  have heq : (Tq : ScalarL2) - (activeInverseMaterial B α β q : ScalarL2) = -(Iq : ScalarL2) :=
    congrArg (fun g : ScalarBodyCurrentL2 B => (g : ScalarL2))
      (activePhysicalSolution_equation k hk B σ u v α β hα hβ)
  have hαne : α ≠ 0 := by intro hz; simpa [hz] using hα
  have hβne : β ≠ 0 := by intro hz; simpa [hz] using hβ
  change p.current =ᵐ[volume] polarization (rankOneBody B u v α β) (volumeTotalElectric k σ p)
  rw [rankOneBody_polarization]
  filter_upwards [activeInjection_coe B u v q, bodyOutgoingOperator_coe k B f,
    activeProjection_coe B u v (bodyOutgoingOperator k B f), activeProjection_coe B u v (bodyIncidentCurrent k B σ),
    bodyIncidentCurrent_coe k B σ, activeInverseMaterial_coe B α β q,
    Lp.coeFn_sub (Tq : ScalarL2) (activeInverseMaterial B α β q : ScalarL2),
    Lp.coeFn_neg (Iq : ScalarL2), outgoingElectricField_eq_ae k p] with x hJ hT hP hI hInc hInv hsub hneg hout
  have hx := congrArg (fun g : ScalarL2 => g x) heq
  rw [hsub, hneg] at hx
  change (Tq : ScalarL2) x - (activeInverseMaterial B α β q : ScalarL2) x = -(Iq : ScalarL2) x at hx
  rw [hP, hI, hInv, hT, hInc] at hx
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd] at hx
    change B.domain.indicator (fun y => (f : VectorL2) y) x = _
    rw [indicator_of_mem hxd, indicator_of_mem hxd, hJ]
    change (if x 2 < B.absorberThickness then (q : ScalarL2) x • complexify u else
      (q : ScalarL2) x • complexify v) =
      if x 2 < B.absorberThickness then
        (α * axisCoupling u (incidentElectric k σ x + outgoingElectricField k p x)) • complexify u
      else (β * axisCoupling v (incidentElectric k σ x + outgoingElectricField k p x)) • complexify v
    rw [hout]
    by_cases hxa : x 2 < B.absorberThickness
    · simp only [hxa, ite_true] at hx ⊢
      have hid : (q : ScalarL2) x = α * (axisCoupling u (incidentElectric k σ x) +
          axisCoupling u (electricVolumeField k p x)) := by
        field_simp at hx
        linear_combination -hx
      rw [hid]
      congr 1
      simp [axisCoupling, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [hxa, ite_false] at hx ⊢
      have hid : (q : ScalarL2) x = β * (axisCoupling v (incidentElectric k σ x) +
          axisCoupling v (electricVolumeField k p x)) := by
        field_simp at hx
        linear_combination -hx
      rw [hid]
      congr 1
      simp [axisCoupling, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  · change B.domain.indicator (fun y => (f : VectorL2) y) x = _
    rw [indicator_of_notMem hxd, indicator_of_notMem hxd]

theorem rankOnePhysicalScatteringState_exists (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Nonempty (ScatteringState k (rankOneBody B u v α β) σ) := by
  exact ⟨scatteringStateOfVolumeEquation k _ σ _
    (activePhysicalSolution_physicalVolumeEquation k hk B σ u v α β hα hβ)⟩

end OQ7Prescribed
