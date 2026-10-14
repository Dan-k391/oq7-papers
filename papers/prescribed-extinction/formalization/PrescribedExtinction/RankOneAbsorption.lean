import PrescribedExtinction.PhysicalAbsorptionWork
import PrescribedExtinction.RotationResponse

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
local notation "ScalarL2" => Lp ℂ 2 (volume : Measure Position)

theorem activePhysicalSolution_projected_total (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    activeProjection B u v (bodyIncidentCurrent k B σ + bodyOutgoingOperator k B
      (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ))) =
      activeInverseMaterial B α β (activePhysicalSolution k hk B σ u v α β hα hβ) := by
  let q := activePhysicalSolution k hk B σ u v α β hα hβ
  have heq : activeProjection B u v (bodyOutgoingOperator k B (activeInjection B u v q)) -
      activeInverseMaterial B α β q = -activeProjection B u v (bodyIncidentCurrent k B σ) :=
    activePhysicalSolution_equation k hk B σ u v α β hα hβ
  rw [map_add]
  rw [(sub_eq_iff_eq_add).mp heq, add_neg_cancel_left]

theorem activePhysicalAbsorption_work (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (u v : Position) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    absorption k (rankOneBody B u v α β)
      (volumeTotalElectric k σ (bodyCurrentPolarization B
        (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ)))) =
      k * -(inner ℂ (activePhysicalSolution k hk B σ u v α β hα hβ)
        (activeInverseMaterial B α β (activePhysicalSolution k hk B σ u v α β hα hβ))).im := by
  have ha := volumeAbsorption_body_inner k _ σ _
    (activePhysicalSolution_physicalVolumeEquation k hk B σ u v α β hα hβ)
  change absorption k (rankOneBody B u v α β)
      (volumeTotalElectric k σ (bodyCurrentPolarization B
        (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ)))) =
      k * (inner ℂ (bodyIncidentCurrent k B σ + bodyOutgoingOperator k B
    (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ)))
      (activeInjection B u v (activePhysicalSolution k hk B σ u v α β hα hβ))).im at ha
  rw [ha]
  rw [activeProjection_inner, activePhysicalSolution_projected_total]
  congr 1
  exact inner_im_symm (𝕜 := ℂ) _ _

def activeLossWeight (B : TwoLayerBody) (α β : ℂ) (x : Position) : ℝ :=
  if x 2 < B.absorberThickness then activeScalarLoss α else activeScalarLoss β

theorem activeInverseMaterial_loss_integral (B : TwoLayerBody) (α β : ℂ) (q : ScalarBodyCurrentL2 B) :
    -(inner ℂ q (activeInverseMaterial B α β q)).im =
      ∫ x : Position, activeLossWeight B α β x * ‖(q : ScalarL2) x‖ ^ 2 := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (q : ScalarL2) (activeInverseMaterial B α β q : ScalarL2)
  have him : (inner ℂ q (activeInverseMaterial B α β q)).im =
      ∫ x : Position, (inner ℂ ((q : ScalarL2) x) ((activeInverseMaterial B α β q : ScalarL2) x)).im := by
    change (inner ℂ (q : ScalarL2) (activeInverseMaterial B α β q : ScalarL2)).im = _
    rw [L2.inner_def]
    exact (Complex.imCLM.integral_comp_comm hi).symm
  rw [him, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [activeInverseMaterial_coe B α β q] with x hx
  rw [hx]
  unfold activeLossWeight
  by_cases hxa : x 2 < B.absorberThickness <;> simp only [hxa, ite_true, ite_false]
  · exact scalarInverse_negative_imaginary α _
  · exact scalarInverse_negative_imaginary β _

def normalizedAbsorption (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  k * -(inner ℂ (normalizedActiveResponse k hk B σ θ α β hα hβ)
    (activeInverseMaterial B α β (normalizedActiveResponse k hk B σ θ α β hα hβ))).im

/-- Exact factorization of the original local physical dielectric absorption. -/
theorem physicalAbsorption_sine_squared_factorization (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    absorption k (rankOneBody B (basisR 0) (rotatedAxis θ) α β)
      (volumeTotalElectric k σ (bodyCurrentPolarization B
        (activeInjection B (basisR 0) (rotatedAxis θ)
          (activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ)))) =
      (Real.sin θ) ^ 2 * normalizedAbsorption k hk B σ θ α β hα hβ := by
  rw [activePhysicalAbsorption_work, activePhysicalSolution_sine_factorization, map_smul]
  have hi (r : ℝ) (f g : ScalarBodyCurrentL2 B) :
      (inner ℂ ((r : ℂ) • f) ((r : ℂ) • g)).im = r ^ 2 * (inner ℂ f g).im := by
    change (inner ℂ ((r : ℂ) • (f : ScalarL2)) ((r : ℂ) • (g : ScalarL2))).im =
      r ^ 2 * (inner ℂ (f : ScalarL2) (g : ScalarL2)).im
    rw [inner_smul_left, inner_smul_right]
    change ((star (r : ℂ)) * ((r : ℂ) * inner ℂ f g)).im = _
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [hi]
  unfold normalizedAbsorption
  ring

end OQ7Prescribed
