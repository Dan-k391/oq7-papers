import PrescribedExtinction.RotationResponse
import PrescribedExtinction.PhysicalExtinctionWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory
local notation "ScalarL2" => Lp ℂ 2 (volume : Measure Position)

def normalizedExtinction (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  k * (inner ℂ (normalizedIncidentDrive k B σ) (normalizedActiveResponse k hk B σ θ α β hα hβ)).im

/-- Exact factorization of the original physical extinction cross section.
The auxiliary response is defined at zero angle, without dividing by sin theta. -/
theorem physicalExtinction_sine_squared_factorization (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    extinction k (rankOneBody B (basisR 0) (rotatedAxis θ) α β) σ
      (volumeTotalElectric k σ (bodyCurrentPolarization B
        (activeInjection B (basisR 0) (rotatedAxis θ)
          (activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ)))) =
      (Real.sin θ) ^ 2 * normalizedExtinction k hk B σ θ α β hα hβ := by
  rw [activePhysicalExtinction_work, activeProjectedIncident_sine_factorization,
    activePhysicalSolution_sine_factorization]
  have hi (r : ℝ) (f g : ScalarBodyCurrentL2 B) :
      (inner ℂ ((r : ℂ) • f) ((r : ℂ) • g)).im = r ^ 2 * (inner ℂ f g).im := by
    change (inner ℂ ((r : ℂ) • (f : ScalarL2)) ((r : ℂ) • (g : ScalarL2))).im =
      r ^ 2 * (inner ℂ (f : ScalarL2) (g : ScalarL2)).im
    rw [inner_smul_left, inner_smul_right]
    change ((star (r : ℂ)) * ((r : ℂ) * inner ℂ f g)).im = _
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [hi]
  unfold normalizedExtinction
  ring

end OQ7Prescribed
