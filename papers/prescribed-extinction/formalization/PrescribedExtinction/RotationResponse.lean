import PrescribedExtinction.RankOneScattering
import PrescribedExtinction.Drive

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical
local notation "ScalarL2" => Lp ℂ 2 (volume : Measure Position)
local notation "Coordinate" => (PiLp.proj 2 (fun _ : Fin 3 => ℂ) 1 : Vector →L[ℂ] ℂ)

/-- The original plate drive after removal of the physical sine factor. -/
def normalizedIncidentDrive (k : ℝ) (B : TwoLayerBody) (σ : Direction) : ScalarBodyCurrentL2 B :=
  twoPieceSupportedMap volume B.domain (bodyAbsorberSlice B) (bodyAbsorberSlice_measurable B)
    (0 : Vector →L[ℂ] ℂ) Coordinate (bodyIncidentCurrent k B σ)

theorem normalizedIncidentDrive_coe (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    (normalizedIncidentDrive k B σ : ScalarL2) =ᵐ[volume]
      B.domain.indicator (fun x => if x 2 < B.absorberThickness then 0 else planePhase k σ x) := by
  unfold normalizedIncidentDrive
  filter_upwards [twoPieceSupportedMap_coe volume B.domain (bodyAbsorberSlice B)
    (bodyAbsorberSlice_measurable B) (0 : Vector →L[ℂ] ℂ) Coordinate
      (bodyIncidentCurrent k B σ), bodyIncidentCurrent_coe k B σ] with x hx hi
  rw [hx, hi]
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd]
    by_cases hxa : x 2 < B.absorberThickness <;>
      simp [bodyAbsorberSlice, hxa, PiLp.proj_apply, incidentElectric, basisC]
  · simp [hxd]

theorem activeProjectedIncident_sine_factorization (k : ℝ) (B : TwoLayerBody) (σ : Direction) (θ : ℝ) :
    activeProjection B (basisR 0) (rotatedAxis θ) (bodyIncidentCurrent k B σ) =
      (Real.sin θ : ℂ) • normalizedIncidentDrive k B σ := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [activeProjection_coe B (basisR 0) (rotatedAxis θ) (bodyIncidentCurrent k B σ),
    bodyIncidentCurrent_coe k B σ, normalizedIncidentDrive_coe k B σ,
    Lp.coeFn_smul (Real.sin θ : ℂ) (normalizedIncidentDrive k B σ : ScalarL2)] with x hp hi hg hs
  change (activeProjection B (basisR 0) (rotatedAxis θ) (bodyIncidentCurrent k B σ) : ScalarL2) x =
    ((Real.sin θ : ℂ) • (normalizedIncidentDrive k B σ : ScalarL2)) x
  rw [hp, hs]
  change _ = (Real.sin θ : ℂ) • (normalizedIncidentDrive k B σ : ScalarL2) x
  rw [hi, hg]
  by_cases hxd : x ∈ B.domain
  · rw [indicator_of_mem hxd, indicator_of_mem hxd]
    by_cases hxa : x 2 < B.absorberThickness
    · simp [hxa, incident_absorber_coupling]
    · simp [hxa, incident_plate_coupling, smul_eq_mul]
  · simp [hxd, axisCoupling]

def normalizedActiveResponse (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ScalarBodyCurrentL2 B :=
  (activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ).symm
    (-normalizedIncidentDrive k B σ)

theorem activePhysicalSolution_sine_factorization (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    activePhysicalSolution k hk B σ (basisR 0) (rotatedAxis θ) α β hα hβ =
      (Real.sin θ : ℂ) • normalizedActiveResponse k hk B σ θ α β hα hβ := by
  unfold activePhysicalSolution normalizedActiveResponse
  rw [activeProjectedIncident_sine_factorization]
  simp only [map_neg, map_smul, smul_neg]

theorem normalizedActiveResponse_norm_le (k : ℝ) (hk : 0 < k) (B : TwoLayerBody) (σ : Direction)
    (θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    ‖normalizedActiveResponse k hk B σ θ α β hα hβ‖ ≤
      (1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β)) * ‖normalizedIncidentDrive k B σ‖ := by
  let e := activeMaterialEquiv k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  have hn := e.symm.toContinuousLinearMap.le_opNorm (-normalizedIncidentDrive k B σ)
  have he := activeMaterialEquiv_inverse_norm_le k hk B (basisR 0) (rotatedAxis θ) α β hα hβ
  exact hn.trans (by simpa only [norm_neg] using
    mul_le_mul_of_nonneg_right he (norm_nonneg (-normalizedIncidentDrive k B σ)))

end OQ7Prescribed
