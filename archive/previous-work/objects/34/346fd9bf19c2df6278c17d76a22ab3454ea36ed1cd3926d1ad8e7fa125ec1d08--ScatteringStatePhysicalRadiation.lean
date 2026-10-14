import work.PhysicalSphereFlux
import PrescribedExtinction.WeakPhysicalRepresentation
import PrescribedExtinction.ForwardOpticalTheorem

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Filter
open scoped Topology

def scatteringStateRadiatingElectric {k : ℝ} {B : TwoLayerBody} {σ : Direction}
    (s : ScatteringState k B σ) : Field :=
  outgoingElectricField k (physicalCompactPolarization B s.electric s.maxwell.1)

def scatteringStateRadiatingMagnetic {k : ℝ} {B : TwoLayerBody} {σ : Direction}
    (s : ScatteringState k B σ) : Field :=
  outgoingMagneticField k (physicalCompactPolarization B s.electric s.maxwell.1)

def scatteringStateSphereFlux {k : ℝ} {B : TwoLayerBody} {σ : Direction}
    (s : ScatteringState k B σ) (r : ℝ) : ℝ :=
  ∫ n : UnitSphere, r ^ 2 * (pairing (scatteringStateRadiatingElectric s (r • (n : Position)))
    (cross (scatteringStateRadiatingMagnetic s (r • (n : Position))) (complexify (n : Position)))).re ∂sphereArea

theorem scatteringStateSphereFlux_eq_exterior (k : ℝ) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) (r : ℝ)
    (hr : 2 * (physicalCompactPolarization B s.electric s.maxwell.1).radius + 2 ≤ r) :
    scatteringStateSphereFlux s r = exteriorSphereFlux k (physicalCompactPolarization B s.electric s.maxwell.1) r := by
  classical
  let p := physicalCompactPolarization B s.electric s.maxwell.1
  have hrpos : 0 < r := by linarith [p.radius_nonneg]
  unfold scatteringStateSphereFlux exteriorSphereFlux
  apply integral_congr_ae
  apply ae_of_all
  intro n
  have hn : ‖r • (n : Position)‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, unitSphere_norm]
  have hx : r • (n : Position) ∈ currentExterior p := by change p.radius + 1 < ‖r • (n : Position)‖; rw [hn]; linarith [p.radius_nonneg]
  have hm := magneticExterior_eq_pointwise_far k p (r • (n : Position)) (by rw [hn]; linarith [p.radius_nonneg])
  have he : scatteringStateRadiatingElectric s (r • (n : Position)) = exteriorElectric k p (r • (n : Position)) := by
    change (if r • (n : Position) ∈ currentExterior p then exteriorElectric k p (r • (n : Position))
      else electricVolumeField k p (r • (n : Position))) = _
    rw [if_pos hx]
  have hmag : scatteringStateRadiatingMagnetic s (r • (n : Position)) = exteriorMagnetic k p (r • (n : Position)) := hm.symm
  change r ^ 2 * (pairing (scatteringStateRadiatingElectric s (r • (n : Position)))
    (cross (scatteringStateRadiatingMagnetic s (r • (n : Position))) (complexify (n : Position)))).re =
    r ^ 2 * (pairing (exteriorElectric k p (r • (n : Position)))
    (cross (exteriorMagnetic k p (r • (n : Position))) (complexify (n : Position)))).re
  rw [he, hmag]

theorem scatteringState_radiating_representative (k : ℝ) (hk : 0 < k)
    (B : TwoLayerBody) (σ : Direction) (s : ScatteringState k B σ) :
    s.electric =ᵐ[volume] (fun x => incidentElectric k σ x + scatteringStateRadiatingElectric s x) ∧
      s.magnetic =ᵐ[volume] (fun x => incidentMagnetic k σ x + scatteringStateRadiatingMagnetic s x) :=
  scatteringState_outgoing_volume_representation k hk B σ s

/-- The original current far field is the actual far-field amplitude of
the canonical radiating representative, uniformly over the entire sphere. -/
theorem scatteringState_currentFarField_is_physical (k : ℝ) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) :
    let p := physicalCompactPolarization B s.electric s.maxwell.1
    ∀ r : ℝ, 2 * p.radius + 2 ≤ r → ∀ n : UnitSphere,
      ‖((r : ℂ) * Complex.exp (-Complex.I * ((k * r : ℝ) : ℂ))) •
        scatteringStateRadiatingElectric s (r • (n : Position)) - currentFarField k B s.electric n‖ ≤
        farFieldKernelConstant k p.radius / r * (∫ y : Position, ‖p.current y‖) := by
  classical
  let p := physicalCompactPolarization B s.electric s.maxwell.1
  dsimp only
  intro r hr n
  have hrpos : 0 < r := by linarith [p.radius_nonneg]
  have hn : ‖r • (n : Position)‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, unitSphere_norm]
  have hx : r • (n : Position) ∈ currentExterior p := by change p.radius + 1 < ‖r • (n : Position)‖; rw [hn]; linarith [p.radius_nonneg]
  have h := exteriorElectric_uniform_farField_error k p (r • (n : Position)) (by rw [hn]; exact hr)
  rw [hn, radialDirection_positive_smul r hrpos n] at h
  rw [physicalCurrentFarField_eq_compact k B s.electric s.maxwell.1]
  have he : scatteringStateRadiatingElectric s (r • (n : Position)) = exteriorElectric k p (r • (n : Position)) := by
    change (if r • (n : Position) ∈ currentExterior p then exteriorElectric k p (r • (n : Position))
      else electricVolumeField k p (r • (n : Position))) = _
    rw [if_pos hx]
  rw [he]
  exact h

/-- The original all-angle scattering cross section is the limit of the
actual outward Poynting flux through full expanding physical spheres. -/
theorem scatteringState_scattering_is_physical_flux (k : ℝ) (B : TwoLayerBody)
    (σ : Direction) (s : ScatteringState k B σ) :
    Tendsto (scatteringStateSphereFlux s) atTop
      (𝓝 (scattering k B s.electric)) := by
  have h := exteriorSphereFlux_tendsto k (physicalCompactPolarization B s.electric s.maxwell.1)
  have he : scattering k B s.electric = ∫ n : UnitSphere,
      ‖compactCurrentFarField k (physicalCompactPolarization B s.electric s.maxwell.1) n‖ ^ 2 ∂sphereArea := by
    rw [physicalScattering_eq_Haar k B s.electric s.maxwell.1]
    simp_rw [physicalCurrentFarField_eq_compact k B s.electric s.maxwell.1]
  rw [he]
  have heq : scatteringStateSphereFlux s =ᶠ[atTop]
      exteriorSphereFlux k (physicalCompactPolarization B s.electric s.maxwell.1) := by
    filter_upwards [eventually_ge_atTop (2 * (physicalCompactPolarization B s.electric s.maxwell.1).radius + 2)] with r hr
    exact scatteringStateSphereFlux_eq_exterior k B σ s r hr
  exact h.congr' heq.symm

end OQ7Prescribed
