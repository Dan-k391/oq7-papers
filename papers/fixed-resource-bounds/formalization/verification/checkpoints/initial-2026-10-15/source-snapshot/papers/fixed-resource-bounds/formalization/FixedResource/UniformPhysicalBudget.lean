import FixedResource.MaxwellCore
import FixedResource.PowerIntervals

/-! Actual full-sphere bounds under a uniform susceptibility cap and loss floor.
The budget here is |D| M²/m. The sharper c²/δ+Q budget and variable L¹ response
budget in the manuscript are separate obligations, not claimed by this file. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FixedResource
open MeasureTheory Set OQ7Prescribed QuarticMaxwell WeakMaterial PhysicalPowers

def uniformBudget (B : Medium) : ℝ := volume.real B.domain * (B.M ^ 2 / B.m)
def uniformBeta (B : Medium) (k : ℝ) : ℝ := k ^ 3 * uniformBudget B / (6 * Real.pi)

theorem current_norm_loss (B : Medium) {k : ℝ} (hk : 0 < k) (E : Field)
    (hE : LocallySquareIntegrable E) :
    ‖currentL2 B E hE‖ ^ 2 ≤ (B.M ^ 2 / B.m) * absorption B k E / k := by
  have h := TensorMultiplier.inverse_loss_bound volume B.domain B.susceptibility
    B.measurable_susceptibility B.M B.cap B.measurable B.m_pos B.loss B.M_pos (currentL2 B E hE)
  rw [absorption_eq_volume B k E hE]
  unfold UniformBound.absorptionPower
  have hm := B.m_pos
  have hM := B.M_pos
  change B.m / B.M ^ 2 * ‖currentL2 B E hE‖ ^ 2 ≤
    -(inner ℂ (currentL2 B E hE) (VolumeInverse.inverseSusceptibility B.domain B.measurable
      B.susceptibility B.measurable_susceptibility B.M B.cap B.m_pos B.loss (currentL2 B E hE))).im at h
  apply (le_div_iff₀ hk).mpr
  have h' := (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ B.M ^ 2 / B.m * k))
  field_simp at h' ⊢
  nlinarith

theorem physical_scattering_efficiency (B : Medium) {k : ℝ} (hk : 0 < k)
    (E : Field) (hE : LocallySquareIntegrable E) :
    scattering B k E hE ≤ uniformBeta B k * absorption B k E := by
  rw [scattering_eq_volume B k E hE]
  have hrad := radiationLp_norm_sq_bound k B.domain B.measurable B.finite (currentL2 B E hE : VectorL2)
  have hloss := current_norm_loss B hk E hE
  have hA := absorption_nonneg B k hk.le E hE
  have hM := B.M_pos
  have hm := B.m_pos
  change ‖domainRadiationMap k B.domain B.measurable B.finite (currentL2 B E hE)‖ ^ 2 ≤
    8 * Real.pi * volume.real B.domain / 3 * ‖currentL2 B E hE‖ ^ 2 at hrad
  unfold UniformBound.scatteringPower uniformBeta uniformBudget
  calc
    _ ≤ k ^ 4 / (16 * Real.pi ^ 2) *
        (8 * Real.pi * volume.real B.domain / 3 * ‖currentL2 B E hE‖ ^ 2) := by gcongr
    _ ≤ k ^ 4 / (16 * Real.pi ^ 2) *
        (8 * Real.pi * volume.real B.domain / 3 *
          ((B.M ^ 2 / B.m) * absorption B k E / k)) := by gcongr
    _ = _ := by field_simp; ring

theorem physical_extinction_work (B : Medium) {k : ℝ} (hk : 0 < k)
    (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1)
    (E : Field) (hE : LocallySquareIntegrable E) :
    (extinction B k n e E) ^ 2 ≤ k * uniformBudget B * absorption B k E := by
  have hinner : extinction B k n e E =
      k * (inner ℂ (domainIncidentSource k n e B.domain B.measurable B.finite) (currentL2 B E hE)).im := by
    unfold PhysicalPowers.extinction
    rw [source_inner_current]
  have hn := norm_inner_le_norm (𝕜 := ℂ)
    (domainIncidentSource k n e B.domain B.measurable B.finite) (currentL2 B E hE)
  have hi := (Complex.abs_im_le_norm _).trans hn
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
  rw [sq_abs, mul_pow, domainIncidentSource_norm_sq, he, one_pow, mul_one] at hs
  have hloss := current_norm_loss B hk E hE
  have h := mul_le_mul_of_nonneg_left hloss (show 0 ≤ k ^ 2 * volume.real B.domain by positivity)
  have h0 := mul_le_mul_of_nonneg_left hs (sq_nonneg k)
  rw [hinner, mul_pow]
  unfold uniformBudget
  have hc : k ^ 2 * volume.real B.domain * ((B.M ^ 2 / B.m) * absorption B k E / k) =
      k * (volume.real B.domain * (B.M ^ 2 / B.m)) * absorption B k E := by field_simp
  rw [hc] at h
  nlinarith

theorem physical_uniform_pair (B : Medium) {k : ℝ} (hk : 0 < k)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0)
    (s : State B k n e) (t : State B k (opposite n) (vectorConjugate e))
    (hX : 0 < extinction B k n e s.electric) :
    |absorption B k s.electric - absorption B k t.electric| / extinction B k n e s.electric ≤
      uniformBeta B k / (1 + uniformBeta B k) ∧
    uniformBeta B k / (1 + uniformBeta B k) < 1 := by
  have hc := complex_pair_extinction B hk hsym n e htr s t
  have hp := state_power_balance B hk n e htr s
  have hm := state_power_balance B hk _ _ (conjugate_polarization_transverse n e htr) t
  rw [← hc] at hm
  have hb : 0 ≤ uniformBeta B k := by
    unfold uniformBeta uniformBudget
    exact div_nonneg (mul_nonneg (pow_nonneg hk.le _) (mul_nonneg (by positivity)
      (div_nonneg (sq_nonneg _) B.m_pos.le))) (by positivity)
  refine ⟨efficiency_pair hX hb hp hm (scattering_nonneg _ _ _ _) (scattering_nonneg _ _ _ _)
    (physical_scattering_efficiency B hk _ _) (physical_scattering_efficiency B hk _ _), ?_⟩
  exact (div_lt_one (by positivity : 0 < 1 + uniformBeta B k)).mpr (by linarith)

theorem physical_uniform_response_pair (B : Medium) {k : ℝ} (hk : 0 < k)
    (hV : 0 < volume.real B.domain)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
      bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u))
    (n : UnitSphere) (e : Vector) (he : ‖e‖ = 1)
    (htr : bilinear (complexify (n : QuarticMaxwell.Position)) e = 0)
    (s : State B k n e) (t : State B k (opposite n) (vectorConjugate e)) :
    PhysicalPowers.extinction B k n e s.electric ≤ k * uniformBudget B ∧
    |absorption B k s.electric - absorption B k t.electric| / extinction B k n e s.electric ≤
      min (uniformBeta B k / (1 + uniformBeta B k))
        (1 - extinction B k n e s.electric / (k * uniformBudget B)) := by
  have hc := complex_pair_extinction B hk hsym n e htr s t
  have hp := state_power_balance B hk n e htr s
  have hm := state_power_balance B hk _ _ (conjugate_polarization_transverse n e htr) t
  rw [← hc] at hm
  have hb : 0 ≤ uniformBeta B k := by
    unfold uniformBeta uniformBudget
    exact div_nonneg (mul_nonneg (pow_nonneg hk.le _) (mul_nonneg hV.le
      (div_nonneg (sq_nonneg _) B.m_pos.le))) (by positivity)
  have hK : 0 < k * uniformBudget B := by
    unfold uniformBudget
    exact mul_pos hk (mul_pos hV (div_pos (sq_pos_of_pos B.M_pos) B.m_pos))
  have hworkm := physical_extinction_work B hk (opposite n) (vectorConjugate e)
    (by rw [vectorConjugate_norm]; exact he) t.electric t.electric_L2
  rw [← hc] at hworkm
  exact response_pair (positive_extinction B hk hV n e he htr s) hb hK hp hm
    (scattering_nonneg _ _ _ _) (scattering_nonneg _ _ _ _)
    (physical_scattering_efficiency B hk _ _) (physical_scattering_efficiency B hk _ _)
    (physical_extinction_work B hk n e he _ s.electric_L2) hworkm

end FixedResource
