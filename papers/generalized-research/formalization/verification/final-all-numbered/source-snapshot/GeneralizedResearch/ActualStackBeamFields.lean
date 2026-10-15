import GeneralizedResearch.PhysicalFourierIntegral
import GeneralizedResearch.VacuumReference

/-! Actual absorber/plate/vacuum field states associated with the derived
scattering matrix. Every interface and incoming/outgoing boundary is derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.ActualStackBeamFields
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ObliqueFamily TransferScattering
open FourierMaxwell
open MeasureTheory Set
open scoped Matrix ComplexOrder

structure Parameters where
  k : ℝ
  η : ℝ
  h : ℝ
  t : ℝ
  j : ℕ
  hk : 0 < k
  hη : 0 ≤ η
  hh : 0 ≤ h
  hj : 1 ≤ j

namespace Parameters
def thickness (p : Parameters) : ℝ := OQ7Prescribed.plateDesignThickness p.k p.j
def K (p : Parameters) (κ : ObliqueVacuum.Transverse) : Mat4 :=
  ObliqueFamily.waveTransfer p.k p.η p.h p.j κ p.t
def S (p : Parameters) (κ : ObliqueVacuum.Transverse) : Mat4 := response p.k p.η p.h p.j κ p.t
def initialLeft (p : Parameters) (κ : ObliqueVacuum.Transverse) (u : Channel → ℂ) : Channel → ℂ :=
  basis p.k κ *ᵥ (leftState (p.K κ) *ᵥ u)
def initialRight (p : Parameters) (κ : ObliqueVacuum.Transverse) (u : Channel → ℂ) : Channel → ℂ :=
  basis p.k κ *ᵥ (rightState (p.K κ) *ᵥ u)

def absorberState (p : Parameters) (κ : ObliqueVacuum.Transverse) (u : Channel → ℂ) (z : ℝ) : Channel → ℂ :=
  transfer p.k κ 1 (absorberLoss p.η) z *ᵥ p.initialLeft κ u
def plateState (p : Parameters) (κ : ObliqueVacuum.Transverse) (u : Channel → ℂ) (z : ℝ) : Channel → ℂ :=
  transfer p.k κ (PlanarPlateBridge.tensor p.j p.t) 0 (z - p.h) *ᵥ p.absorberState κ u p.h
def leftVacuumState (p : Parameters) (κ : ObliqueVacuum.Transverse) (u : Channel → ℂ) (z : ℝ) : Channel → ℂ :=
  transfer p.k κ 1 0 z *ᵥ p.initialLeft κ u
def rightVacuumState (p : Parameters) (κ : ObliqueVacuum.Transverse) (u : Channel → ℂ) (z : ℝ) : Channel → ℂ :=
  transfer p.k κ 1 0 (z - (p.h + p.thickness)) *ᵥ p.initialRight κ u

theorem boundary (p : Parameters) (κ : ObliqueVacuum.Transverse) (hκ : square κ < p.k ^ 2)
    (u : Channel → ℂ) :
    fieldTransfer p.k p.η p.h p.j κ p.t *ᵥ p.initialLeft κ u = p.initialRight κ u := by
  have hpass := waveTransfer_passive p.k p.η p.h p.j κ p.t p.hk p.hη p.hh p.hj hκ
  have hb := congrArg (fun M : Mat4 => M *ᵥ u) (TransferScattering.boundary (p.K κ) (D_isUnit _ hpass))
  have hw := waveTransfer_boundary p.hk hκ (fieldTransfer p.k p.η p.h p.j κ p.t)
    (leftState (p.K κ) *ᵥ u)
  change basis p.k κ *ᵥ (p.K κ *ᵥ (leftState (p.K κ) *ᵥ u)) =
    fieldTransfer p.k p.η p.h p.j κ p.t *ᵥ p.initialLeft κ u at hw
  rw [← hw]
  unfold initialRight
  congr 1
  simpa only [Matrix.mulVec_mulVec] using hb

theorem interfaces (p : Parameters) (κ : ObliqueVacuum.Transverse) (hκ : square κ < p.k ^ 2)
    (u : Channel → ℂ) :
    p.leftVacuumState κ u 0 = p.absorberState κ u 0 ∧
      p.absorberState κ u p.h = p.plateState κ u p.h ∧
      p.plateState κ u (p.h + p.thickness) = p.rightVacuumState κ u (p.h + p.thickness) := by
  constructor
  · simp only [leftVacuumState, absorberState, transfer_initial, Matrix.one_mulVec]
  constructor
  · simp only [plateState, sub_self, transfer_initial, Matrix.one_mulVec]
  · simp only [plateState, rightVacuumState, add_sub_cancel_left, sub_self, transfer_initial, Matrix.one_mulVec]
    change (transfer p.k κ (PlanarPlateBridge.tensor p.j p.t) 0 p.thickness *ᵥ
      (transfer p.k κ 1 (absorberLoss p.η) p.h *ᵥ p.initialLeft κ u)) = _
    rw [Matrix.mulVec_mulVec]
    exact p.boundary κ hκ u

end Parameters

theorem leftState_eq_leftWaves (K : Mat4) : leftState K = leftWaves (scattering K) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [leftState, leftWaves, scattering]

theorem rightState_eq_rightWaves (K : Mat4) : rightState K = rightWaves (scattering K) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [rightState, rightWaves, scattering]

theorem vacuum_travel (k : ℝ) (hk : 0 < k) (κ : ObliqueVacuum.Transverse)
    (hκ : square κ < k ^ 2) (u : Channel → ℂ) (z : ℝ) :
    transfer k κ 1 0 z *ᵥ (basis k κ *ᵥ u) =
      basis k κ *ᵥ (VacuumReference.traveling (longitudinal k κ) z *ᵥ u) := by
  have h := waveTransfer_boundary hk hκ (transfer k κ 1 0 z) u
  rw [VacuumReference.vacuum_waveTransfer hk hκ z] at h
  exact h.symm

theorem left_outgoing_expansion (p : Parameters) (κ : ObliqueVacuum.Transverse)
    (hκ : square κ < p.k ^ 2) (u : Channel → ℂ) (z : ℝ) :
    p.leftVacuumState κ u z = basis p.k κ *ᵥ
      (VacuumReference.traveling (longitudinal p.k κ) z *ᵥ (leftWaves (p.S κ) *ᵥ u)) := by
  unfold Parameters.leftVacuumState Parameters.initialLeft
  rw [vacuum_travel p.k p.hk κ hκ, leftState_eq_leftWaves]
  rfl

theorem right_outgoing_expansion (p : Parameters) (κ : ObliqueVacuum.Transverse)
    (hκ : square κ < p.k ^ 2) (u : Channel → ℂ) (z : ℝ) :
    p.rightVacuumState κ u z = basis p.k κ *ᵥ
      (VacuumReference.traveling (longitudinal p.k κ) (z - (p.h + p.thickness)) *ᵥ
        (rightWaves (p.S κ) *ᵥ u)) := by
  unfold Parameters.rightVacuumState Parameters.initialRight
  rw [vacuum_travel p.k p.hk κ hκ, rightState_eq_rightWaves]
  rfl

theorem propagating_disk (p : Parameters) (r : ℝ) (hr : r < p.k)
    (q : BeamAveraging.Transverse) (hq : q ∈ BeamPackets.disk r) :
    square (WithLp.ofLp q) < p.k ^ 2 := by
  have hq' : ‖q‖ ≤ r := by simpa [BeamPackets.disk, Metric.mem_closedBall, dist_zero_right] using hq
  rw [BeamFibers.square_ofLp]
  nlinarith [norm_nonneg q, p.hk]

abbrev Transverse := BeamAveraging.Transverse

/-- Componentwise physical angular superposition of the full reconstructed
electric and magnetic fields, with the physical Fourier normalization. -/
def trace (r k : ℝ) (F : Transverse → Channel → ℂ) (x y : ℝ) : Vec3 × Vec3 :=
  (fun i => (PhysicalFourier.factor : ℂ) * ∫ q in BeamPackets.disk r,
    phase (WithLp.ofLp q) x y * electric k (WithLp.ofLp q) (F q) i,
   fun i => (PhysicalFourier.factor : ℂ) * ∫ q in BeamPackets.disk r,
    phase (WithLp.ofLp q) x y * magnetic k (WithLp.ofLp q) (F q) i)

theorem trace_congr (r k : ℝ) (F G : Transverse → Channel → ℂ)
    (h : ∀ q ∈ BeamPackets.disk r, F q = G q) (x y : ℝ) : trace r k F x y = trace r k G x y := by
  apply Prod.ext <;> funext i
  all_goals
    dsimp only [trace]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (isCompact_closedBall (0 : Transverse) r).measurableSet] with q hq
    rw [h q hq]

theorem integrated_interfaces (p : Parameters) (r : ℝ) (hr : r < p.k)
    (u : Transverse → Channel → ℂ) (x y : ℝ) :
    trace r p.k (fun q => p.leftVacuumState (WithLp.ofLp q) (u q) 0) x y =
      trace r p.k (fun q => p.absorberState (WithLp.ofLp q) (u q) 0) x y ∧
    trace r p.k (fun q => p.absorberState (WithLp.ofLp q) (u q) p.h) x y =
      trace r p.k (fun q => p.plateState (WithLp.ofLp q) (u q) p.h) x y ∧
    trace r p.k (fun q => p.plateState (WithLp.ofLp q) (u q) (p.h + p.thickness)) x y =
      trace r p.k (fun q => p.rightVacuumState (WithLp.ofLp q) (u q) (p.h + p.thickness)) x y := by
  constructor
  · apply trace_congr
    intro q hq
    exact (p.interfaces _ (propagating_disk p r hr q hq) (u q)).1
  constructor
  · apply trace_congr
    intro q hq
    exact (p.interfaces _ (propagating_disk p r hr q hq) (u q)).2.1
  · apply trace_congr
    intro q hq
    exact (p.interfaces _ (propagating_disk p r hr q hq) (u q)).2.2

theorem phase_inner (q : Transverse) (x y : ℝ) :
    phase (WithLp.ofLp q) x y =
      Complex.exp (Complex.I * ((inner ℝ q (WithLp.toLp 2 ![x, y]) : ℝ) : ℂ)) := by
  unfold phase OQ7Prescribed.apertureOscillation
  rw [← Complex.exp_add]
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem cutoff_memLp (r : ℝ) (f : Transverse → ℂ) (hf : ContinuousOn f (BeamPackets.disk r)) :
    MemLp ((BeamPackets.disk r).indicator f) 1 volume ∧
      MemLp ((BeamPackets.disk r).indicator f) 2 volume := by
  have hK : IsCompact (BeamPackets.disk r) := isCompact_closedBall _ _
  have hm := hK.measurableSet
  have : IsFiniteMeasure (volume.restrict (BeamPackets.disk r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.norm
  have hb : ∀ᵐ q ∂volume.restrict (BeamPackets.disk r), ‖f q‖ ≤ C := by
    filter_upwards [ae_restrict_mem hm] with q hq
    exact hC ⟨q, hq, rfl⟩
  constructor
  · exact (memLp_indicator_iff_restrict hm).mpr (MemLp.of_bound (hf.aestronglyMeasurable hm) C hb)
  · exact (memLp_indicator_iff_restrict hm).mpr (MemLp.of_bound (hf.aestronglyMeasurable hm) C hb)

def componentTrace (r : ℝ) (f : Transverse → ℂ) (x : Transverse) : ℂ :=
  (PhysicalFourier.factor : ℂ) * ∫ q in BeamPackets.disk r,
    Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) * f q

/-- These compact spatial field components are genuine finite-power L²
physical inverse Fourier transforms, with their literal angular integrals. -/
theorem componentTrace_ae (r : ℝ) (f : Transverse → ℂ) (hf : ContinuousOn f (BeamPackets.disk r)) :
    (PhysicalFourier.inverse ((cutoff_memLp r f hf).2.toLp ((BeamPackets.disk r).indicator f)) : Transverse → ℂ) =ᵐ[volume]
      componentTrace r f := by
  have h := PhysicalFourier.inverse_integral_ae (cutoff_memLp r f hf).1 (cutoff_memLp r f hf).2
  apply h.trans
  exact ae_of_all _ (fun x => by
    unfold PhysicalFourier.integralInverse componentTrace
    congr 1
    calc
      _ = ∫ q, (BeamPackets.disk r).indicator (fun q =>
          Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) * f q) q := by
        apply integral_congr_ae
        exact ae_of_all _ (fun q => by
          by_cases hq : q ∈ BeamPackets.disk r <;> simp [Set.indicator, hq])
      _ = _ := integral_indicator (isCompact_closedBall (0 : Transverse) r).measurableSet)

end GeneralizedResearch.ActualStackBeamFields
