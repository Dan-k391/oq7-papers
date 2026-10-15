import GeneralizedResearch.ActualStackBeamFields
import GeneralizedResearch.SuperposedMaxwell

/-! Compact-disk continuity and genuine finite transverse L² of the actual
absorber, plate and vacuum fields, with the same derived scattering states. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.ActualStackContinuity
open ActualStackBeamFields ObliqueVacuum ObliqueMaxwell ObliqueFamily
open ObliqueWaveBasis TransferScattering FourierMaxwell
open MeasureTheory Set
open scoped Matrix
abbrev Transverse := BeamAveraging.Transverse

theorem leftWaves_continuous : Continuous (leftWaves : Mat4 → Mat4) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  rcases i with i|i <;> rcases j with j|j <;> simp [leftWaves, Matrix.fromBlocks]
  all_goals
    first
    | exact continuous_const
    | change Continuous (fun a : Mat4 => a _ _); fun_prop

theorem rightWaves_continuous : Continuous (rightWaves : Mat4 → Mat4) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  rcases i with i|i <;> rcases j with j|j <;> simp [rightWaves, Matrix.fromBlocks]
  all_goals
    first
    | exact continuous_const
    | change Continuous (fun a : Mat4 => a _ _); fun_prop

theorem response_continuousOn (p : Parameters) (r : ℝ) (hr : r < p.k) :
    ContinuousOn (fun q : Transverse => p.S (WithLp.ofLp q)) (BeamPackets.disk r) := by
  intro q hq
  have h := ObliqueFamily.response_continuousAt (k := p.k) (η := p.η) (h := p.h)
    p.j (p := (WithLp.ofLp q, p.t)) p.hk p.hη p.hh p.hj (propagating_disk p r hr q hq)
  have hm : Continuous (fun q : Transverse => (WithLp.ofLp q, p.t)) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).prodMk continuous_const
  exact (h.comp (f := fun q : Transverse => (WithLp.ofLp q, p.t)) hm.continuousAt).continuousWithinAt

theorem basis_continuousOn (p : Parameters) (r : ℝ) (hr : r < p.k) :
    ContinuousOn (fun q : Transverse => basis p.k (WithLp.ofLp q)) (BeamPackets.disk r) := by
  intro q hq
  exact (((ObliqueFamily.basis_continuousAt p.hk (propagating_disk p r hr q hq)).1).comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).continuousAt).continuousWithinAt

theorem initial_continuousOn (p : Parameters) (r : ℝ) (hr : r < p.k)
    (u : Transverse → Channel → ℂ) (hu : ContinuousOn u (BeamPackets.disk r)) :
    ContinuousOn (fun q => p.initialLeft (WithLp.ofLp q) (u q)) (BeamPackets.disk r) ∧
      ContinuousOn (fun q => p.initialRight (WithLp.ofLp q) (u q)) (BeamPackets.disk r) := by
  have hs := response_continuousOn p r hr
  have hb := basis_continuousOn p r hr
  have hl := leftWaves_continuous.comp_continuousOn hs
  have hr' := rightWaves_continuous.comp_continuousOn hs
  constructor
  · simpa only [Parameters.initialLeft, leftState_eq_leftWaves, Parameters.S, Parameters.K,
      ObliqueFamily.response, Function.comp_def] using
      SuperposedMaxwell.matrixVector_continuousOn _ _ _ hb
        (SuperposedMaxwell.matrixVector_continuousOn _ _ _ hl hu)
  · simpa only [Parameters.initialRight, rightState_eq_rightWaves, Parameters.S, Parameters.K,
      ObliqueFamily.response, Function.comp_def] using
      SuperposedMaxwell.matrixVector_continuousOn _ _ _ hb
        (SuperposedMaxwell.matrixVector_continuousOn _ _ _ hr' hu)

theorem transfer_continuous (k z : ℝ) (R Q : RMat) :
    Continuous (fun q : Transverse => transfer k (WithLp.ofLp q) R Q z) := by
  have hm : Continuous (fun q : Transverse => (WithLp.ofLp q, (0 : ℝ))) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).prodMk continuous_const
  exact (ObliqueMaxwell.transfer_continuous k z (fun _ => R) (fun _ => Q)
    continuous_const continuous_const).comp (f := fun q : Transverse => (WithLp.ofLp q, (0 : ℝ))) hm

theorem states_continuousOn (p : Parameters) (r : ℝ) (hr : r < p.k)
    (u : Transverse → Channel → ℂ) (hu : ContinuousOn u (BeamPackets.disk r)) (z : ℝ) :
    ContinuousOn (fun q => p.absorberState (WithLp.ofLp q) (u q) z) (BeamPackets.disk r) ∧
      ContinuousOn (fun q => p.plateState (WithLp.ofLp q) (u q) z) (BeamPackets.disk r) ∧
      ContinuousOn (fun q => p.leftVacuumState (WithLp.ofLp q) (u q) z) (BeamPackets.disk r) ∧
      ContinuousOn (fun q => p.rightVacuumState (WithLp.ofLp q) (u q) z) (BeamPackets.disk r) := by
  have hi := initial_continuousOn p r hr u hu
  have ha (z : ℝ) := SuperposedMaxwell.matrixVector_continuousOn _ _ _
    (transfer_continuous p.k z 1 (absorberLoss p.η)).continuousOn hi.1
  exact ⟨ha z,
    SuperposedMaxwell.matrixVector_continuousOn _ _ _
      (transfer_continuous p.k (z - p.h) (PlanarPlateBridge.tensor p.j p.t) 0).continuousOn (ha p.h),
    SuperposedMaxwell.matrixVector_continuousOn _ _ _
      (transfer_continuous p.k z 1 0).continuousOn hi.1,
    SuperposedMaxwell.matrixVector_continuousOn _ _ _
      (transfer_continuous p.k (z - (p.h + p.thickness)) 1 0).continuousOn hi.2⟩

theorem trace_eq_componentTrace (r k : ℝ) (F : Transverse → Channel → ℂ)
    (x : Transverse) (i : Fin 3) :
    (trace r k F (WithLp.ofLp x 0) (WithLp.ofLp x 1)).1 i =
      componentTrace r (fun q => electric k (WithLp.ofLp q) (F q) i) x ∧
    (trace r k F (WithLp.ofLp x 0) (WithLp.ofLp x 1)).2 i =
      componentTrace r (fun q => magnetic k (WithLp.ofLp q) (F q) i) x := by
  have hx : WithLp.toLp 2 ![WithLp.ofLp x 0, WithLp.ofLp x 1] = x := by
    ext j; fin_cases j <;> rfl
  constructor <;> dsimp only [trace, componentTrace]
  all_goals
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun q => by dsimp only; rw [phase_inner, hx])

theorem trace_memLp (r k : ℝ) (F : Transverse → Channel → ℂ)
    (hF : ContinuousOn F (BeamPackets.disk r)) (i : Fin 3) :
    MemLp (fun x : Transverse => (trace r k F (WithLp.ofLp x 0) (WithLp.ofLp x 1)).1 i) 2 volume ∧
      MemLp (fun x : Transverse => (trace r k F (WithLp.ofLp x 0) (WithLp.ofLp x 1)).2 i) 2 volume := by
  have he := (SuperposedMaxwell.electric_continuous k).comp_continuousOn
    (continuous_id.continuousOn.prodMk hF)
  have hm := (SuperposedMaxwell.magnetic_continuous k).comp_continuousOn
    (continuous_id.continuousOn.prodMk hF)
  have hei : ContinuousOn (fun q => electric k (WithLp.ofLp q) (F q) i) (BeamPackets.disk r) :=
    fun q hq => continuousWithinAt_pi.mp (he q hq) i
  have hmi : ContinuousOn (fun q => magnetic k (WithLp.ofLp q) (F q) i) (BeamPackets.disk r) :=
    fun q hq => continuousWithinAt_pi.mp (hm q hq) i
  have hE := componentTrace_ae r _ hei
  have hH := componentTrace_ae r _ hmi
  constructor
  · exact MemLp.ae_eq (hE.trans (ae_of_all _ (fun x => (trace_eq_componentTrace r k F x i).1.symm)))
      (Lp.memLp _)
  · exact MemLp.ae_eq (hH.trans (ae_of_all _ (fun x => (trace_eq_componentTrace r k F x i).2.symm)))
      (Lp.memLp _)

/-- Every longitudinal slice in every actual material or exterior region has
finite transverse electric and magnetic L² components. -/
theorem actual_states_finite (p : Parameters) (r : ℝ) (hr : r < p.k)
    (u : Transverse → Channel → ℂ) (hu : ContinuousOn u (BeamPackets.disk r))
    (z : ℝ) (i : Fin 3) :
    (MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.absorberState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).1 i) 2 volume ∧
      MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.absorberState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).2 i) 2 volume) ∧
    (MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.plateState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).1 i) 2 volume ∧
      MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.plateState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).2 i) 2 volume) ∧
    (MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.leftVacuumState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).1 i) 2 volume ∧
      MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.leftVacuumState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).2 i) 2 volume) ∧
    (MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.rightVacuumState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).1 i) 2 volume ∧
      MemLp (fun x : Transverse =>
      (trace r p.k (fun q => p.rightVacuumState (WithLp.ofLp q) (u q) z)
        (WithLp.ofLp x 0) (WithLp.ofLp x 1)).2 i) 2 volume) := by
  have hs := states_continuousOn p r hr u hu z
  exact ⟨trace_memLp r p.k _ hs.1 i, trace_memLp r p.k _ hs.2.1 i,
    trace_memLp r p.k _ hs.2.2.1 i, trace_memLp r p.k _ hs.2.2.2 i⟩

end GeneralizedResearch.ActualStackContinuity
