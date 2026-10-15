import GeneralizedResearch.PhysicalBeamUpper
import GeneralizedResearch.BoundaryFlux
import GeneralizedResearch.BeamPhysicalPackets
import GeneralizedResearch.BeamTimeReversal
import GeneralizedResearch.ActualStackMaxwell

/-! Original Corollary 6.5: the exact physical oblique stack, classical regional
Maxwell fields, matched interfaces, genuine finite transverse L² packets and
physical Poynting powers all use the same constructed capped design. -/
noncomputable section
namespace GeneralizedResearch.PhysicalBeamCorollary
open MeasureTheory Set PhysicalBeamL2 BeamPackets BeamAveraging BeamFibers
open ActualStackBeamFields ActualStackContinuity ActualStackMaxwell
open ObliqueMaxwell FourierMaxwell
open scoped Matrix
abbrev Transverse := BeamAveraging.Transverse

def parameters (d:Design) : Parameters := ⟨d.k,d.η,d.h,d.t,d.j,d.hk,d.hη,d.hh,d.hj⟩
def coefficient (d:Design) : ℂ := ((Real.sqrt (volume.real (disk d.r)):ℂ)⁻¹)
def amplitude (d:Design) (u:Transverse→Channel→ℂ) : Transverse→Channel→ℂ := fun q=>coefficient d • u q

theorem amplitude_continuousOn (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ContinuousOn (amplitude d u) (disk d.r) := hu.const_smul (coefficient d)

theorem parameters_response (d:Design) (q:Transverse) : (parameters d).S (WithLp.ofLp q)=d.S q := rfl

def finitePair (F:ℝ→ℝ→ℝ→Vec3×Vec3) : Prop := ∀z i,
  MemLp (fun x:Transverse=>(F (WithLp.ofLp x 0) (WithLp.ofLp x 1) z).1 i) 2 volume ∧
  MemLp (fun x:Transverse=>(F (WithLp.ofLp x 0) (WithLp.ofLp x 1) z).2 i) 2 volume

def materialFields (d:Design) (u:Transverse→Channel→ℂ) :=
  (physical (absorber (parameters d) d.r (amplitude d u)),physical (plate (parameters d) d.r (amplitude d u)))
def exteriorFields (d:Design) (u:Transverse→Channel→ℂ) :=
  (physical (vacuumLeft (parameters d) d.r (amplitude d u)),physical (vacuumRight (parameters d) d.r (amplitude d u)))

/-- This is an explicitly stated property of the defined fields, not an input
hypothesis on a scattering matrix or a record storing the desired conclusions. -/
def Realizes (d:Design) (u:Transverse→Channel→ℂ) : Prop :=
  Satisfies d.k 1 (ObliqueFamily.absorberLoss d.η) (materialFields d u).1 ∧
  Satisfies d.k (PlanarPlateBridge.tensor d.j d.t) 0 (materialFields d u).2 ∧
  Satisfies d.k 1 0 (exteriorFields d u).1 ∧ Satisfies d.k 1 0 (exteriorFields d u).2 ∧
  (∀x y,(exteriorFields d u).1 x y 0=(materialFields d u).1 x y 0 ∧
    (materialFields d u).1 x y d.h=(materialFields d u).2 x y d.h ∧
    (materialFields d u).2 x y (d.h+(parameters d).thickness)=
      (exteriorFields d u).2 x y (d.h+(parameters d).thickness)) ∧
  finitePair (materialFields d u).1 ∧ finitePair (materialFields d u).2 ∧
  finitePair (exteriorFields d u).1 ∧ finitePair (exteriorFields d u).2

theorem realizes (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) : Realizes d u := by
  have hr : d.r<(parameters d).k := by change d.r<d.k;linarith [d.hrk,d.hk]
  have ha := amplitude_continuousOn d u hu
  have hm := actual_regional_maxwell (parameters d) d.r hr (amplitude d u) ha
  refine ⟨physical_maxwell hm.1,physical_maxwell hm.2.1,physical_maxwell hm.2.2.1,
    physical_maxwell hm.2.2.2,?_,?_,?_,?_,?_⟩
  · intro x y
    have hi := actual_interfaces (parameters d) d.r hr (amplitude d u) x y
    exact ⟨congrArg (fun v:Vec3×Vec3=>((Real.sqrt 2:ℂ) • v.1,(Real.sqrt 2:ℂ) • v.2)) hi.1,
      congrArg (fun v:Vec3×Vec3=>((Real.sqrt 2:ℂ) • v.1,(Real.sqrt 2:ℂ) • v.2)) hi.2.1,
      congrArg (fun v:Vec3×Vec3=>((Real.sqrt 2:ℂ) • v.1,(Real.sqrt 2:ℂ) • v.2)) hi.2.2⟩
  all_goals intro z i
  all_goals have hs := actual_states_finite (parameters d) d.r hr (amplitude d u) ha z i
  · exact ⟨hs.1.1.const_smul (Real.sqrt 2:ℂ),hs.1.2.const_smul (Real.sqrt 2:ℂ)⟩
  · exact ⟨hs.2.1.1.const_smul (Real.sqrt 2:ℂ),hs.2.1.2.const_smul (Real.sqrt 2:ℂ)⟩
  · exact ⟨hs.2.2.1.1.const_smul (Real.sqrt 2:ℂ),hs.2.2.1.2.const_smul (Real.sqrt 2:ℂ)⟩
  · exact ⟨hs.2.2.2.1.const_smul (Real.sqrt 2:ℂ),hs.2.2.2.2.const_smul (Real.sqrt 2:ℂ)⟩

theorem radiation (d:Design) (u:Transverse→Channel→ℂ) (q:Transverse) (hq:q∈disk d.r) (z:ℝ) :
    (parameters d).leftVacuumState (WithLp.ofLp q) (amplitude d u q) z=
      ObliqueWaveBasis.basis d.k (WithLp.ofLp q)*ᵥ
        (VacuumReference.traveling (ObliqueVacuum.longitudinal d.k (WithLp.ofLp q)) z*ᵥ
          (TransferScattering.leftWaves (d.S q)*ᵥamplitude d u q)) ∧
    (parameters d).rightVacuumState (WithLp.ofLp q) (amplitude d u q) z=
      ObliqueWaveBasis.basis d.k (WithLp.ofLp q)*ᵥ
        (VacuumReference.traveling (ObliqueVacuum.longitudinal d.k (WithLp.ofLp q))
          (z-(d.h+(parameters d).thickness))*ᵥ
          (TransferScattering.rightWaves (d.S q)*ᵥamplitude d u q)) := by
  have hr : d.r<(parameters d).k := by change d.r<d.k;linarith [d.hrk,d.hk]
  have hκ := propagating_disk (parameters d) d.r hr q hq
  exact ⟨left_outgoing_expansion (parameters d) _ hκ _ z,right_outgoing_expansion (parameters d) _ hκ _ z⟩

theorem actual_reference (d:Design) (q:Transverse) (hq:q∈disk d.r) :
    TransferScattering.scattering (ObliqueWaveBasis.waveTransfer d.k (WithLp.ofLp q)
      (transfer d.k (WithLp.ofLp q) 1 0 (d.h+(parameters d).thickness)))=d.S0 q := by
  have hr : d.r<(parameters d).k := by change d.r<d.k;linarith [d.hrk,d.hk]
  exact VacuumReference.vacuum_scattering d.hk (propagating_disk (parameters d) d.r hr q hq)
    (add_nonneg d.hh (OQ7Prescribed.plateDesignThickness_pos d.k d.hk d.j d.hj).le)

theorem true_time_reverse (d:Design) :
    BeamTimeReversal.reversedSpectrum d.S0 (spectrum d.r (fun _=>left))=spectrum d.r d.reverseInput :=
  BeamTimeReversal.actual_reversed_packet d.k (d.h+(parameters d).thickness) d.r


def loss3 (d:Design) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![d.η,0,0]

theorem material_caps (d:Design) {P Q:ℝ} (hP:1<P) (hQ:0<Q)
    (hη:d.η≤Q) (hcap:OQ7Prescribed.plateDesignPermittivity d.j≤P) (ht0:-1≤d.t) (ht1:d.t≤1) :
    (PlanarPlateBridge.tensor3 d.j d.t-1).PosSemidef ∧
      (P • (1:Matrix (Fin 3) (Fin 3) ℝ)-PlanarPlateBridge.tensor3 d.j d.t).PosSemidef ∧
      (loss3 d).PosSemidef ∧ (Q • (1:Matrix (Fin 3) (Fin 3) ℝ)-loss3 d).PosSemidef ∧
      (P • (1:Matrix (Fin 3) (Fin 3) ℝ)-1).PosSemidef := by
  have hp := PlanarPlateBridge.tensor3_bounds d.j d.hj ht0 ht1 hcap
  refine ⟨hp.1,hp.2,?_,?_,?_⟩
  · rw [loss3,Matrix.posSemidef_diagonal_iff]
    intro i;fin_cases i <;> simp [d.hη]
  · have he : Q • (1:Matrix (Fin 3) (Fin 3) ℝ)-loss3 d=Matrix.diagonal ![Q-d.η,Q,Q] := by
      ext i j;fin_cases i <;> fin_cases j <;> simp [loss3]
    rw [he,Matrix.posSemidef_diagonal_iff]
    intro i;fin_cases i <;> simp [sub_nonneg.mpr hη,hQ.le]
  · have he : P • (1:Matrix (Fin 3) (Fin 3) ℝ)-1=(P-1) • (1:Matrix (Fin 3) (Fin 3) ℝ) := by module
    rw [he]
    exact Matrix.PosSemidef.one.smul (by linarith)

/-- Literal original finite-power conclusion. Both actual normalized inputs
have matched Maxwell realizations in the same capped two-layer physical design. -/
theorem corollary65 (k P Q X0 ε:ℝ) (hk:0<k) (hP:1<P) (hQ:0<Q)
    (hX0:0<X0) (hX4:X0<4) (hε:0<ε) :
    ∃d:Design,d.k=k ∧ 0<d.η ∧ d.η≤Q ∧ 0<d.h ∧ OQ7Prescribed.plateDesignPermittivity d.j≤P ∧
      -1<d.t ∧ d.t<1 ∧ Realizes d (fun _=>left) ∧ Realizes d d.reverseInput ∧
      ‖beam d.r (fun _=>left) continuousOn_const‖=1 ∧
      ‖beam d.r d.reverseInput d.reverse_continuous.continuousOn‖=1 ∧
      extinction d (fun _=>left) continuousOn_const=X0 ∧
      extinction d d.reverseInput d.reverse_continuous.continuousOn=X0 ∧
      X0-X0^2/4-ε≤|absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const| ∧
      |absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const|≤X0-X0^2/4 ∧
      (1/2:ℝ)*(inner ℂ (BoundaryFlux.electricField d (fun _=>left) continuousOn_const)
        (BoundaryFlux.magneticField d (fun _=>left) continuousOn_const)).re=absorption d (fun _=>left) continuousOn_const ∧
      (1/2:ℝ)*(inner ℂ (BoundaryFlux.electricField d d.reverseInput d.reverse_continuous.continuousOn)
        (BoundaryFlux.magneticField d d.reverseInput d.reverse_continuous.continuousOn)).re=
          absorption d d.reverseInput d.reverse_continuous.continuousOn := by
  obtain ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,hunit,hunit',hx,hx',hd⟩ :=
    corollary65_approach k P Q X0 ε hk hP hQ hX0 hX4 hε
  have hup := PhysicalBeamUpper.physical_parabola d
  rw [hx] at hup
  exact ⟨d,hk',hη,hηQ,hh,hcap,ht0,ht1,realizes d _ continuousOn_const,
    realizes d _ d.reverse_continuous.continuousOn,hunit,hunit',hx,hx',hd,hup,
    BoundaryFlux.normalized_net_absorption d _ continuousOn_const hunit,
    BoundaryFlux.normalized_net_absorption d _ d.reverse_continuous.continuousOn hunit'⟩

end GeneralizedResearch.PhysicalBeamCorollary
