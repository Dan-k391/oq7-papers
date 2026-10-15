import GeneralizedResearch.PhysicalFourierIntegral
import GeneralizedResearch.PhysicalBeamApproximation
import GeneralizedResearch.VacuumReference

/-! Actual finite-power input and output L² beams. Each spectrum is the
derived oblique Maxwell scattering response, and the spatial beams are their
genuine inverse Fourier transforms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
namespace GeneralizedResearch.PhysicalBeamL2
open MeasureTheory Set BeamAveraging BeamFibers BeamPackets
open ObliqueMaxwell ObliqueFamily FiniteHilbertBridge
open scoped Matrix Matrix.Norms.Operator Topology
abbrev Fiber := EuclideanSpace ℂ Channel
abbrev Wave := Lp Fiber 2 (volume:Measure BeamAveraging.Transverse)
abbrev Transverse := BeamAveraging.Transverse

structure Design where
  k : ℝ
  η : ℝ
  h : ℝ
  r : ℝ
  t : ℝ
  j : ℕ
  hk : 0<k
  hη : 0≤η
  hh : 0≤h
  hr : 0<r
  hrk : r≤k/2
  hj : 1≤j

namespace Design
def S (d:Design) (q:Transverse) : Mat4 := response d.k d.η d.h d.j (WithLp.ofLp q) d.t
def S0 (d:Design) (q:Transverse) : Mat4 := reference d.k (d.h+OQ7Prescribed.plateDesignThickness d.k d.j) (WithLp.ofLp q)
def reverseInput (d:Design) (q:Transverse) : Channel→ℂ := ChannelPowers.reverse (d.S0 q) left

theorem propagating (d:Design) {q:Transverse} (hq:q∈disk d.r) : ‖q‖<d.k := by
  have hn : ‖q‖≤d.r := by simpa [disk,Metric.mem_closedBall,dist_zero_right] using hq
  linarith [d.hk,d.hrk]

theorem S_continuousOn (d:Design) : ContinuousOn d.S (disk d.r) := by
  intro q hq
  have hκ : ObliqueVacuum.square (WithLp.ofLp q)<d.k^2 := by
    rw [square_ofLp]
    nlinarith [d.propagating hq,norm_nonneg q]
  have hp : Continuous (fun q:Transverse=>(WithLp.ofLp q,d.t)) :=
    (PiLp.continuous_ofLp 2 (fun _:Fin 2=>ℝ)).prodMk continuous_const
  exact (ContinuousAt.comp (f:=fun q:Transverse=>(WithLp.ofLp q,d.t))
    (response_continuousAt d.j d.hk d.hη d.hh d.hj hκ) hp.continuousAt).continuousWithinAt

theorem S0_continuous (d:Design) : Continuous d.S0 :=
  (reference_continuous _ _).comp (PiLp.continuous_ofLp 2 (fun _:Fin 2=>ℝ))

theorem reverse_continuous (d:Design) : Continuous d.reverseInput := by
  apply continuous_pi;intro i
  unfold reverseInput ChannelPowers.reverse
  have hc : Continuous (fun q:Transverse=>(d.S0 q*ᵥleft) i) := by
    unfold Matrix.mulVec dotProduct
    apply continuous_finsetSum;intro j _
    exact ((d.S0_continuous.matrix_elem i j).mul continuous_const)
  exact hc.star

theorem output_continuousOn (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ContinuousOn (fun q=>d.S q*ᵥu q) (disk d.r) := by
  intro q hq
  apply continuousWithinAt_pi.mpr;intro i
  exact tendsto_finsetSum Finset.univ (fun j _=>
    (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp (d.S_continuousOn q hq) i) j).mul
      (continuousWithinAt_pi.mp (hu q hq) j))

theorem background_continuousOn (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ContinuousOn (fun q=>d.S0 q*ᵥu q) (disk d.r) := by
  intro q hq
  apply continuousWithinAt_pi.mpr;intro i
  exact tendsto_finsetSum Finset.univ (fun j _=>
    (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp (d.S0_continuous.continuousOn q hq) i) j).mul
      (continuousWithinAt_pi.mp (hu q hq) j))
end Design

theorem vector_continuous : Continuous (vector (n:=Channel)) := PiLp.continuous_toLp 2 (fun _:Channel=>ℂ)

def spectrum (r:ℝ) (u:Transverse→Channel→ℂ) : Transverse→Fiber := packet r (fun q=>vector (u q))

theorem spectrum_memLp (r:ℝ) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) :
    MemLp (spectrum r u) 2 volume :=
  packet_memLp r _ (vector_continuous.comp_continuousOn hu)

def beam (r:ℝ) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) : Wave :=
  PhysicalFourier.inverse ((spectrum_memLp r u hu).toLp (spectrum r u))

theorem beam_norm_sq (r:ℝ) (hr:0<r) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) :
    ‖beam r u hu‖^2=diskAverage r (fun q=>ChannelPowers.power (u q)) := by
  rw [beam,PhysicalFourier.inverse_norm]
  simp only [spectrum]
  rw [packet_norm_sq r hr]
  congr 1
  funext q
  exact norm_sq_coordinates (vector (u q))

theorem beam_real_forward (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    (inner ℂ (beam d.r (fun q=>d.S0 q*ᵥu q) (d.background_continuousOn u hu))
      (beam d.r (fun q=>d.S q*ᵥu q) (d.output_continuousOn u hu))).re=
      diskAverage d.r (fun q=>(ChannelPowers.forward (d.S q) (d.S0 q) (u q)).re) := by
  rw [beam,beam,PhysicalFourier.inverse_inner]
  simp only [spectrum]
  rw [packet_real_inner d.r d.hr]
  congr 1
  funext q
  rw [inner_vector]
  rfl

theorem average_sub (r:ℝ) (f g:Transverse→ℝ) (hf:ContinuousOn f (disk r)) (hg:ContinuousOn g (disk r)) :
    diskAverage r (fun q=>f q-g q)=diskAverage r f-diskAverage r g := by
  unfold diskAverage BeamAveraging.average
  rw [integral_sub (hf.integrableOn_compact (isCompact_closedBall _ _))
    (hg.integrableOn_compact (isCompact_closedBall _ _))]
  ring

theorem average_const_sub (r:ℝ) (hr:0<r) (c:ℝ) (f:Transverse→ℝ) (hf:ContinuousOn f (disk r)) :
    diskAverage r (fun q=>c-f q)=c-diskAverage r f := by
  rw [average_sub r (fun _=>c) f continuousOn_const hf]
  have hc : diskAverage r (fun _:Transverse=>c)=c :=
    average_const volume (disk r) (disk_mass_pos hr) c
  rw [hc]

theorem average_const_mul (r c:ℝ) (f:Transverse→ℝ) :
    diskAverage r (fun q=>c*f q)=c*diskAverage r f := by
  unfold diskAverage BeamAveraging.average
  rw [integral_const_mul]
  ring

def absorption (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) : ℝ :=
  1-‖beam d.r (fun q=>d.S q*ᵥu q) (d.output_continuousOn u hu)‖^2
def extinction (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) : ℝ :=
  2*(1-(inner ℂ (beam d.r (fun q=>d.S0 q*ᵥu q) (d.background_continuousOn u hu))
    (beam d.r (fun q=>d.S q*ᵥu q) (d.output_continuousOn u hu))).re)

theorem power_continuousOn (r:ℝ) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) :
    ContinuousOn (fun q=>ChannelPowers.power (u q)) (disk r) := by
  have hc : Continuous (fun u:Channel→ℂ=>ChannelPowers.power u) := by
    unfold ChannelPowers.power dotProduct
    apply Complex.continuous_re.comp
    apply continuous_finsetSum;intro i _
    exact (continuous_apply i).star.mul (continuous_apply i)
  exact hc.comp_continuousOn hu

theorem absorption_average (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    absorption d u hu=diskAverage d.r (fun q=>ChannelPowers.absorption (d.S q) (u q)) := by
  rw [absorption,beam_norm_sq d.r d.hr]
  exact (average_const_sub d.r d.hr 1 _
    (power_continuousOn d.r _ (d.output_continuousOn u hu))).symm

theorem real_pairing_continuousOn {Y:Type*} [TopologicalSpace Y] (B:Set Y)
    (a b:Y→Channel→ℂ) (ha:ContinuousOn a B) (hb:ContinuousOn b B) :
    ContinuousOn (fun q=>(star (a q) ⬝ᵥ b q).re) B := by
  intro q hq
  apply Complex.continuous_re.continuousAt.comp_continuousWithinAt
  exact tendsto_finsetSum Finset.univ (fun i _=>
    (continuousWithinAt_pi.mp (ha q hq) i).star.mul (continuousWithinAt_pi.mp (hb q hq) i))

theorem forward_continuousOn (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    ContinuousOn (fun q=>(ChannelPowers.forward (d.S q) (d.S0 q) (u q)).re) (disk d.r) := by
  exact real_pairing_continuousOn (disk d.r) _ _
    (d.background_continuousOn u hu) (d.output_continuousOn u hu)

theorem extinction_average (d:Design) (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk d.r)) :
    extinction d u hu=diskAverage d.r (fun q=>ChannelPowers.extinction (d.S q) (d.S0 q) (u q)) := by
  rw [extinction,beam_real_forward d u hu]
  rw [show (fun q=>ChannelPowers.extinction (d.S q) (d.S0 q) (u q))=
    (fun q=>2*(1-(ChannelPowers.forward (d.S q) (d.S0 q) (u q)).re)) by rfl]
  rw [average_const_mul,average_const_sub d.r d.hr 1 _ (forward_continuousOn d u hu)]

theorem left_beam_unit (d:Design) : ‖beam d.r (fun _=>left) continuousOn_const‖=1 := by
  have hs := beam_norm_sq d.r d.hr (fun _=>left) continuousOn_const
  simp only [BeamFibers.left_power] at hs
  have hc : diskAverage d.r (fun _:Transverse=>(1:ℝ))=1 := average_const volume (disk d.r) (disk_mass_pos d.hr) 1
  rw [hc] at hs
  nlinarith [norm_nonneg (beam d.r (fun _=>left) continuousOn_const)]

theorem reverse_beam_unit (d:Design) : ‖beam d.r d.reverseInput d.reverse_continuous.continuousOn‖=1 := by
  have hs := beam_norm_sq d.r d.hr d.reverseInput d.reverse_continuous.continuousOn
  have he : (fun q=>ChannelPowers.power (d.reverseInput q))=fun _:Transverse=>(1:ℝ) := by
    funext q
    exact (ChannelPowers.reverse_power _ (reference_unitary _ _ _) left).trans BeamFibers.left_power
  rw [he] at hs
  have hc : diskAverage d.r (fun _:Transverse=>(1:ℝ))=1 := average_const volume (disk d.r) (disk_mass_pos d.hr) 1
  rw [hc] at hs
  nlinarith [norm_nonneg (beam d.r d.reverseInput d.reverse_continuous.continuousOn)]

theorem left_extinction (d:Design) : extinction d (fun _=>left) continuousOn_const=
    diskAverage d.r (X d.k d.η d.h d.j d.t) := extinction_average d _ _

theorem absorption_difference (d:Design) :
    absorption d d.reverseInput d.reverse_continuous.continuousOn-
      absorption d (fun _=>left) continuousOn_const=diskAverage d.r (D d.k d.η d.h d.j d.t) := by
  rw [absorption_average,absorption_average]
  have hl : ContinuousOn (fun q=>ChannelPowers.absorption (d.S q) left) (disk d.r) :=
    continuousOn_const.sub (power_continuousOn d.r _ (d.output_continuousOn _ continuousOn_const))
  have hr : ContinuousOn (fun q=>ChannelPowers.absorption (d.S q) (d.reverseInput q)) (disk d.r) :=
    continuousOn_const.sub (power_continuousOn d.r _ (d.output_continuousOn _ d.reverse_continuous.continuousOn))
  rw [←average_sub d.r _ _ hr hl]
  rfl

theorem common_extinction (d:Design) :
    extinction d d.reverseInput d.reverse_continuous.continuousOn=extinction d (fun _=>left) continuousOn_const := by
  rw [extinction_average,extinction_average]
  unfold diskAverage BeamAveraging.average
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isCompact_closedBall (0:Transverse) d.r).measurableSet] with q hq
  have hκ : ObliqueVacuum.square (WithLp.ofLp q)<d.k^2 := by
    rw [square_ofLp]
    nlinarith [d.propagating hq,norm_nonneg q]
  exact ChannelPowers.extinction_reciprocity _ _
    (response_reciprocal d.k d.η d.h d.j _ d.t d.hk d.hη d.hh d.hj hκ)
    (reference_transpose _ _ _) (reference_unitary _ _ _) left

theorem corollary65_approach (k P Q X0 ε:ℝ) (hk:0<k) (hP:1<P) (hQ:0<Q)
    (hX0:0<X0) (hX4:X0<4) (hε:0<ε) :
    ∃ d:Design,d.k=k ∧ 0<d.η ∧ d.η≤Q ∧ 0<d.h ∧ OQ7Prescribed.plateDesignPermittivity d.j≤P ∧
      -1<d.t ∧ d.t<1 ∧
      ‖beam d.r (fun _=>left) continuousOn_const‖=1 ∧
      ‖beam d.r d.reverseInput d.reverse_continuous.continuousOn‖=1 ∧
      extinction d (fun _=>left) continuousOn_const=X0 ∧
      extinction d d.reverseInput d.reverse_continuous.continuousOn=X0 ∧
      X0-X0^2/4-ε≤|absorption d d.reverseInput d.reverse_continuous.continuousOn-
        absorption d (fun _=>left) continuousOn_const| := by
  obtain ⟨η,h,j,hη,hηQ,hh,hj,hcap,r,hr,hrk,t,ht0,ht1,hx,hd⟩ :=
    PhysicalBeamApproximation.capped_physical_approach k P Q X0 ε hk hP hQ hX0 hX4 hε
  let d : Design := ⟨k,η,h,r,t,j,hk,hη.le,hh.le,hr,hrk,hj⟩
  have he : extinction d (fun _=>left) continuousOn_const=X0 := (left_extinction d).trans hx
  refine ⟨d,rfl,hη,hηQ,hh,hcap,ht0,ht1,left_beam_unit d,reverse_beam_unit d,he,?_,?_⟩
  · exact (common_extinction d).trans he
  · rw [absorption_difference]
    exact hd.trans (le_abs_self _)

end GeneralizedResearch.PhysicalBeamL2
