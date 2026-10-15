import GeneralizedResearch.PhysicalFourierIntegral
import GeneralizedResearch.BeamPackets
import GeneralizedResearch.FiniteHilbertBridge

/-! Parseval's identity in the actual laboratory-axis admittance power
coordinates. The spatial electric/magnetic cross flux is proved to equal
the channel power and forward pairing used in the beam theorem. -/
noncomputable section
namespace GeneralizedResearch.BeamFlux
open MeasureTheory Set BeamAveraging BeamPackets
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis
open scoped Matrix Matrix.Norms.Operator Topology
abbrev Transverse := BeamAveraging.Transverse
abbrev Fiber := EuclideanSpace ℂ Channel

def electricMatrix (k:ℝ) (q:Transverse) : Mat4 :=
  Matrix.fromBlocks (V k (WithLp.ofLp q)) 0 0 (V k (WithLp.ofLp q))
def magneticMatrix (k:ℝ) (q:Transverse) : Mat4 :=
  Matrix.fromBlocks (U k (WithLp.ofLp q)) 0 0 (U k (WithLp.ofLp q))
def electric (k:ℝ) (q:Transverse) (u:Channel→ℂ) : Fiber :=
  FiniteHilbertBridge.vector (electricMatrix k q*ᵥu)
def magnetic (k:ℝ) (q:Transverse) (u:Channel→ℂ) : Fiber :=
  FiniteHilbertBridge.vector (magneticMatrix k q*ᵥu)

theorem cross_identity {k:ℝ} {q:Transverse} (hk:0<k) (hq:‖q‖<k) :
    (electricMatrix k q).conjTranspose*magneticMatrix k q=1 := by
  have hκ : square (WithLp.ofLp q)<k^2 := by rw [BeamFibers.square_ofLp];nlinarith [norm_nonneg q]
  simp [electricMatrix,magneticMatrix,Matrix.fromBlocks_conjTranspose,
    V_adjoint,Matrix.fromBlocks_multiply,V_mul_U hk hκ]

theorem cross_inner {k:ℝ} {q:Transverse} (hk:0<k) (hq:‖q‖<k) (u v:Channel→ℂ) :
    inner ℂ (electric k q u) (magnetic k q v)=
      inner ℂ (FiniteHilbertBridge.vector u) (FiniteHilbertBridge.vector v) := by
  simp only [electric,magnetic,FiniteHilbertBridge.inner_vector]
  calc
    _ = star u ⬝ᵥ (((electricMatrix k q).conjTranspose*magneticMatrix k q)*ᵥv) := by
      simp only [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
    _ = _ := by rw [cross_identity hk hq,Matrix.one_mulVec]

theorem matrix_continuousOn (k r:ℝ) (hk:0<k) (hrk:r<k) :
    ContinuousOn (electricMatrix k) (disk r) ∧ ContinuousOn (magneticMatrix k) (disk r) := by
  have hb (q:Transverse) (hq:q∈disk r) : ContinuousAt (fun p:Transverse=>basis k (WithLp.ofLp p)) q := by
    have hn : ‖q‖≤r := by simpa [disk,Metric.mem_closedBall,dist_zero_right] using hq
    have hκ : square (WithLp.ofLp q)<k^2 := by rw [BeamFibers.square_ofLp];nlinarith [norm_nonneg q]
    exact ContinuousAt.comp (f:=WithLp.ofLp) (ObliqueFamily.basis_continuousAt hk hκ).1
      (PiLp.continuous_ofLp 2 (fun _:Fin 2=>ℝ)).continuousAt
  constructor <;> intro q hq <;> apply ContinuousAt.continuousWithinAt
  all_goals apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro j
  all_goals rcases i with i|i <;> rcases j with j|j
  · exact continuousAt_pi.mp (continuousAt_pi.mp (hb q hq) (Sum.inl i)) (Sum.inl j)
  · exact continuousAt_const
  · exact continuousAt_const
  · exact continuousAt_pi.mp (continuousAt_pi.mp (hb q hq) (Sum.inl i)) (Sum.inl j)
  · exact continuousAt_pi.mp (continuousAt_pi.mp (hb q hq) (Sum.inr i)) (Sum.inl j)
  · exact continuousAt_const
  · exact continuousAt_const
  · exact continuousAt_pi.mp (continuousAt_pi.mp (hb q hq) (Sum.inr i)) (Sum.inl j)

theorem mulVec_continuousOn (r:ℝ) (M:Transverse→Mat4) (u:Transverse→Channel→ℂ)
    (hM:ContinuousOn M (disk r)) (hu:ContinuousOn u (disk r)) :
    ContinuousOn (fun q=>M q*ᵥu q) (disk r) := by
  intro q hq
  apply continuousWithinAt_pi.mpr;intro i
  exact tendsto_finsetSum Finset.univ (fun j _=>
    (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp (hM q hq) i) j).mul
      (continuousWithinAt_pi.mp (hu q hq) j))

theorem field_continuousOn (k r:ℝ) (hk:0<k) (hrk:r<k)
    (u:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) :
    ContinuousOn (fun q=>electric k q (u q)) (disk r) ∧
      ContinuousOn (fun q=>magnetic k q (u q)) (disk r) := by
  have hm := matrix_continuousOn k r hk hrk
  have hv : Continuous (FiniteHilbertBridge.vector (n:=Channel)) := PiLp.continuous_toLp 2 (fun _:Channel=>ℂ)
  exact ⟨hv.comp_continuousOn (mulVec_continuousOn r _ u hm.1 hu),
    hv.comp_continuousOn (mulVec_continuousOn r _ u hm.2 hu)⟩

/-- The real spatial E/H pairing is the normalized oriented Poynting flux.
Both sides use actual inverse Fourier transforms of the admittance fields. -/
theorem spatial_flux (k r:ℝ) (hk:0<k) (hr:0<r) (hrk:r<k)
    (u v:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) (hv:ContinuousOn v (disk r)) :
    let hE := packet_memLp r _ (field_continuousOn k r hk hrk u hu).1
    let hH := packet_memLp r _ (field_continuousOn k r hk hrk v hv).2
    (inner ℂ (PhysicalFourier.inverse (hE.toLp (packet r (fun q=>electric k q (u q)))))
      (PhysicalFourier.inverse (hH.toLp (packet r (fun q=>magnetic k q (v q)))))).re=
      diskAverage r (fun q=>(inner ℂ (FiniteHilbertBridge.vector (u q))
        (FiniteHilbertBridge.vector (v q))).re) := by
  dsimp only
  rw [PhysicalFourier.inverse_inner,packet_real_inner r hr]
  unfold diskAverage BeamAveraging.average
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isCompact_closedBall (0:Transverse) r).measurableSet] with q hq
  have hn : ‖q‖≤r := by simpa [Metric.mem_closedBall,dist_zero_right] using hq
  rw [cross_inner hk (hn.trans_lt hrk)]


theorem time_average_normalization {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e h:E) :
    (1/2:ℝ)*(inner ℂ ((Real.sqrt 2:ℂ) • e) ((Real.sqrt 2:ℂ) • h)).re=(inner ℂ e h).re := by
  rw [inner_smul_left,inner_smul_right]
  have hc : (Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ)=2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  rw [Complex.conj_ofReal,←mul_assoc,hc]
  simp [Complex.mul_re]

theorem physical_spatial_flux (k r:ℝ) (hk:0<k) (hr:0<r) (hrk:r<k)
    (u v:Transverse→Channel→ℂ) (hu:ContinuousOn u (disk r)) (hv:ContinuousOn v (disk r)) :
    let hE := packet_memLp r _ (field_continuousOn k r hk hrk u hu).1
    let hH := packet_memLp r _ (field_continuousOn k r hk hrk v hv).2
    (1/2:ℝ)*(inner ℂ ((Real.sqrt 2:ℂ) • PhysicalFourier.inverse (hE.toLp (packet r (fun q=>electric k q (u q)))))
      ((Real.sqrt 2:ℂ) • PhysicalFourier.inverse (hH.toLp (packet r (fun q=>magnetic k q (v q)))))).re=
      diskAverage r (fun q=>(inner ℂ (FiniteHilbertBridge.vector (u q))
        (FiniteHilbertBridge.vector (v q))).re) := by
  dsimp only
  rw [time_average_normalization]
  exact spatial_flux k r hk hr hrk u v hu hv

end GeneralizedResearch.BeamFlux
