import GeneralizedResearch.NormalScattering
import GeneralizedResearch.FourierMaxwell
import GeneralizedResearch.BeamAveraging

/-! Power-normalized physical fiber observables for the planar beam family.
The exact normal-incidence values are obtained from the actual oblique
transfer, and continuity holds in a fixed laboratory-axis ChannelPowers.power basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.BeamFibers
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ObliqueFamily NormalScattering ChannelPowers
open OQ7Prescribed
open scoped Matrix Matrix.Norms.Operator ComplexOrder

def swap : Mat4 := Matrix.fromBlocks 0 1 1 0
def phase (k d:ℝ) (κ:ObliqueVacuum.Transverse) : ℂ := apertureOscillation (longitudinal k κ) d
def reference (k d:ℝ) (κ:ObliqueVacuum.Transverse) : Mat4 := phase k d κ • swap
def left : Channel→ℂ := relabelVector PlanarFourPort.left
def right : Channel→ℂ := relabelVector PlanarFourPort.right
def X (k η h:ℝ) (j:ℕ) (t:ℝ) (q:BeamAveraging.Transverse) : ℝ :=
  ChannelPowers.extinction (response k η h j (WithLp.ofLp q) t)
    (reference k (h+plateDesignThickness k j) (WithLp.ofLp q)) left
def D (k η h:ℝ) (j:ℕ) (t:ℝ) (q:BeamAveraging.Transverse) : ℝ :=
  ChannelPowers.absorption (response k η h j (WithLp.ofLp q) t)
      (ChannelPowers.reverse (reference k (h+plateDesignThickness k j) (WithLp.ofLp q)) left)-
    ChannelPowers.absorption (response k η h j (WithLp.ofLp q) t) left

theorem phase_unitary (k d:ℝ) (κ:ObliqueVacuum.Transverse) : star (phase k d κ)*phase k d κ=1 := by
  have hn := apertureOscillation_norm (longitudinal k κ) d
  have hs : Complex.normSq (phase k d κ)=1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [phase,hn]
  calc
    _ = (Complex.normSq (phase k d κ):ℂ) := Complex.normSq_eq_conj_mul_self.symm
    _ = 1 := by rw [hs];rfl

theorem reference_transpose (k d:ℝ) (κ:ObliqueVacuum.Transverse) :
    (reference k d κ).transpose=reference k d κ := by
  simp [reference,swap,Matrix.transpose_smul,Matrix.fromBlocks_transpose]
theorem reference_unitary (k d:ℝ) (κ:ObliqueVacuum.Transverse) :
    (reference k d κ).conjTranspose*reference k d κ=1 := by
  have hs : swap.conjTranspose*swap=(1:Mat4) := by
    simp [swap,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
  have hp : phase k d κ*star (phase k d κ)=1 := by rw [mul_comm,phase_unitary]
  simp only [reference,Matrix.conjTranspose_smul,smul_mul_assoc,mul_smul_comm,smul_smul,
    hp,one_smul,hs]

theorem left_power : ChannelPowers.power left=1 := by rw [left,relabel_power,PlanarFourPort.left_unit]
theorem right_power : ChannelPowers.power right=1 := by rw [right,relabel_power,PlanarFourPort.right_unit]

theorem reverse_left (k d:ℝ) (κ:ObliqueVacuum.Transverse) :
    ChannelPowers.reverse (reference k d κ) left=star (phase k d κ) • right := by
  ext i;rcases i with i|i <;> fin_cases i <;>
    simp [ChannelPowers.reverse,reference,swap,left,right,relabelVector,index,finSumFinEquiv,
      PlanarFourPort.left,PlanarFourPort.right,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two]

theorem reference_zero (k h:ℝ) (hk:0<k) (j:ℕ) (hj:1≤j) :
    reference k (h+plateDesignThickness k j) 0=relabel (PlanarFourPort.reference (PlanarRealization.phase k h)) := by
  have he := PlanarRealization.reference_vacuum k h hk j hj
  rw [he]
  ext i l
  rcases i with i|i <;> rcases l with l|l <;> fin_cases i <;> fin_cases l <;>
    simp [reference,phase,(normal_coordinates hk).1,relabel,swap,index,finSumFinEquiv,Matrix.fromBlocks]

theorem normal_values (k η h:ℝ) (hk:0<k) (hη:0≤η) (hh:0≤h) (j:ℕ) (hj:1≤j)
    {t:ℝ} (ht0:-1≤t) (ht1:t≤1) :
    X k η h j t 0=2*(1-t) ∧
      D k η h j t 0=(1-t^2)*OQ7.absorptanceLeft (PlanarRealization.slabR k η h) (PlanarRealization.slabT k η h) := by
  simp only [X,D,WithLp.ofLp_zero,response_at_zero k η h j hk hη hh hj ht0 ht1,
    candidate_relabel,reference_zero k h hk j hj,left,relabel_reverse,relabel_absorption,
    ChannelPowers.extinction,relabel_forward]
  have hx := (PlanarRealization.physical_extinction_values k η h t).1
  have ha := PlanarRealization.physical_power_values k η h t ht0 ht1
  exact ⟨hx,by rw [ha.1,ha.2,sub_zero]⟩

theorem reference_continuous (k d:ℝ) : Continuous (reference k d) := by
  have hp : Continuous (phase k d) := by
    unfold phase apertureOscillation
    have hl := longitudinal_continuous k
    fun_prop
  exact hp.smul continuous_const

theorem square_ofLp (q:BeamAveraging.Transverse) : square (WithLp.ofLp q)=‖q‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜:=ℝ),EuclideanSpace.inner_eq_star_dotProduct]
  simp [square,dotProduct,Fin.sum_univ_two,pow_two]

theorem mulVec_continuousAt {Y:Type*} [TopologicalSpace Y] {p:Y}
    {M:Y→Mat4} {u:Y→Channel→ℂ} (hM:ContinuousAt M p) (hu:ContinuousAt u p) :
    ContinuousAt (fun y=>M y*ᵥu y) p := by
  apply continuousAt_pi.mpr;intro i
  exact tendsto_finsetSum Finset.univ (fun j _=>
    (continuousAt_pi.mp (continuousAt_pi.mp hM i) j).mul (continuousAt_pi.mp hu j))

theorem dot_continuousAt {Y:Type*} [TopologicalSpace Y] {p:Y}
    {u v:Y→Channel→ℂ} (hu:ContinuousAt u p) (hv:ContinuousAt v p) :
    ContinuousAt (fun y=>star (u y) ⬝ᵥ v y) p := by
  exact tendsto_finsetSum Finset.univ (fun i _=>
    (continuousAt_pi.mp hu i).star.mul (continuousAt_pi.mp hv i))

theorem power_continuousAt {Y:Type*} [TopologicalSpace Y] {p:Y}
    {u:Y→Channel→ℂ} (hu:ContinuousAt u p) : ContinuousAt (fun y=>ChannelPowers.power (u y)) p := by
  exact ContinuousAt.comp (f:=fun y=>star (u y) ⬝ᵥ u y)
    Complex.continuous_re.continuousAt (dot_continuousAt hu hu)

theorem continuousAt_values (k η h:ℝ) (j:ℕ) (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j)
    (p:ℝ×BeamAveraging.Transverse) (hq:‖p.2‖<k) :
    ContinuousAt (fun z:ℝ×BeamAveraging.Transverse=>X k η h j z.1 z.2) p ∧
      ContinuousAt (fun z:ℝ×BeamAveraging.Transverse=>D k η h j z.1 z.2) p := by
  have hκ : square (WithLp.ofLp p.2)<k^2 := by rw [square_ofLp];nlinarith [norm_nonneg p.2]
  have ho : Continuous (fun z:ℝ×BeamAveraging.Transverse=>(WithLp.ofLp z.2,z.1)) :=
    ((PiLp.continuous_ofLp 2 (fun _:Fin 2=>ℝ)).comp continuous_snd).prodMk continuous_fst
  have hs := ContinuousAt.comp (f:=fun z:ℝ×BeamAveraging.Transverse=>(WithLp.ofLp z.2,z.1))
    (ObliqueFamily.response_continuousAt j hk hη hh hj hκ) ho.continuousAt
  have hs0 : Continuous (fun z:ℝ×BeamAveraging.Transverse=>
      reference k (h+plateDesignThickness k j) (WithLp.ofLp z.2)) :=
    (reference_continuous _ _).comp ((PiLp.continuous_ofLp 2 (fun _:Fin 2=>ℝ)).comp continuous_snd)
  have hs0a := hs0.continuousAt (x:=p)
  have hleft : ContinuousAt (fun z:ℝ×BeamAveraging.Transverse=>left) p := continuousAt_const
  have hsu := mulVec_continuousAt hs hleft
  have h0u := mulVec_continuousAt hs0a hleft
  have hreverse : ContinuousAt (fun z:ℝ×BeamAveraging.Transverse=>
      ChannelPowers.reverse (reference k (h+plateDesignThickness k j) (WithLp.ofLp z.2)) left) p := by
    apply continuousAt_pi.mpr;intro i
    exact (continuousAt_pi.mp h0u i).star
  have hre : ContinuousAt (fun z:ℝ×BeamAveraging.Transverse=>
      (star (reference k (h+plateDesignThickness k j) (WithLp.ofLp z.2)*ᵥleft) ⬝ᵥ
        (response k η h j (WithLp.ofLp z.2) z.1*ᵥleft)).re) p := by
    exact ContinuousAt.comp (f:=fun z:ℝ×BeamAveraging.Transverse=>
      star (reference k (h+plateDesignThickness k j) (WithLp.ofLp z.2)*ᵥleft) ⬝ᵥ
        (response k η h j (WithLp.ofLp z.2) z.1*ᵥleft))
      Complex.continuous_re.continuousAt (dot_continuousAt h0u hsu)
  constructor
  · exact (continuousAt_const.sub hre).const_mul 2
  · exact (continuousAt_const.sub (power_continuousAt (mulVec_continuousAt hs hreverse))).sub
      (continuousAt_const.sub (power_continuousAt hsu))

end GeneralizedResearch.BeamFibers
