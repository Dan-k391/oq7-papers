import GeneralizedResearch.TransferScattering
import GeneralizedResearch.NormalTransfer
import GeneralizedResearch.PlanarRealization

/-! Actual oblique two-layer material family, solved by its Maxwell transfer.
All inverses, passivity and reciprocal scattering properties are derived. -/
noncomputable section
namespace GeneralizedResearch.ObliqueFamily
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ChannelAttainment
open scoped Matrix Matrix.Norms.Operator ComplexOrder

def xProjection : RMat := !![1,0;0,0]
def absorberLoss (η:ℝ) : RMat := η • xProjection
def fieldTransfer (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ) : Mat4 :=
  transfer k κ (PlanarPlateBridge.tensor j t) 0 (OQ7Prescribed.plateDesignThickness k j)*
    transfer k κ 1 (absorberLoss η) h
def waveTransfer (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ) : Mat4 :=
  ObliqueWaveBasis.waveTransfer k κ (fieldTransfer k η h j κ t)
def response (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ) : Mat4 :=
  TransferScattering.scattering (waveTransfer k η h j κ t)

theorem xProjection_posSemidef : xProjection.PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (![1,0]:Fin 2→ℝ) using 1
  ext i l;fin_cases i <;> fin_cases l <;> norm_num [xProjection,Matrix.vecMulVec_apply]
theorem absorberLoss_posSemidef {η:ℝ} (hη:0≤η) : (absorberLoss η).PosSemidef :=
  xProjection_posSemidef.smul hη
theorem absorberLoss_transpose (η:ℝ) : (absorberLoss η).transpose=absorberLoss η := by
  ext i l;fin_cases i <;> fin_cases l <;> simp [absorberLoss,xProjection]

theorem transfer_product_passive (F G:Mat4) (hF:(flux-F.conjTranspose*flux*F).PosSemidef)
    (hG:(flux-G.conjTranspose*flux*G).PosSemidef) :
    (flux-(G*F).conjTranspose*flux*(G*F)).PosSemidef := by
  have hs := hF.add (hG.conjTranspose_mul_mul_same F)
  have he : flux-(G*F).conjTranspose*flux*(G*F)=
      (flux-F.conjTranspose*flux*F)+F.conjTranspose*(flux-G.conjTranspose*flux*G)*F := by
    simp only [Matrix.conjTranspose_mul,mul_sub,sub_mul,mul_assoc]
    abel
  rwa [he]

theorem transfer_product_symplectic (F G:Mat4) (hF:F.transpose*symplectic*F=symplectic)
    (hG:G.transpose*symplectic*G=symplectic) :
    (G*F).transpose*symplectic*(G*F)=symplectic := by
  calc
    _ = F.transpose*(G.transpose*symplectic*G)*F := by simp [Matrix.transpose_mul,mul_assoc]
    _ = _ := by rw [hG,hF]

theorem fieldTransfer_passive (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ)
    (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j) :
    (flux-(fieldTransfer k η h j κ t).conjTranspose*flux*fieldTransfer k η h j κ t).PosSemidef := by
  apply transfer_product_passive
  · exact ObliqueMaxwell.transfer_passive k κ 1 (absorberLoss η) hk.le
      (by simp) (absorberLoss_posSemidef hη) hh
  · exact ObliqueMaxwell.transfer_passive k κ _ 0 hk.le
      (PlanarPlateBridge.tensor_symmetric j t) Matrix.PosSemidef.zero
      (OQ7Prescribed.plateDesignThickness_pos k hk j hj).le

theorem fieldTransfer_symplectic (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ) :
    (fieldTransfer k η h j κ t).transpose*symplectic*fieldTransfer k η h j κ t=symplectic := by
  apply transfer_product_symplectic
  · exact ObliqueMaxwell.transfer_symplectic k κ 1 (absorberLoss η) (by simp) (absorberLoss_transpose η) h
  · exact ObliqueMaxwell.transfer_symplectic k κ _ 0 (PlanarPlateBridge.tensor_symmetric j t) (by simp) _

theorem waveTransfer_passive (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ)
    (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j) (hκ:square κ<k^2) :
    (powerFlux-(waveTransfer k η h j κ t).conjTranspose*powerFlux*waveTransfer k η h j κ t).PosSemidef :=
  ObliqueWaveBasis.waveTransfer_passive hk hκ _ (fieldTransfer_passive k η h j κ t hk hη hh hj)

theorem response_passive (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ)
    (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j) (hκ:square κ<k^2) :
    (1-(response k η h j κ t).conjTranspose*response k η h j κ t).PosSemidef :=
  TransferScattering.scattering_passive _ (waveTransfer_passive k η h j κ t hk hη hh hj hκ)

theorem response_reciprocal (k η h:ℝ) (j:ℕ) (κ:Transverse) (t:ℝ)
    (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j) (hκ:square κ<k^2) :
    (response k η h j κ t).transpose=response k η h j κ t := by
  apply TransferScattering.scattering_reciprocal
  · exact TransferScattering.D_isUnit _ (waveTransfer_passive k η h j κ t hk hη hh hj hκ)
  · exact ObliqueWaveBasis.waveTransfer_symplectic hk hκ _ (fieldTransfer_symplectic k η h j κ t)

theorem tensor_continuous (j:ℕ) : Continuous (PlanarPlateBridge.tensor j) := by
  apply continuous_pi;intro i;apply continuous_pi;intro l
  simp only [PlanarPlateBridge.tensor,PlanarPlateBridge.susceptibility,Matrix.add_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,PlanarPlateBridge.principal]
  fin_cases i <;> fin_cases l <;>
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      PlanarPlateBridge.coeffU,PlanarPlateBridge.coeffV]
  all_goals fun_prop

theorem fieldTransfer_continuous (k η h:ℝ) (j:ℕ) :
    Continuous (fun p:Transverse×ℝ=>fieldTransfer k η h j p.1 p.2) := by
  exact (ObliqueMaxwell.transfer_continuous k _ _ (fun _=>0) (tensor_continuous j) continuous_const).mul
    (ObliqueMaxwell.transfer_continuous k h (fun _=>1) (fun _=>absorberLoss η) continuous_const continuous_const)

theorem basis_continuousAt {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) :
    ContinuousAt (basis k) κ ∧ ContinuousAt (inverse k) κ := by
  have ho : IsOpen {q:Transverse|square q<k^2} := isOpen_lt square_continuous continuous_const
  have hu := (rootAdmittance_continuousOn hk).continuousAt (ho.mem_nhds hκ)
  have hv := (invRootAdmittance_continuousOn hk).continuousAt (ho.mem_nhds hκ)
  have hU : ContinuousAt (U k) κ := by
    apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro l
    exact Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_pi.mp (continuousAt_pi.mp hu i) l)
  have hV : ContinuousAt (V k) κ := by
    apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro l
    exact Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_pi.mp (continuousAt_pi.mp hv i) l)
  constructor
  · apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro l
    rcases i with i|i <;> rcases l with l|l
    · exact continuousAt_pi.mp (continuousAt_pi.mp hV i) l
    · exact continuousAt_pi.mp (continuousAt_pi.mp hV i) l
    · exact continuousAt_pi.mp (continuousAt_pi.mp hU i) l
    · exact (continuousAt_pi.mp (continuousAt_pi.mp hU i) l).neg
  · apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro l
    rcases i with i|i <;> rcases l with l|l
    all_goals
      first
      | exact (continuousAt_pi.mp (continuousAt_pi.mp hU i) l).const_mul (1/2:ℂ)
      | exact (continuousAt_pi.mp (continuousAt_pi.mp hV i) l).const_mul (1/2:ℂ)
      | exact (continuousAt_pi.mp (continuousAt_pi.mp hV i) l).neg.const_mul (1/2:ℂ)

theorem waveTransfer_continuousAt {k η h:ℝ} (j:ℕ) {p:Transverse×ℝ}
    (hk:0<k) (hκ:square p.1<k^2) :
    ContinuousAt (fun q:Transverse×ℝ=>waveTransfer k η h j q.1 q.2) p := by
  have hb := basis_continuousAt hk hκ
  exact ((hb.2.comp continuous_fst.continuousAt).mul (fieldTransfer_continuous k η h j).continuousAt).mul
    (hb.1.comp continuous_fst.continuousAt)

theorem response_continuousAt {k η h:ℝ} (j:ℕ) {p:Transverse×ℝ}
    (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j) (hκ:square p.1<k^2) :
    ContinuousAt (fun q:Transverse×ℝ=>response k η h j q.1 q.2) p :=
  TransferScattering.scattering_continuousAt (waveTransfer_continuousAt j hk hκ)
    (TransferScattering.D_isUnit _ (waveTransfer_passive k η h j p.1 p.2 hk hη hh hj hκ))

end GeneralizedResearch.ObliqueFamily
