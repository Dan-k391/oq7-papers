import GeneralizedResearch.NormalFamily

/-! Exact scattering of the actual oblique Maxwell family at normal
incidence. The original four-port normal response is recovered by solving
the same incoming/outgoing boundary equations, rather than assumed. -/
noncomputable section
namespace GeneralizedResearch.NormalScattering
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ObliqueFamily NormalFamily
open scoped Matrix Matrix.Norms.Operator ComplexOrder

def candidate (r q H:CMat) : Mat4 := Matrix.fromBlocks r (q*H) (H*q) (H*r*H)
def vacuumBasis : Mat4 := Matrix.fromBlocks 1 1 1 (-1)

theorem basis_zero {k:ℝ} (hk:0<k) : basis k 0=vacuumBasis := by
  simp only [basis,U,V,(normal_coordinates hk).2.1,(normal_coordinates hk).2.2,
    ChannelAttainment.complexify_one]
  rfl

theorem plate_boundary (F:Mat4) (r q H:CMat) (hH:H*H=1)
    (hF:F*Matrix.fromBlocks (1+r) q (1-r) (-q)=Matrix.fromBlocks q (1+r) q (r-1)) :
    (Matrix.fromBlocks H 0 0 H*F)*vacuumBasis*TransferScattering.leftWaves (candidate r q H)=
      vacuumBasis*TransferScattering.rightWaves (candidate r q H) := by
  let J : Mat4 := Matrix.fromBlocks 1 0 0 H
  have hL : vacuumBasis*TransferScattering.leftWaves (candidate r q H)=
      Matrix.fromBlocks (1+r) q (1-r) (-q)*J := by
    simp [vacuumBasis,TransferScattering.leftWaves,candidate,J,Matrix.fromBlocks_multiply,
      mul_add,mul_sub,sub_mul,add_mul,mul_assoc,sub_eq_add_neg]
  have hR : Matrix.fromBlocks H 0 0 H*Matrix.fromBlocks q (1+r) q (r-1)*J=
      vacuumBasis*TransferScattering.rightWaves (candidate r q H) := by
    simp [vacuumBasis,TransferScattering.rightWaves,candidate,J,Matrix.fromBlocks_multiply,
      mul_add,mul_sub,sub_mul,add_mul,mul_assoc,hH,sub_eq_add_neg,add_comm]
  calc
    _ = Matrix.fromBlocks H 0 0 H*(F*(vacuumBasis*TransferScattering.leftWaves (candidate r q H))) := by
      simp only [mul_assoc]
    _ = Matrix.fromBlocks H 0 0 H*(F*(Matrix.fromBlocks (1+r) q (1-r) (-q)*J)) := by rw [hL]
    _ = Matrix.fromBlocks H 0 0 H*(F*Matrix.fromBlocks (1+r) q (1-r) (-q))*J := by
      simp only [mul_assoc]
    _ = _ := by rw [hF,hR]

theorem field_boundary (k η h:ℝ) (j:ℕ) (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j)
    {t:ℝ} (ht0:-1≤t) (ht1:t≤1) :
    fieldTransfer k η h j 0 t*basis k 0*
      TransferScattering.leftWaves (candidate (R k η h) (T k η h) (H t))=
      basis k 0*TransferScattering.rightWaves (candidate (R k η h) (T k η h) (H t)) := by
  rw [fieldTransfer,normal_plate k hk j hj ht0 ht1,basis_zero hk]
  exact plate_boundary _ _ _ _ (H_square ht0 ht1) (absorber_boundary k η h hk hη hh)

theorem response_at_zero (k η h:ℝ) (j:ℕ) (hk:0<k) (hη:0≤η) (hh:0≤h) (hj:1≤j)
    {t:ℝ} (ht0:-1≤t) (ht1:t≤1) :
    response k η h j 0 t=candidate (R k η h) (T k η h) (H t) := by
  have hκ : square (0:Transverse)<k^2 := by simp [square];nlinarith
  apply TransferScattering.scattering_of_boundary
  · exact TransferScattering.D_isUnit _ (ObliqueFamily.waveTransfer_passive k η h j 0 t hk hη hh hj hκ)
  · have hf := field_boundary k η h j hk hη hh hj ht0 ht1
    change (inverse k 0*fieldTransfer k η h j 0 t*basis k 0)*_= _
    calc
      _ = inverse k 0*(fieldTransfer k η h j 0 t*basis k 0*
          TransferScattering.leftWaves (candidate (R k η h) (T k η h) (H t))) := by simp only [mul_assoc]
      _ = inverse k 0*(basis k 0*TransferScattering.rightWaves (candidate (R k η h) (T k η h) (H t))) := by rw [hf]
      _ = _ := by rw [←mul_assoc,inverse_basis hk hκ,one_mul]

def index : Channel≃Fin 4 := finSumFinEquiv

def relabel (M:PlanarFourPort.Mat4) : Mat4 := M.submatrix index index
def relabelVector (u:PlanarFourPort.Vec4) : Channel→ℂ := u ∘ index

theorem candidate_relabel (k η h t:ℝ) :
    candidate (R k η h) (T k η h) (H t)=relabel (PlanarRealization.response k η h t) := by
  rw [PlanarRealization.response,PlanarFourPort.scattering_formula]
  ext i l
  rcases i with i|i <;> rcases l with l|l <;> fin_cases i <;> fin_cases l <;>
    simp [candidate,relabel,R,T,H,ChannelAttainment.complexify,PlanarPlateBridge.H,
      Matrix.fromBlocks,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,index,finSumFinEquiv] <;> ring
  all_goals simp

theorem relabel_mulVec (M:PlanarFourPort.Mat4) (u:PlanarFourPort.Vec4) :
    relabel M*ᵥrelabelVector u=relabelVector (M*ᵥu) := by
  simpa [relabel,relabelVector,Function.comp_def] using
    Matrix.submatrix_mulVec_equiv M (u ∘ index) index index

theorem relabel_power (u:PlanarFourPort.Vec4) : ChannelPowers.power (relabelVector u)=ChannelPowers.power u := by
  unfold ChannelPowers.power
  congr 1

theorem relabel_absorption (M:PlanarFourPort.Mat4) (u:PlanarFourPort.Vec4) :
    ChannelPowers.absorption (relabel M) (relabelVector u)=ChannelPowers.absorption M u := by
  rw [ChannelPowers.absorption,relabel_mulVec,relabel_power]
  rfl

theorem relabel_forward (M M0:PlanarFourPort.Mat4) (u:PlanarFourPort.Vec4) :
    ChannelPowers.forward (relabel M) (relabel M0) (relabelVector u)=ChannelPowers.forward M M0 u := by
  simp only [ChannelPowers.forward,relabel_mulVec]
  exact (Equiv.sum_comp index (fun i:Fin 4=>star ((M0*ᵥu) i)*(M*ᵥu) i)).symm

theorem relabel_reverse (M0:PlanarFourPort.Mat4) (u:PlanarFourPort.Vec4) :
    ChannelPowers.reverse (relabel M0) (relabelVector u)=relabelVector (ChannelPowers.reverse M0 u) := by
  simp only [ChannelPowers.reverse,relabel_mulVec]
  rfl

end GeneralizedResearch.NormalScattering
