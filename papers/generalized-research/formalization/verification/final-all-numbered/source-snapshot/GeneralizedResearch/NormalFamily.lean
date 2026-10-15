import GeneralizedResearch.ObliqueFamily

/-! Exact normal-incidence identification of the actual oblique material
transfer, including the absorbing scalar channel and the finite wave plate. -/
noncomputable section
namespace GeneralizedResearch.NormalFamily
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ObliqueFamily NormalTransfer ChannelAttainment
open OQ7Prescribed
open scoped Matrix Matrix.Norms.Operator ComplexOrder

def projection (t:ℝ) : CMat := ChannelAttainment.complexify (Matrix.vecMulVec (PlanarPlateBridge.principal t) (PlanarPlateBridge.principal t))
def H (t:ℝ) : CMat := ChannelAttainment.complexify (PlanarPlateBridge.H t)
def Px : CMat := ChannelAttainment.complexify xProjection
def scalarTransfer (k η h:ℝ) : OQ7.Mat2 := OQ7.layerTransfer k (dielectricSlab 1 η h)
def R (k η h:ℝ) : CMat := !![PlanarRealization.slabR k η h,0;0,0]
def T (k η h:ℝ) : CMat := !![PlanarRealization.slabT k η h,0;0,PlanarRealization.phase k h]

theorem projection_idempotent {t:ℝ} (ht0:-1≤t) (ht1:t≤1) : projection t*projection t=projection t := by
  have hu : PlanarPlateBridge.principal t ⬝ᵥ PlanarPlateBridge.principal t=1 := by
    simpa [PlanarPlateBridge.principal,dotProduct,Fin.sum_univ_two,pow_two] using
      (PlanarPlateBridge.coefficient_properties ht0 ht1).2.2.1
  rw [projection,←complexify_mul,Matrix.vecMulVec_mul_vecMulVec,hu,one_smul]

theorem Px_idempotent : Px*Px=Px := by
  rw [Px,←complexify_mul]
  congr 1
  ext i j;fin_cases i <;> fin_cases j <;> simp [xProjection,Matrix.mul_apply,Fin.sum_univ_two]

theorem H_projection {t:ℝ} (ht0:-1≤t) (ht1:t≤1) : H t=(2:ℂ) • projection t-1 := by
  have hc := PlanarPlateBridge.coefficient_complex ht0 ht1
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [H,projection,ChannelAttainment.complexify,PlanarPlateBridge.H,PlanarPlateBridge.principal,Matrix.vecMulVec_apply]
  · linear_combination (-1) * hc.1 - hc.2.1
  · linear_combination (-1) * hc.2.2
  · linear_combination (-1) * hc.2.2
  · linear_combination (-1) * hc.1 + hc.2.1

theorem H_square {t:ℝ} (ht0:-1≤t) (ht1:t≤1) : H t*H t=1 := by
  rw [H_projection ht0 ht1]
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_smul,
    projection_idempotent ht0 ht1,mul_one,one_mul]
  module

theorem normal_absorber (k η h:ℝ) :
    transfer k 0 1 (absorberLoss η) h=lift Px (scalarTransfer k η h) (OQ7.homogeneousTransfer k 1 h) := by
  let layer := dielectricSlab 1 η h
  have hn : OQ7.refractiveIndex layer≠0 := OQ7.refractiveIndex_ne_zero (by rfl)
  apply transfer_at_zero Px Px_idempotent k hn
  rw [OQ7.refractiveIndex_sq]
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [Px,ChannelAttainment.complexify,absorberLoss,xProjection,layer,dielectricSlab,OQ7.relativePermittivity,
      Matrix.smul_apply,smul_eq_mul] <;> ring

theorem normal_plate (k:ℝ) (hk:0<k) (j:ℕ) (hj:1≤j) {t:ℝ} (ht0:-1≤t) (ht1:t≤1) :
    transfer k 0 (PlanarPlateBridge.tensor j t) 0 (plateDesignThickness k j)=
      Matrix.fromBlocks (H t) 0 0 (H t) := by
  have hn : (plateDesignIndex j:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt ((by norm_num : (0:ℝ)<1).trans (plateDesignIndex_gt_one j hj)))
  have hε : ChannelAttainment.complexify (PlanarPlateBridge.tensor j t)+Complex.I • ChannelAttainment.complexify (0:RMat)=
      (plateDesignIndex j:ℂ)^2 • projection t+(1-projection t) := by
    ext i l;fin_cases i <;> fin_cases l <;>
      simp [PlanarPlateBridge.tensor,PlanarPlateBridge.susceptibility,projection,ChannelAttainment.complexify,
      plateDesignPermittivity,Matrix.smul_apply,smul_eq_mul]
    all_goals ring
  rw [transfer_at_zero (projection t) (projection_idempotent ht0 ht1) k hn _ _ hε,
    losslessPlateDesign_active_transfer k hk j hj,losslessPlateDesign_vacuum_transfer k hk j hj]
  ext i l
  rcases i with i|i <;> rcases l with l|l <;>
    simp [lift,Matrix.fromBlocks,H_projection ht0 ht1]
  all_goals ring

theorem vacuum_boundary (k h:ℝ) :
    OQ7.homogeneousTransfer k 1 h*OQ7.inputFieldStates 0 (PlanarRealization.phase k h)=
      OQ7.outputFieldStates 0 (PlanarRealization.phase k h) := by
  have hz : PlanarRealization.phase k h=Complex.cos ((k:ℂ)*(h:ℂ))+
      Complex.I*Complex.sin ((k:ℂ)*(h:ℂ)) := by
    simpa [PlanarRealization.phase,apertureOscillation,mul_comm] using
      Complex.exp_mul_I ((k:ℂ)*(h:ℂ))
  have ht := Complex.sin_sq_add_cos_sq ((k:ℂ)*(h:ℂ))
  ext i l;fin_cases i <;> fin_cases l <;>
    simp [OQ7.homogeneousTransfer,OQ7.inputFieldStates,OQ7.outputFieldStates,
      Matrix.mul_apply,Fin.sum_univ_two,hz]
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals first | (solve | ring) | (solve | linear_combination ht) | (solve | linear_combination (-1) * ht)

theorem scalar_boundary (k η h:ℝ) (hk:0<k) (hη:0≤η) (hh:0≤h) :
    scalarTransfer k η h*OQ7.inputFieldStates (PlanarRealization.slabR k η h) (PlanarRealization.slabT k η h)=
      OQ7.outputFieldStates (PlanarRealization.slabR k η h) (PlanarRealization.slabT k η h) := by
  have hpass := OQ7.layerTransfer_fluxDefect_posSemidef hk.le
    (layer:=dielectricSlab 1 η h) (by rfl) hη hh
  have hd := OQ7.passive_transfer_denominator_ne_zero _ hpass
  have hdet := OQ7.layerTransfer_det k (show OQ7.LayerAdmissible 1 η (dielectricSlab 1 η h) from
    ⟨le_rfl,le_rfl,hη,le_rfl,hh⟩)
  have hm := OQ7.field_transfer_boundary_states _ hd hdet
  rw [dielectricSlabReflection_both_sides] at hm
  exact hm

theorem absorber_boundary (k η h:ℝ) (hk:0<k) (hη:0≤η) (hh:0≤h) :
    transfer k 0 1 (absorberLoss η) h*
      Matrix.fromBlocks (1+R k η h) (T k η h) (1-R k η h) (-T k η h)=
      Matrix.fromBlocks (T k η h) (1+R k η h) (T k η h) (R k η h-1) := by
  have hs := scalar_boundary k η h hk hη hh
  have hv := vacuum_boundary k h
  have he := congrArg (fun M:OQ7.Mat2=>lift Px M
    (OQ7.homogeneousTransfer k 1 h*OQ7.inputFieldStates 0 (PlanarRealization.phase k h))) hs
  rw [←lift_mul Px Px_idempotent,←normal_absorber,hv] at he
  have hin : lift Px (OQ7.inputFieldStates (PlanarRealization.slabR k η h) (PlanarRealization.slabT k η h))
      (OQ7.inputFieldStates 0 (PlanarRealization.phase k h))=
      Matrix.fromBlocks (1+R k η h) (T k η h) (1-R k η h) (-T k η h) := by
    ext i l
    rcases i with i|i <;> rcases l with l|l <;> fin_cases i <;> fin_cases l <;>
      simp [lift,Px,ChannelAttainment.complexify,xProjection,R,T,OQ7.inputFieldStates,Matrix.fromBlocks]
  have hout : lift Px (OQ7.outputFieldStates (PlanarRealization.slabR k η h) (PlanarRealization.slabT k η h))
      (OQ7.outputFieldStates 0 (PlanarRealization.phase k h))=
      Matrix.fromBlocks (T k η h) (1+R k η h) (T k η h) (R k η h-1) := by
    ext i l
    rcases i with i|i <;> rcases l with l|l <;> fin_cases i <;> fin_cases l <;>
      simp [lift,Px,ChannelAttainment.complexify,xProjection,R,T,OQ7.outputFieldStates,Matrix.fromBlocks]
  rwa [hin,hout] at he

end GeneralizedResearch.NormalFamily
