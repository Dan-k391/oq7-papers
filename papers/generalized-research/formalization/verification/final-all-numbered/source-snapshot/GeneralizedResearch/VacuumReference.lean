import GeneralizedResearch.BeamFibers

/-! The lossless reference is derived from actual oblique vacuum propagation,
including its full finite-width phase. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.VacuumReference
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis NormalTransfer ChannelAttainment
open OQ7Prescribed
open scoped Matrix Matrix.Norms.Operator ComplexOrder

def traveling (ℓ z:ℝ) : Mat4 := Matrix.fromBlocks
  (apertureOscillation ℓ z • (1:CMat)) 0 0 (apertureOscillation (-ℓ) z • (1:CMat))

theorem opposite_phase (ℓ z:ℝ) : apertureOscillation (-ℓ) z*apertureOscillation ℓ z=1 := by
  rw [apertureOscillation,apertureOscillation,←Complex.exp_add]
  have he : Complex.I*(((-ℓ)*z:ℝ):ℂ)+Complex.I*((ℓ*z:ℝ):ℂ)=0 := by push_cast;ring
  rw [he,Complex.exp_zero]

theorem generator_basis {k:ℝ} {κ:ObliqueVacuum.Transverse} (hk:0<k) (hκ:square κ<k^2) :
    generator k κ 1 0*basis k κ=basis k κ*((Complex.I*(longitudinal k κ:ℂ)) • powerFlux) := by
  have he : ChannelAttainment.complexify (electricBlock k κ)*U k κ=
      ((longitudinal k κ/k:ℝ):ℂ) • V k κ := by
    rw [U,V,←complexify_mul,vacuum_electric_modes hk hκ]
    ext i j;simp [ChannelAttainment.complexify,Matrix.smul_apply,smul_eq_mul]
  have hm : materialBlock k κ 1 0*V k κ=
      ((longitudinal k κ/k:ℝ):ℂ) • U k κ := by
    have hmb : materialBlock k κ 1 0=ChannelAttainment.complexify (magneticBlock k κ) := by
      ext i j;simp [materialBlock,realBlock,magneticBlock,ChannelAttainment.complexify]
    rw [hmb,V,U,←complexify_mul,vacuum_magnetic_modes hk hκ]
    ext i j;simp [ChannelAttainment.complexify,Matrix.smul_apply,smul_eq_mul]
  have hc : (Complex.I*(k:ℂ))*((longitudinal k κ/k:ℝ):ℂ)=Complex.I*(longitudinal k κ:ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hk.ne']
  simp only [generator,basis,powerFlux,smul_mul_assoc,mul_smul_comm,
    Matrix.fromBlocks_multiply,mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,
    mul_neg,neg_mul,he,hm,Matrix.fromBlocks_smul,smul_zero,smul_smul,hc]
  congr 1 <;> module

theorem traveling_initial (ℓ:ℝ) : traveling ℓ 0=1 := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [traveling,apertureOscillation,Matrix.fromBlocks,Matrix.one_apply]

theorem traveling_hasDerivAt (ℓ z:ℝ) :
    HasDerivAt (traveling ℓ) (((Complex.I*(ℓ:ℂ)) • powerFlux)*traveling ℓ z) z := by
  have hp := apertureOscillation_hasDerivAt ℓ z
  have hn := apertureOscillation_hasDerivAt (-ℓ) z
  have hm : ((Complex.I*(ℓ:ℂ)) • powerFlux)*traveling ℓ z=
      Matrix.fromBlocks ((Complex.I*(ℓ:ℂ)*apertureOscillation ℓ z) • (1:CMat)) 0 0
        ((-(Complex.I*(ℓ:ℂ))*apertureOscillation (-ℓ) z) • (1:CMat)) := by
    simp [traveling,powerFlux,smul_mul_assoc,Matrix.fromBlocks_multiply,Matrix.fromBlocks_smul,
      smul_smul,mul_comm]
  rw [hm]
  apply hasDerivAt_pi.mpr;intro i;apply hasDerivAt_pi.mpr;intro j
  rcases i with i|i <;> rcases j with j|j
  · convert hp.mul_const ((1:CMat) i j) using 1 <;>
      simp [traveling,powerFlux,Matrix.fromBlocks_multiply,Matrix.fromBlocks,Matrix.smul_apply,smul_eq_mul]
  · simpa [traveling,powerFlux,Matrix.fromBlocks_multiply,Matrix.fromBlocks] using hasDerivAt_const z (0:ℂ)
  · simpa [traveling,powerFlux,Matrix.fromBlocks_multiply,Matrix.fromBlocks] using hasDerivAt_const z (0:ℂ)
  · convert hn.mul_const ((1:CMat) i j) using 1 <;>
      simp [traveling,powerFlux,Matrix.fromBlocks_multiply,Matrix.fromBlocks,Matrix.smul_apply,smul_eq_mul]

theorem vacuum_waveTransfer {k:ℝ} {κ:ObliqueVacuum.Transverse} (hk:0<k) (hκ:square κ<k^2) (z:ℝ) :
    ObliqueWaveBasis.waveTransfer k κ (transfer k κ 1 0 z)=traveling (longitudinal k κ) z := by
  let F : ℝ→Mat4 := fun x=>basis k κ*traveling (longitudinal k κ) x*inverse k κ
  have hF : ∀x,HasDerivAt F (generator k κ 1 0*F x) x := by
    intro x
    have hp := ((traveling_hasDerivAt (longitudinal k κ) x).const_mul (basis k κ)).mul_const (inverse k κ)
    convert hp using 1
    · rfl
    · simp only [F,←mul_assoc,generator_basis hk hκ]
  have h0 : F 0=1 := by simp [F,traveling_initial,basis_inverse hk hκ]
  have he := solution_eq_exp (generator k κ 1 0) F h0 hF z
  change F z=transfer k κ 1 0 z at he
  rw [←he]
  simp only [ObliqueWaveBasis.waveTransfer,F,←mul_assoc,inverse_basis hk hκ,one_mul]
  rw [mul_assoc,inverse_basis hk hκ,mul_one]

theorem vacuum_scattering {k:ℝ} {κ:ObliqueVacuum.Transverse} (hk:0<k) (hκ:square κ<k^2)
    {d:ℝ} (hd:0≤d) :
    TransferScattering.scattering (ObliqueWaveBasis.waveTransfer k κ (transfer k κ 1 0 d))=
      BeamFibers.reference k d κ := by
  have hp := ObliqueWaveBasis.waveTransfer_passive hk hκ _
    (ObliqueMaxwell.transfer_passive k κ 1 0 hk.le (by simp) Matrix.PosSemidef.zero hd)
  apply TransferScattering.scattering_of_boundary
  · exact TransferScattering.D_isUnit _ hp
  · rw [vacuum_waveTransfer hk hκ]
    simp [traveling,TransferScattering.leftWaves,TransferScattering.rightWaves,
      BeamFibers.reference,BeamFibers.phase,BeamFibers.swap,Matrix.fromBlocks_smul,
      Matrix.fromBlocks_multiply,smul_smul]
    rw [mul_comm,opposite_phase,one_smul]

end GeneralizedResearch.VacuumReference
