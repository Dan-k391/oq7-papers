import GeneralizedResearch.ObliqueMaxwell

/-! Laboratory-axis incoming/outgoing power coordinates.  The explicit
vacuum admittance square roots remain nonsingular at normal incidence. -/
noncomputable section
namespace GeneralizedResearch.ObliqueWaveBasis
open ObliqueVacuum ObliqueMaxwell ChannelAttainment
open scoped Matrix ComplexOrder

def U (k:ℝ) (κ:Transverse) : CMat := complexify (rootAdmittance k κ)
def V (k:ℝ) (κ:Transverse) : CMat := complexify (invRootAdmittance k κ)
def basis (k:ℝ) (κ:Transverse) : Mat4 := Matrix.fromBlocks (V k κ) (V k κ) (U k κ) (-U k κ)
def inverse (k:ℝ) (κ:Transverse) : Mat4 :=
  (1/2:ℂ) • Matrix.fromBlocks (U k κ) (V k κ) (U k κ) (-V k κ)
def powerFlux : Mat4 := Matrix.fromBlocks 1 0 0 (-1)

theorem U_mul_V {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) : U k κ*V k κ=1 := by
  rw [U,V,←complexify_mul,root_inverse hk hκ,complexify_one]
theorem V_mul_U {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) : V k κ*U k κ=1 := by
  rw [V,U,←complexify_mul,inverse_root hk hκ,complexify_one]
theorem U_transpose (k:ℝ) (κ:Transverse) : (U k κ).transpose=U k κ := by
  rw [U,complexify_transpose,rootAdmittance_transpose]
theorem V_transpose (k:ℝ) (κ:Transverse) : (V k κ).transpose=V k κ := by
  rw [V,complexify_transpose,invRootAdmittance_transpose]
theorem U_adjoint (k:ℝ) (κ:Transverse) : (U k κ).conjTranspose=U k κ := by
  rw [U,complexify_conjTranspose,rootAdmittance_transpose]
theorem V_adjoint (k:ℝ) (κ:Transverse) : (V k κ).conjTranspose=V k κ := by
  rw [V,complexify_conjTranspose,invRootAdmittance_transpose]

theorem inverse_basis {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) : inverse k κ*basis k κ=1 := by
  simp only [inverse,basis,smul_mul_assoc,Matrix.fromBlocks_multiply,mul_neg,neg_mul,
    U_mul_V hk hκ,V_mul_U hk hκ,neg_neg,add_neg_cancel,neg_add_cancel]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [Matrix.fromBlocks,Matrix.one_apply] <;> ring
theorem basis_inverse {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) : basis k κ*inverse k κ=1 :=
  mul_eq_one_comm.mp (inverse_basis hk hκ)

theorem basis_flux {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) :
    (basis k κ).conjTranspose*flux*basis k κ=(2:ℂ) • powerFlux := by
  simp only [basis,flux,powerFlux,Matrix.fromBlocks_conjTranspose,U_adjoint,V_adjoint,
    Matrix.conjTranspose_neg,Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,
    mul_one,one_mul,mul_neg,neg_mul,U_mul_V hk hκ,V_mul_U hk hκ,neg_neg,
    add_neg_cancel,neg_add_cancel,Matrix.fromBlocks_smul,smul_zero]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [Matrix.fromBlocks] <;> ring

theorem basis_symplectic {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2) :
    (basis k κ).transpose*symplectic*basis k κ=(-2:ℂ) • symplectic := by
  simp only [basis,symplectic,Matrix.fromBlocks_transpose,U_transpose,V_transpose,
    Matrix.transpose_neg,Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,
    mul_one,one_mul,mul_neg,neg_mul,U_mul_V hk hκ,V_mul_U hk hκ,neg_neg,
    add_neg_cancel,neg_add_cancel,Matrix.fromBlocks_smul,smul_zero]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [Matrix.fromBlocks] <;> ring

def waveTransfer (k:ℝ) (κ:Transverse) (F:Mat4) : Mat4 := inverse k κ*F*basis k κ

theorem waveTransfer_boundary {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2)
    (F:Mat4) (a:Channel→ℂ) :
    basis k κ*ᵥ(waveTransfer k κ F*ᵥa)=F*ᵥ(basis k κ*ᵥa) := by
  simp only [waveTransfer,Matrix.mulVec_mulVec,←mul_assoc,basis_inverse hk hκ,one_mul]

theorem waveTransfer_passive {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2)
    (F:Mat4) (hF:(flux-F.conjTranspose*flux*F).PosSemidef) :
    (powerFlux-(waveTransfer k κ F).conjTranspose*powerFlux*waveTransfer k κ F).PosSemidef := by
  have hp := hF.conjTranspose_mul_mul_same (basis k κ)
  have he : (basis k κ).conjTranspose*(flux-F.conjTranspose*flux*F)*basis k κ=
      (2:ℂ) • (powerFlux-(waveTransfer k κ F).conjTranspose*powerFlux*waveTransfer k κ F) := by
    have hb : F*basis k κ=basis k κ*waveTransfer k κ F := by
      simp only [waveTransfer,←mul_assoc,basis_inverse hk hκ,one_mul]
    have hg : (F*basis k κ).conjTranspose*flux*(F*basis k κ)=
        (waveTransfer k κ F).conjTranspose*((2:ℂ) • powerFlux)*waveTransfer k κ F := by
      calc
        _ = (waveTransfer k κ F).conjTranspose*
            ((basis k κ).conjTranspose*flux*basis k κ)*waveTransfer k κ F := by
          rw [hb]
          simp only [Matrix.conjTranspose_mul,mul_assoc]
        _ = _ := by rw [basis_flux hk hκ]
    calc
      _ = (basis k κ).conjTranspose*flux*basis k κ-
          (F*basis k κ).conjTranspose*flux*(F*basis k κ) := by
        simp [Matrix.conjTranspose_mul,mul_sub,sub_mul,mul_assoc]
      _ = _ := by rw [basis_flux hk hκ,hg];simp only [mul_smul_comm,smul_mul_assoc];module
  rw [he] at hp
  have hs := hp.smul (show 0≤(1/2:ℂ) by exact Complex.nonneg_iff.mpr ⟨by norm_num,by norm_num⟩)
  simpa [smul_smul] using hs

theorem waveTransfer_symplectic {k:ℝ} {κ:Transverse} (hk:0<k) (hκ:square κ<k^2)
    (F:Mat4) (hF:F.transpose*symplectic*F=symplectic) :
    (waveTransfer k κ F).transpose*symplectic*waveTransfer k κ F=symplectic := by
  have hb : F*basis k κ=basis k κ*waveTransfer k κ F := by
    simp only [waveTransfer,←mul_assoc,basis_inverse hk hκ,one_mul]
  have he : (-2:ℂ) • ((waveTransfer k κ F).transpose*symplectic*waveTransfer k κ F)=
      (-2:ℂ) • symplectic := by
    calc
      _ = (waveTransfer k κ F).transpose*
          ((basis k κ).transpose*symplectic*basis k κ)*waveTransfer k κ F := by
        rw [basis_symplectic hk hκ];simp only [mul_smul_comm,smul_mul_assoc]
      _ = (F*basis k κ).transpose*symplectic*(F*basis k κ) := by
        rw [hb];simp only [Matrix.transpose_mul,mul_assoc]
      _ = (basis k κ).transpose*(F.transpose*symplectic*F)*basis k κ := by
        simp only [Matrix.transpose_mul,mul_assoc]
      _ = _ := by rw [hF,basis_symplectic hk hκ]
  have hz := congrArg (fun M:Mat4=>(-1/2:ℂ) • M) he
  simpa only [smul_smul,show (-1/2:ℂ)*(-2)=1 by norm_num,one_smul] using hz

end GeneralizedResearch.ObliqueWaveBasis
