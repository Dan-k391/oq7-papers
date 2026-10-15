import GeneralizedResearch.PlanarPlateBridge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! Nonsingular laboratory-axis vacuum power coordinates at oblique incidence.
The square-root admittance matrices have explicit formulas continuous through
normal incidence; no azimuth-dependent TE/TM frame is selected. -/

noncomputable section
namespace GeneralizedResearch.ObliqueVacuum
open scoped Matrix
abbrev RMat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Transverse := Fin 2→ℝ
def square (κ:Transverse) : ℝ := κ 0^2+κ 1^2
def radial (κ:Transverse) : RMat := Matrix.vecMulVec κ κ
def perpendicular (κ:Transverse) : Transverse := ![-κ 1,κ 0]
def longitudinal (k:ℝ) (κ:Transverse) : ℝ := Real.sqrt (k^2-square κ)
def root (k:ℝ) (κ:Transverse) : ℝ := Real.sqrt (longitudinal k κ/k)
def coefficient (k:ℝ) (κ:Transverse) : ℝ := 1/(k*root k κ*(k+longitudinal k κ))
def admittance (k:ℝ) (κ:Transverse) : RMat :=
  (longitudinal k κ/k) • 1+(1/(k*longitudinal k κ)) • radial κ
def rootAdmittance (k:ℝ) (κ:Transverse) : RMat := root k κ • 1+coefficient k κ • radial κ
def invRootAdmittance (k:ℝ) (κ:Transverse) : RMat := (1/root k κ) • 1-coefficient k κ • radial κ
def electricBlock (k:ℝ) (κ:Transverse) : RMat := 1-(1/k^2) • radial κ
def magneticBlock (k:ℝ) (κ:Transverse) : RMat := 1-(1/k^2) • radial (perpendicular κ)

theorem radial_square (κ:Transverse) : radial κ*radial κ=square κ • radial κ := by
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [radial,square,Matrix.mul_apply,Matrix.vecMulVec_apply,Fin.sum_univ_two] <;> ring
theorem radial_transpose (κ:Transverse) : (radial κ).transpose=radial κ := by
  ext i j
  simp [radial,Matrix.transpose_apply,Matrix.vecMulVec_apply,mul_comm]
theorem perpendicular_radial (κ:Transverse) : radial (perpendicular κ)=square κ • 1-radial κ := by
  ext i j;fin_cases i <;> fin_cases j <;> simp [radial,perpendicular,square,Matrix.vecMulVec_apply] <;> ring
theorem square_nonneg (κ:Transverse) : 0≤square κ := add_nonneg (sq_nonneg _) (sq_nonneg _)

variable {k:ℝ} {κ:Transverse}
theorem longitudinal_pos (_hk:0<k) (hκ:square κ<k^2) : 0<longitudinal k κ :=
  Real.sqrt_pos.mpr (sub_pos.mpr hκ)
theorem longitudinal_sq (hκ:square κ≤k^2) : (longitudinal k κ)^2+square κ=k^2 := by
  rw [longitudinal,Real.sq_sqrt (sub_nonneg.mpr hκ)]
  ring
theorem root_pos (hk:0<k) (hκ:square κ<k^2) : 0<root k κ :=
  Real.sqrt_pos.mpr (div_pos (longitudinal_pos hk hκ) hk)
theorem root_sq (hk:0<k) (hκ:square κ<k^2) : k*(root k κ)^2=longitudinal k κ := by
  rw [root,Real.sq_sqrt (div_nonneg (longitudinal_pos hk hκ).le hk.le)]
  field_simp

theorem coefficient_radial (hk:0<k) (hκ:square κ<k^2) :
    coefficient k κ*square κ=(1-(root k κ)^2)/root k κ := by
  have hz := longitudinal_pos hk hκ
  have ha := root_pos hk hκ
  have hsum : k+longitudinal k κ≠0 := ne_of_gt (add_pos hk hz)
  have hZ := longitudinal_sq hκ.le
  have hA := root_sq hk hκ
  unfold coefficient
  field_simp [hk.ne',ha.ne',hsum]
  linear_combination hZ+(k+longitudinal k κ)*hA

theorem inverse_coefficient (hk:0<k) (hκ:square κ<k^2) :
    -(root k κ*coefficient k κ)+coefficient k κ/root k κ-
      coefficient k κ^2*square κ=0 := by
  have ha := root_pos hk hκ
  rw [show coefficient k κ^2*square κ=coefficient k κ*(coefficient k κ*square κ) by ring,
    coefficient_radial hk hκ]
  field_simp [ha.ne']
  ring

theorem square_coefficient (hk:0<k) (hκ:square κ<k^2) :
    2*root k κ*coefficient k κ+coefficient k κ^2*square κ=1/(k*longitudinal k κ) := by
  have hz := longitudinal_pos hk hκ
  have ha := root_pos hk hκ
  have hsum : k+longitudinal k κ≠0 := ne_of_gt (add_pos hk hz)
  have hA := root_sq hk hκ
  rw [show coefficient k κ^2*square κ=coefficient k κ*(coefficient k κ*square κ) by ring,
    coefficient_radial hk hκ]
  unfold coefficient
  field_simp [hk.ne',hz.ne',ha.ne',hsum]
  linear_combination -hA

theorem root_inverse (hk:0<k) (hκ:square κ<k^2) :
    rootAdmittance k κ*invRootAdmittance k κ=1 := by
  have ha := root_pos hk hκ
  have he : rootAdmittance k κ*invRootAdmittance k κ=
      (root k κ/root k κ) • (1:RMat)+
        (-(root k κ*coefficient k κ)+coefficient k κ/root k κ-coefficient k κ^2*square κ) • radial κ := by
    simp only [rootAdmittance,invRootAdmittance,add_mul,mul_sub,
      smul_mul_assoc,mul_smul_comm,smul_smul,one_mul,mul_one,radial_square]
    module
  rw [he,inverse_coefficient hk hκ,div_self ha.ne',one_smul,zero_smul,add_zero]

theorem inverse_root (hk:0<k) (hκ:square κ<k^2) :
    invRootAdmittance k κ*rootAdmittance k κ=1 := mul_eq_one_comm.mp (root_inverse hk hκ)

theorem root_square (hk:0<k) (hκ:square κ<k^2) :
    rootAdmittance k κ*rootAdmittance k κ=admittance k κ := by
  have ha : (root k κ)^2=longitudinal k κ/k := by
    exact (eq_div_iff hk.ne').mpr (by simpa only [mul_comm] using root_sq hk hκ)
  have he : rootAdmittance k κ*rootAdmittance k κ=
      (root k κ)^2 • (1:RMat)+
        (2*root k κ*coefficient k κ+coefficient k κ^2*square κ) • radial κ := by
    simp only [rootAdmittance,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      smul_smul,one_mul,mul_one,radial_square]
    module
  rw [he,ha,square_coefficient hk hκ]
  rfl

theorem admittance_inverse_root (hk:0<k) (hκ:square κ<k^2) :
    admittance k κ*invRootAdmittance k κ=rootAdmittance k κ := by
  rw [← root_square hk hκ,mul_assoc,root_inverse hk hκ,mul_one]

theorem electric_admittance (hk:0<k) (hκ:square κ<k^2) :
    electricBlock k κ*admittance k κ=(longitudinal k κ/k) • (1:RMat) := by
  have hz := longitudinal_pos hk hκ
  have hZ := longitudinal_sq hκ.le
  have hc : 1/(k*longitudinal k κ)-(longitudinal k κ/k)/k^2-
      square κ/(k^2*(k*longitudinal k κ))=0 := by
    field_simp [hk.ne',hz.ne']
    linear_combination -hZ
  have he : electricBlock k κ*admittance k κ=
      (longitudinal k κ/k) • (1:RMat)+
        (1/(k*longitudinal k κ)-(longitudinal k κ/k)/k^2-
          square κ/(k^2*(k*longitudinal k κ))) • radial κ := by
    simp only [electricBlock,admittance,sub_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      smul_smul,one_mul,mul_one,radial_square]
    module
  rw [he,hc,zero_smul,add_zero]

theorem magnetic_admittance (hk:0<k) (hκ:square κ<k^2) :
    magneticBlock k κ=(longitudinal k κ/k) • admittance k κ := by
  have hz := longitudinal_pos hk hκ
  have hZ := longitudinal_sq hκ.le
  have h0 : 1-square κ/k^2=(longitudinal k κ/k)^2 := by
    field_simp [hk.ne']
    linear_combination -hZ
  have h1 : 1/k^2=(longitudinal k κ/k)*(1/(k*longitudinal k κ)) := by
    field_simp [hk.ne',hz.ne']
  have he : magneticBlock k κ=(1-square κ/k^2) • (1:RMat)+(1/k^2) • radial κ := by
    rw [magneticBlock,perpendicular_radial,smul_sub,smul_smul]
    module
  rw [he,h0,admittance,smul_add,smul_smul,smul_smul]
  rw [← h1,pow_two]

theorem vacuum_electric_modes (hk:0<k) (hκ:square κ<k^2) :
    electricBlock k κ*rootAdmittance k κ=(longitudinal k κ/k) • invRootAdmittance k κ := by
  have h := congrArg (fun A:RMat=>A*invRootAdmittance k κ) (electric_admittance hk hκ)
  simpa only [mul_assoc,admittance_inverse_root hk hκ,smul_mul_assoc,one_mul] using h
theorem vacuum_magnetic_modes (hk:0<k) (hκ:square κ<k^2) :
    magneticBlock k κ*invRootAdmittance k κ=(longitudinal k κ/k) • rootAdmittance k κ := by
  rw [magnetic_admittance hk hκ,smul_mul_assoc,admittance_inverse_root hk hκ]

theorem normal_coordinates (hk:0<k) :
    longitudinal k (0:Transverse)=k ∧ rootAdmittance k 0=1 ∧ invRootAdmittance k 0=1 := by
  have hz : longitudinal k (0:Transverse)=k := by simp [longitudinal,square,Real.sqrt_sq hk.le]
  have ha : root k (0:Transverse)=1 := by simp [root,hz,hk.ne']
  exact ⟨hz,by simp [rootAdmittance,ha,radial],by simp [invRootAdmittance,ha,radial]⟩

theorem square_continuous : Continuous square := by unfold square;fun_prop
theorem radial_continuous : Continuous radial := by
  apply continuous_pi;intro i;apply continuous_pi;intro j
  simp only [radial,Matrix.vecMulVec_apply]
  fun_prop
theorem longitudinal_continuous (k:ℝ) : Continuous (longitudinal k) := by
  unfold longitudinal
  exact (continuous_const.sub square_continuous).sqrt
theorem root_continuous (k:ℝ) : Continuous (root k) :=
  ((longitudinal_continuous k).div_const k).sqrt
theorem coefficient_continuousOn (hk:0<k) :
    ContinuousOn (coefficient k) {κ:Transverse|square κ<k^2} := by
  have hd : Continuous (fun κ:Transverse=>k*root k κ*(k+longitudinal k κ)) :=
    (continuous_const.mul (root_continuous k)).mul (continuous_const.add (longitudinal_continuous k))
  exact continuousOn_const.div hd.continuousOn (fun κ hκ=>ne_of_gt
    (mul_pos (mul_pos hk (root_pos hk hκ)) (add_pos hk (longitudinal_pos hk hκ))))
theorem rootAdmittance_continuousOn (hk:0<k) :
    ContinuousOn (rootAdmittance k) {κ:Transverse|square κ<k^2} :=
  ((root_continuous k).continuousOn.smul continuousOn_const).add
    ((coefficient_continuousOn hk).smul radial_continuous.continuousOn)
theorem invRootAdmittance_continuousOn (hk:0<k) :
    ContinuousOn (invRootAdmittance k) {κ:Transverse|square κ<k^2} :=
  ((continuousOn_const.div (root_continuous k).continuousOn
    (fun _ hκ=>(root_pos hk hκ).ne')).smul continuousOn_const).sub
      ((coefficient_continuousOn hk).smul radial_continuous.continuousOn)
theorem rootAdmittance_transpose (k:ℝ) (κ:Transverse) :
    (rootAdmittance k κ).transpose=rootAdmittance k κ := by
  simp [rootAdmittance,Matrix.transpose_add,Matrix.transpose_smul,radial_transpose]
theorem invRootAdmittance_transpose (k:ℝ) (κ:Transverse) :
    (invRootAdmittance k κ).transpose=invRootAdmittance k κ := by
  simp [invRootAdmittance,Matrix.transpose_sub,Matrix.transpose_smul,radial_transpose]

end GeneralizedResearch.ObliqueVacuum
