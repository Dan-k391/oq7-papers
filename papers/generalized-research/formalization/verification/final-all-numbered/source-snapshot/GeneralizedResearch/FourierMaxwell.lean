import GeneralizedResearch.ObliqueFamily

/-! Actual three-dimensional Maxwell plane waves associated with the
four-component transfer generator. Longitudinal components and transverse
derivatives are derived explicitly in the fixed laboratory axes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.FourierMaxwell
open ObliqueVacuum ObliqueMaxwell ChannelAttainment
open scoped Matrix Matrix.Norms.Operator
abbrev Vec2 := Fin 2→ℂ
abbrev Vec3 := Fin 3→ℂ

def state (k:ℝ) (κ:Transverse) (R Q:RMat) (u:Channel→ℂ) (z:ℝ) : Channel→ℂ :=
  transfer k κ R Q z*ᵥu
def electric (k:ℝ) (κ:Transverse) (u:Channel→ℂ) : Vec3 :=
  ![u (Sum.inl 0),u (Sum.inl 1),
    -((κ 0:ℂ)*u (Sum.inr 0)+(κ 1:ℂ)*u (Sum.inr 1))/(k:ℂ)]
def magnetic (k:ℝ) (κ:Transverse) (u:Channel→ℂ) : Vec3 :=
  ![-u (Sum.inr 1),u (Sum.inr 0),
    ((κ 0:ℂ)*u (Sum.inl 1)-(κ 1:ℂ)*u (Sum.inl 0))/(k:ℂ)]
def constitutive (R Q:RMat) (E:Vec3) : Vec3 :=
  ![((complexify R+Complex.I • complexify Q)*ᵥ![E 0,E 1]) 0,
    ((complexify R+Complex.I • complexify Q)*ᵥ![E 0,E 1]) 1,E 2]
def fourierCurl (κ:Transverse) (F G:Vec3) : Vec3 :=
  ![Complex.I*(κ 1:ℂ)*F 2-G 1,
    G 0-Complex.I*(κ 0:ℂ)*F 2,
    Complex.I*(κ 0:ℂ)*F 1-Complex.I*(κ 1:ℂ)*F 0]

theorem state_hasDerivAt (k:ℝ) (κ:Transverse) (R Q:RMat) (u:Channel→ℂ) (z:ℝ) :
    HasDerivAt (state k κ R Q u) (generator k κ R Q*ᵥstate k κ R Q u z) z := by
  apply hasDerivAt_pi.mpr;intro i
  have hd := transfer_hasDerivAt k κ R Q z
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _=>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j).mul_const (u j))
  simp only [state]
  convert hs using 1
  all_goals first |rfl |simpa only [Matrix.mulVec,dotProduct] using
    (congrFun (Matrix.mulVec_mulVec u (generator k κ R Q) (transfer k κ R Q z)) i)

theorem electric_hasDerivAt {k:ℝ} {κ:Transverse} {F:ℝ→Channel→ℂ} {G:Channel→ℂ} {z:ℝ}
    (hF:HasDerivAt F G z) : HasDerivAt (fun x=>electric k κ (F x)) (electric k κ G) z := by
  apply hasDerivAt_pi.mpr;intro i;fin_cases i
  · exact hasDerivAt_pi.mp hF (Sum.inl 0)
  · exact hasDerivAt_pi.mp hF (Sum.inl 1)
  · exact ((((hasDerivAt_pi.mp hF (Sum.inr 0)).const_mul (κ 0:ℂ)).add
      ((hasDerivAt_pi.mp hF (Sum.inr 1)).const_mul (κ 1:ℂ))).neg).div_const (k:ℂ)

theorem magnetic_hasDerivAt {k:ℝ} {κ:Transverse} {F:ℝ→Channel→ℂ} {G:Channel→ℂ} {z:ℝ}
    (hF:HasDerivAt F G z) : HasDerivAt (fun x=>magnetic k κ (F x)) (magnetic k κ G) z := by
  apply hasDerivAt_pi.mpr;intro i;fin_cases i
  · exact (hasDerivAt_pi.mp hF (Sum.inr 1)).neg
  · exact hasDerivAt_pi.mp hF (Sum.inr 0)
  · exact (((hasDerivAt_pi.mp hF (Sum.inl 1)).const_mul (κ 0:ℂ)).sub
      ((hasDerivAt_pi.mp hF (Sum.inl 0)).const_mul (κ 1:ℂ))).div_const (k:ℂ)

theorem fourier_maxwell (k:ℝ) (hk:k≠0) (κ:Transverse) (R Q:RMat) (u:Channel→ℂ) :
    fourierCurl κ (electric k κ u) (electric k κ (generator k κ R Q*ᵥu))=
        (Complex.I*(k:ℂ)) • magnetic k κ u ∧
      fourierCurl κ (magnetic k κ u) (magnetic k κ (generator k κ R Q*ᵥu))=
        (-(Complex.I*(k:ℂ))) • constitutive R Q (electric k κ u) := by
  have hkC : (k:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hk
  constructor <;> ext i <;> fin_cases i <;>
    simp [fourierCurl,electric,magnetic,constitutive,generator,materialBlock,realBlock,
      electricBlock,radial,perpendicular,complexify,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
  all_goals field_simp [hkC]
  all_goals ring_nf

def phase (κ:Transverse) (x y:ℝ) : ℂ :=
  OQ7Prescribed.apertureOscillation (κ 0) x*OQ7Prescribed.apertureOscillation (κ 1) y

def plane (κ:Transverse) (F:ℝ→Vec3) (x y z:ℝ) : Vec3 := phase κ x y • F z

def curl (F:ℝ→ℝ→ℝ→Vec3) (x y z:ℝ) : Vec3 :=
  ![deriv (fun r=>F x r z 2) y-deriv (fun r=>F x y r 1) z,
    deriv (fun r=>F x y r 0) z-deriv (fun r=>F r y z 2) x,
    deriv (fun r=>F r y z 1) x-deriv (fun r=>F x r z 0) y]

theorem plane_curl (κ:Transverse) {F:ℝ→Vec3} {G:Vec3} {z:ℝ}
    (hF:HasDerivAt F G z) (x y:ℝ) :
    curl (plane κ F) x y z=phase κ x y • fourierCurl κ (F z) G := by
  have hx (i:Fin 3) : HasDerivAt (fun r=>plane κ F r y z i)
      (Complex.I*(κ 0:ℂ)*(phase κ x y*F z i)) x := by
    have hp := ((OQ7Prescribed.apertureOscillation_hasDerivAt (κ 0) x).mul_const
      (OQ7Prescribed.apertureOscillation (κ 1) y)).mul_const (F z i)
    convert hp using 1 <;> first |rfl |(simp only [phase];ring)
  have hy (i:Fin 3) : HasDerivAt (fun r=>plane κ F x r z i)
      (Complex.I*(κ 1:ℂ)*(phase κ x y*F z i)) y := by
    have hp := ((OQ7Prescribed.apertureOscillation_hasDerivAt (κ 1) y).const_mul
      (OQ7Prescribed.apertureOscillation (κ 0) x)).mul_const (F z i)
    convert hp using 1 <;> first |rfl |(simp only [phase];ring)
  have hz (i:Fin 3) : HasDerivAt (fun r=>plane κ F x y r i) (phase κ x y*G i) z :=
    (hasDerivAt_pi.mp hF i).const_mul (phase κ x y)
  ext i;fin_cases i <;> simp [curl,(hx _).deriv,(hy _).deriv,(hz _).deriv,fourierCurl]
  all_goals ring

theorem constitutive_smul (R Q:RMat) (c:ℂ) (E:Vec3) :
    constitutive R Q (c • E)=c • constitutive R Q E := by
  ext i;fin_cases i <;>
    simp [constitutive,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring

theorem plane_maxwell (k:ℝ) (hk:k≠0) (κ:Transverse) (R Q:RMat) (u:Channel→ℂ) (x y z:ℝ) :
    curl (plane κ (fun r=>electric k κ (state k κ R Q u r))) x y z=
        (Complex.I*(k:ℂ)) • plane κ (fun r=>magnetic k κ (state k κ R Q u r)) x y z ∧
      curl (plane κ (fun r=>magnetic k κ (state k κ R Q u r))) x y z=
        (-(Complex.I*(k:ℂ))) •
          constitutive R Q (plane κ (fun r=>electric k κ (state k κ R Q u r)) x y z) := by
  have hs := state_hasDerivAt k κ R Q u z
  have hm := fourier_maxwell k hk κ R Q (state k κ R Q u z)
  constructor
  · rw [plane_curl κ (electric_hasDerivAt hs),hm.1]
    simp [plane,smul_smul,mul_comm]
  · rw [plane_curl κ (magnetic_hasDerivAt hs),hm.2]
    simp [plane,constitutive_smul,smul_smul,mul_comm]

end GeneralizedResearch.FourierMaxwell
