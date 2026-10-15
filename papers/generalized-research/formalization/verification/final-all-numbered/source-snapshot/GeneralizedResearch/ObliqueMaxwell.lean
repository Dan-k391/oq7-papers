import GeneralizedResearch.ObliqueVacuum
import GeneralizedResearch.ChannelAttainment
import OQ7.PhysicalExponential

/-! The literal oblique four-component Maxwell transfer. Material tensors are
nonmagnetic, have zz=1 and no transverse/longitudinal coupling. The transverse
permittivity is R+iQ with real symmetric R,Q; passivity is Q positive
semidefinite. Flux and reciprocity identities are derived from this generator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.ObliqueMaxwell
open ObliqueVacuum ChannelAttainment
open scoped Matrix Matrix.Norms.Operator ComplexOrder
abbrev CMat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Channel := Fin 2 ⊕ Fin 2
abbrev Mat4 := Matrix Channel Channel ℂ

def realBlock (k:ℝ) (κ:Transverse) (R:RMat) : RMat :=
  R-(1/k^2) • radial (perpendicular κ)
def materialBlock (k:ℝ) (κ:Transverse) (R Q:RMat) : CMat :=
  complexify (realBlock k κ R)+Complex.I • complexify Q
def generator (k:ℝ) (κ:Transverse) (R Q:RMat) : Mat4 :=
  (Complex.I*(k:ℂ)) • Matrix.fromBlocks 0 (complexify (electricBlock k κ))
    (materialBlock k κ R Q) 0
def flux : Mat4 := Matrix.fromBlocks 0 1 1 0
def symplectic : Mat4 := Matrix.fromBlocks 0 1 (-1) 0
def lossBlock (Q:RMat) : Mat4 := Matrix.fromBlocks (complexify Q) 0 0 0
def transfer (k:ℝ) (κ:Transverse) (R Q:RMat) (d:ℝ) : Mat4 :=
  NormedSpace.exp (d • generator k κ R Q)

theorem electricBlock_transpose (k:ℝ) (κ:Transverse) :
    (electricBlock k κ).transpose=electricBlock k κ := by
  simp [electricBlock,Matrix.transpose_sub,Matrix.transpose_smul,radial_transpose]
theorem realBlock_transpose (k:ℝ) (κ:Transverse) (R:RMat) (hR:R.transpose=R) :
    (realBlock k κ R).transpose=realBlock k κ R := by
  simp [realBlock,Matrix.transpose_sub,Matrix.transpose_smul,radial_transpose,hR]
theorem materialBlock_transpose (k:ℝ) (κ:Transverse) (R Q:RMat)
    (hR:R.transpose=R) (hQ:Q.transpose=Q) :
    (materialBlock k κ R Q).transpose=materialBlock k κ R Q := by
  simp [materialBlock,Matrix.transpose_add,Matrix.transpose_smul,complexify_transpose,
    realBlock_transpose k κ R hR,hQ]
theorem materialBlock_conjTranspose (k:ℝ) (κ:Transverse) (R Q:RMat)
    (hR:R.transpose=R) (hQ:Q.transpose=Q) :
    (materialBlock k κ R Q).conjTranspose=
      complexify (realBlock k κ R)-Complex.I • complexify Q := by
  simp [materialBlock,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    complexify_conjTranspose,realBlock_transpose k κ R hR,hQ,sub_eq_add_neg]

theorem generator_flux (k:ℝ) (κ:Transverse) (R Q:RMat)
    (hR:R.transpose=R) (hQ:Q.transpose=Q) :
    (generator k κ R Q).conjTranspose*flux+flux*generator k κ R Q=
      (-2*(k:ℂ)) • lossBlock Q := by
  simp only [generator,flux,lossBlock,Matrix.conjTranspose_smul,Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero,Matrix.conjTranspose_one,smul_mul_assoc,mul_smul_comm,
    Matrix.fromBlocks_multiply,mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,
    materialBlock_conjTranspose k κ R Q hR hQ,complexify_conjTranspose,electricBlock_transpose,
    Matrix.fromBlocks_smul,smul_zero,Matrix.fromBlocks_add]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [Matrix.fromBlocks,materialBlock,Matrix.smul_apply,smul_eq_mul,
      Complex.star_def,Complex.mul_re,Complex.mul_im]
  all_goals apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

theorem generator_symplectic (k:ℝ) (κ:Transverse) (R Q:RMat)
    (hR:R.transpose=R) (hQ:Q.transpose=Q) :
    (generator k κ R Q).transpose*symplectic+symplectic*generator k κ R Q=0 := by
  simp only [generator,symplectic,Matrix.transpose_smul,Matrix.fromBlocks_transpose,
    Matrix.transpose_zero,Matrix.transpose_one,smul_mul_assoc,mul_smul_comm,
    Matrix.fromBlocks_multiply,mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,
    mul_neg,neg_mul,materialBlock_transpose k κ R Q hR hQ,complexify_transpose,
    electricBlock_transpose,Matrix.fromBlocks_smul,smul_zero,Matrix.fromBlocks_add]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [Matrix.fromBlocks]

theorem lossBlock_posSemidef {Q:RMat} (hQ:Q.PosSemidef) : (lossBlock Q).PosSemidef := by
  have hc := complexify_posSemidef hQ
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simp [Matrix.IsHermitian,lossBlock,Matrix.fromBlocks_conjTranspose,hc.1.eq]
  · intro u
    have he : star u ⬝ᵥ (lossBlock Q*ᵥu)=
        star (fun i:Fin 2=>u (Sum.inl i)) ⬝ᵥ
          (complexify Q*ᵥ(fun i:Fin 2=>u (Sum.inl i))) := by
      simp [lossBlock,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks]
    rw [he]
    exact hc.dotProduct_mulVec_nonneg _

theorem transfer_initial (k:ℝ) (κ:Transverse) (R Q:RMat) : transfer k κ R Q 0=1 := by
  simp [transfer]
theorem transfer_hasDerivAt (k:ℝ) (κ:Transverse) (R Q:RMat) (d:ℝ) :
    HasDerivAt (transfer k κ R Q) (generator k κ R Q*transfer k κ R Q d) d :=
  hasDerivAt_exp_smul_const' _ _

theorem generator_continuous (k:ℝ) (R Q:ℝ→RMat) (hR:Continuous R) (hQ:Continuous Q) :
    Continuous (fun p:Transverse×ℝ=>generator k p.1 (R p.2) (Q p.2)) := by
  apply continuous_pi;intro i;apply continuous_pi;intro j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [generator,Matrix.fromBlocks,materialBlock,realBlock,electricBlock,radial,perpendicular,
      complexify,Matrix.vecMulVec_apply,Matrix.smul_apply,smul_eq_mul]
  all_goals fun_prop

theorem transfer_continuous (k d:ℝ) (R Q:ℝ→RMat) (hR:Continuous R) (hQ:Continuous Q) :
    Continuous (fun p:Transverse×ℝ=>transfer k p.1 (R p.2) (Q p.2) d) := by
  exact NormedSpace.exp_continuous.comp ((generator_continuous k R Q hR hQ).const_smul d)

theorem matrix_quadratic_hasDerivAt {F:ℝ→Mat4} {G:Mat4} {x:ℝ}
    (h:HasDerivAt F G x) (u:Channel→ℂ) :
    HasDerivAt (fun z=>star u ⬝ᵥ (F z*ᵥu)) (star u ⬝ᵥ (G*ᵥu)) x := by
  have he (i j:Channel) : HasDerivAt (fun z=>F z i j) (G i j) x :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j
  have hr (i:Channel) := HasDerivAt.fun_sum (u:=Finset.univ)
    (fun j _=>(he i j).mul_const (u j))
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>(hr i).const_mul (star (u i)))
  convert hs using 1 <;> rfl

theorem conjTranspose_hasDerivAt {F:ℝ→Mat4} {G:Mat4} {x:ℝ} (h:HasDerivAt F G x) :
    HasDerivAt (fun z=>(F z).conjTranspose) G.conjTranspose x := by
  apply hasDerivAt_pi.mpr;intro i;apply hasDerivAt_pi.mpr;intro j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp h j) i).star

theorem flux_hasDerivAt (k:ℝ) (κ:Transverse) (R Q:RMat)
    (hR:R.transpose=R) (hQ:Q.transpose=Q) (x:ℝ) :
    HasDerivAt (fun z=>(transfer k κ R Q z).conjTranspose*flux*transfer k κ R Q z)
      ((-2*(k:ℂ)) • ((transfer k κ R Q x).conjTranspose*lossBlock Q*transfer k κ R Q x)) x := by
  have hd := transfer_hasDerivAt k κ R Q x
  have hp := ((conjTranspose_hasDerivAt hd).mul_const flux).mul hd
  convert hp using 1
  · rfl
  · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul]
    have he : (transfer k κ R Q x).conjTranspose*
        ((generator k κ R Q).conjTranspose*flux+flux*generator k κ R Q)*transfer k κ R Q x=
        (generator k κ R Q*transfer k κ R Q x).conjTranspose*flux*transfer k κ R Q x+
          (transfer k κ R Q x).conjTranspose*flux*(generator k κ R Q*transfer k κ R Q x) := by
      simp [Matrix.conjTranspose_mul,mul_add,add_mul,mul_assoc]
    rw [generator_flux k κ R Q hR hQ] at he
    simpa only [mul_smul_comm,smul_mul_assoc,Matrix.conjTranspose_mul,mul_assoc] using he

theorem flux_conjTranspose : flux.conjTranspose=flux := by
  simp [flux,Matrix.fromBlocks_conjTranspose]

theorem transfer_passive (k:ℝ) (κ:Transverse) (R Q:RMat) (hk:0≤k)
    (hR:R.transpose=R) (hQ:Q.PosSemidef) {d:ℝ} (hd:0≤d) :
    (flux-(transfer k κ R Q d).conjTranspose*flux*transfer k κ R Q d).PosSemidef := by
  have hQT : Q.transpose=Q := by
    ext i j
    have he := congrFun (congrFun hQ.1.eq i) j
    simpa [Matrix.conjTranspose_apply] using he
  have hloss := lossBlock_posSemidef hQ
  have hHerm : (flux-(transfer k κ R Q d).conjTranspose*flux*transfer k κ R Q d).IsHermitian := by
    simp [Matrix.IsHermitian,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,flux_conjTranspose,mul_assoc]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro u
  let f : ℝ→ℝ := fun z=>(star u ⬝ᵥ
    (((transfer k κ R Q z).conjTranspose*flux*transfer k κ R Q z)*ᵥu)).re
  have hderiv (x:ℝ) : HasDerivAt f
      (-2*k*(star (transfer k κ R Q x*ᵥu) ⬝ᵥ
        (lossBlock Q*ᵥ(transfer k κ R Q x*ᵥu))).re) x := by
    have hm := matrix_quadratic_hasDerivAt (flux_hasDerivAt k κ R Q hR hQT x) u
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hm
    convert hr using 1
    · rfl
    · simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
      have he : star u ⬝ᵥ (((transfer k κ R Q x).conjTranspose*lossBlock Q*transfer k κ R Q x)*ᵥu)=
          star (transfer k κ R Q x*ᵥu) ⬝ᵥ (lossBlock Q*ᵥ(transfer k κ R Q x*ᵥu)) := by
        simp only [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.star_mulVec,Matrix.vecMul_vecMul]
      rw [he]
      simp [Complex.mul_re]
  have hanti : Antitone f := antitone_of_hasDerivAt_nonpos hderiv (by
    intro x
    have hn := (Complex.nonneg_iff.mp (hloss.dotProduct_mulVec_nonneg (transfer k κ R Q x*ᵥu))).1
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hn)
  have hf := hanti hd
  have hre : 0≤(star u ⬝ᵥ
      ((flux-(transfer k κ R Q d).conjTranspose*flux*transfer k κ R Q d)*ᵥu)).re := by
    simpa [f,transfer_initial,Matrix.sub_mulVec,dotProduct_sub] using sub_nonneg.mpr hf
  have hs := hHerm.star_dotProduct_mulVec_comm u u
  have him := congrArg Complex.im hs
  have him0 : (star u ⬝ᵥ
      ((flux-(transfer k κ R Q d).conjTranspose*flux*transfer k κ R Q d)*ᵥu)).im=0 := by
    simp only [Complex.star_def,Complex.conj_im] at him
    linarith
  exact Complex.nonneg_iff.mpr ⟨hre,him0.symm⟩

theorem transpose_hasDerivAt {F:ℝ→Mat4} {G:Mat4} {x:ℝ} (h:HasDerivAt F G x) :
    HasDerivAt (fun z=>(F z).transpose) G.transpose x := by
  apply hasDerivAt_pi.mpr;intro i;apply hasDerivAt_pi.mpr;intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp h j) i

theorem transfer_symplectic (k:ℝ) (κ:Transverse) (R Q:RMat)
    (hR:R.transpose=R) (hQ:Q.transpose=Q) (d:ℝ) :
    (transfer k κ R Q d).transpose*symplectic*transfer k κ R Q d=symplectic := by
  let F : ℝ→Mat4 := fun z=>(transfer k κ R Q z).transpose*symplectic*transfer k κ R Q z
  have hF (x:ℝ) : HasDerivAt F 0 x := by
    have hd := transfer_hasDerivAt k κ R Q x
    have hp := ((transpose_hasDerivAt hd).mul_const symplectic).mul hd
    convert hp using 1
    · rfl
    · have he : (transfer k κ R Q x).transpose*
          ((generator k κ R Q).transpose*symplectic+symplectic*generator k κ R Q)*transfer k κ R Q x=
          (generator k κ R Q*transfer k κ R Q x).transpose*symplectic*transfer k κ R Q x+
            (transfer k κ R Q x).transpose*symplectic*(generator k κ R Q*transfer k κ R Q x) := by
        simp [Matrix.transpose_mul,mul_add,add_mul,mul_assoc]
      rw [generator_symplectic k κ R Q hR hQ] at he
      simpa using he
  have hc := is_const_of_deriv_eq_zero (fun x=>(hF x).differentiableAt) (fun x=>(hF x).deriv) d 0
  simpa [F,transfer_initial] using hc

end GeneralizedResearch.ObliqueMaxwell
