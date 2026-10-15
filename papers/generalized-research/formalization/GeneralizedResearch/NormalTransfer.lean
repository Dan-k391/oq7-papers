import GeneralizedResearch.ObliqueMaxwell

/-! Exact normal-incidence transfer reduction.  The four-component matrix
exponential is connected to the already proved scalar homogeneous fields by
actual invariant polarization projections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedResearch.NormalTransfer
open ObliqueVacuum ObliqueMaxwell
open scoped Matrix Matrix.Norms.Operator

def lift (P:CMat) (M N:OQ7.Mat2) : Mat4 := Matrix.fromBlocks
  (M 0 0 • P+N 0 0 • (1-P)) (M 0 1 • P+N 0 1 • (1-P))
  (M 1 0 • P+N 1 0 • (1-P)) (M 1 1 • P+N 1 1 • (1-P))

theorem lift_mul (P:CMat) (hP:P*P=P) (M N M' N':OQ7.Mat2) :
    lift P M N*lift P M' N'=lift P (M*M') (N*N') := by
  have hpq : P*(1-P)=0 := by rw [mul_sub,mul_one,hP,sub_self]
  have hqp : (1-P)*P=0 := by rw [sub_mul,one_mul,hP,sub_self]
  have hqq : (1-P)*(1-P)=1-P := by rw [sub_mul,one_mul,hpq,sub_zero]
  simp only [lift,Matrix.fromBlocks_multiply,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    smul_smul,hP,hpq,hqp,hqq,smul_zero,add_zero,zero_add,Matrix.mul_apply,Fin.sum_univ_two]
  congr 1 <;> module

theorem lift_one (P:CMat) : lift P 1 1=1 := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [lift,Matrix.fromBlocks,Matrix.one_apply]

theorem lift_hasDerivAt {P:CMat} {M N:ℝ→OQ7.Mat2} {M' N':OQ7.Mat2} {x:ℝ}
    (hM:HasDerivAt M M' x) (hN:HasDerivAt N N' x) :
    HasDerivAt (fun z=>lift P (M z) (N z)) (lift P M' N') x := by
  apply hasDerivAt_pi.mpr;intro i;apply hasDerivAt_pi.mpr;intro j
  rcases i with i|i <;> rcases j with j|j
  all_goals
    first
    | exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hM 0) 0).mul_const (P i j)).add
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hN 0) 0).mul_const ((1-P) i j))
    | exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hM 0) 1).mul_const (P i j)).add
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hN 0) 1).mul_const ((1-P) i j))
    | exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hM 1) 0).mul_const (P i j)).add
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hN 1) 0).mul_const ((1-P) i j))
    | exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hM 1) 1).mul_const (P i j)).add
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hN 1) 1).mul_const ((1-P) i j))

theorem solution_eq_exp (G:Mat4) (F:ℝ→Mat4) (h0:F 0=1)
    (hF:∀z,HasDerivAt F (G*F z) z) (z:ℝ) : F z=NormedSpace.exp (z • G) := by
  let V : ℝ→Mat4 := fun u=>NormedSpace.exp ((-u) • G)*F u
  have hV (u:ℝ) : HasDerivAt V 0 u := by
    have he0 : HasDerivAt (fun v:ℝ=>NormedSpace.exp (v • G))
        (NormedSpace.exp ((-u) • G)*G) (-u) := hasDerivAt_exp_smul_const G (-u)
    have he := he0.scomp u ((hasDerivAt_id u).neg)
    have hp := he.mul (hF u)
    convert hp using 1 <;> first |rfl |simp [mul_assoc]
  have hc : V z=V 0 := is_const_of_deriv_eq_zero
    (fun u=>(hV u).differentiableAt) (fun u=>(hV u).deriv) z 0
  have hz : V 0=1 := by simp [V,h0]
  rw [hz] at hc
  have hi : NormedSpace.exp (z • G)*NormedSpace.exp ((-z) • G)=1 := by
    rw [←Matrix.exp_add_of_commute _ _ (Commute.smul_left (Commute.smul_right (Commute.refl G) _) _)]
    simp
  have hm := congrArg (fun X:Mat4=>NormedSpace.exp (z • G)*X) hc
  simpa only [V,←mul_assoc,hi,one_mul,mul_one] using hm

theorem lift_homogeneous_eq_exp (P:CMat) (hP:P*P=P) (k:ℝ) {n:ℂ} (hn:n≠0) (z:ℝ) :
    lift P (OQ7.homogeneousTransfer k n z) (OQ7.homogeneousTransfer k 1 z)=
      NormedSpace.exp (z • lift P (OQ7.maxwellGenerator k n) (OQ7.maxwellGenerator k 1)) := by
  apply solution_eq_exp (lift P (OQ7.maxwellGenerator k n) (OQ7.maxwellGenerator k 1))
    (fun x=>lift P (OQ7.homogeneousTransfer k n x) (OQ7.homogeneousTransfer k 1 x))
  · have hz : OQ7.homogeneousTransfer k n 0=1 := by
      ext i j;fin_cases i <;> fin_cases j <;> simp [OQ7.homogeneousTransfer]
    have ho : OQ7.homogeneousTransfer k 1 0=1 := by
      ext i j;fin_cases i <;> fin_cases j <;> simp [OQ7.homogeneousTransfer]
    rw [hz,ho,lift_one]
  · intro x
    rw [lift_mul P hP]
    exact lift_hasDerivAt (OQ7.homogeneousTransfer_hasDerivAt k hn x)
      (OQ7.homogeneousTransfer_hasDerivAt k (by norm_num : (1:ℂ)≠0) x)

theorem generator_at_zero (P:CMat) (k:ℝ) (n:ℂ) (R Q:RMat)
    (hε:ChannelAttainment.complexify R+Complex.I • ChannelAttainment.complexify Q=
      n^2 • P+(1-P)) :
    generator k 0 R Q=lift P (OQ7.maxwellGenerator k n) (OQ7.maxwellGenerator k 1) := by
  have he : electricBlock k 0=1 := by ext i j;simp [electricBlock,radial,Matrix.vecMulVec_apply]
  have hp : radial (perpendicular (0:Transverse))=0 := by
    ext i j;fin_cases i <;> fin_cases j <;> simp [radial,perpendicular,Matrix.vecMulVec_apply]
  have hm : materialBlock k 0 R Q=n^2 • P+(1-P) := by
    simpa only [materialBlock,realBlock,hp,smul_zero,sub_zero] using hε
  simp only [generator,he,hm,ChannelAttainment.complexify_one]
  ext i j
  rcases i with i|i <;> rcases j with j|j
  all_goals by_cases hij:i=j <;>
    simp [lift,OQ7.maxwellGenerator,Matrix.fromBlocks,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hij] <;> ring

theorem transfer_at_zero (P:CMat) (hP:P*P=P) (k:ℝ) {n:ℂ} (hn:n≠0) (R Q:RMat)
    (hε:ChannelAttainment.complexify R+Complex.I • ChannelAttainment.complexify Q=
      n^2 • P+(1-P)) (z:ℝ) :
    transfer k 0 R Q z=lift P (OQ7.homogeneousTransfer k n z) (OQ7.homogeneousTransfer k 1 z) := by
  rw [transfer,generator_at_zero P k n R Q hε]
  exact (lift_homogeneous_eq_exp P hP k hn z).symm

end GeneralizedResearch.NormalTransfer
