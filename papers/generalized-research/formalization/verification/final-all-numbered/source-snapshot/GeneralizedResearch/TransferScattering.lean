import GeneralizedResearch.ObliqueWaveBasis
import Mathlib.Topology.Instances.Matrix

/-! Scattering is solved from the actual wave transfer.  Invertibility of the
right-going block follows from flux passivity, so no radiation solution or
contractivity assumption is hidden in a chosen inverse. -/
noncomputable section
namespace GeneralizedResearch.TransferScattering
open ObliqueVacuum ObliqueMaxwell ObliqueWaveBasis ChannelPowers
open scoped Matrix ComplexOrder

def A (K:Mat4) : CMat := K.toBlocks₁₁
def B (K:Mat4) : CMat := K.toBlocks₁₂
def C (K:Mat4) : CMat := K.toBlocks₂₁
def D (K:Mat4) : CMat := K.toBlocks₂₂
def scattering (K:Mat4) : Mat4 := Matrix.fromBlocks
  (-((D K)⁻¹*C K)) (D K)⁻¹ (A K-B K*(D K)⁻¹*C K) (B K*(D K)⁻¹)
def leftState (K:Mat4) : Mat4 := Matrix.fromBlocks 1 0 (-((D K)⁻¹*C K)) (D K)⁻¹
def rightState (K:Mat4) : Mat4 := Matrix.fromBlocks (A K-B K*(D K)⁻¹*C K) (B K*(D K)⁻¹) 0 1

theorem blocks (K:Mat4) : Matrix.fromBlocks (A K) (B K) (C K) (D K)=K := Matrix.fromBlocks_toBlocks K

theorem flux_quadratic (u:Channel→ℂ) :
    (star u ⬝ᵥ (powerFlux*ᵥu)).re=
      power (fun i:Fin 2=>u (Sum.inl i))-power (fun i:Fin 2=>u (Sum.inr i)) := by
  simp [powerFlux,power,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks]
  ring

theorem flux_monotone (K:Mat4) (hK:(powerFlux-K.conjTranspose*powerFlux*K).PosSemidef)
    (u:Channel→ℂ) : (star (K*ᵥu) ⬝ᵥ (powerFlux*ᵥ(K*ᵥu))).re≤
      (star u ⬝ᵥ (powerFlux*ᵥu)).re := by
  have hn := (Complex.nonneg_iff.mp (hK.dotProduct_mulVec_nonneg u)).1
  have he : star u ⬝ᵥ ((K.conjTranspose*powerFlux*K)*ᵥu)=
      star (K*ᵥu) ⬝ᵥ (powerFlux*ᵥ(K*ᵥu)) := by
    simp only [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.star_mulVec,Matrix.vecMul_vecMul]
  simp only [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,he] at hn
  linarith

theorem power_zero {u:Fin 2→ℂ} (hu:power u=0) : u=0 := by
  apply dotProduct_star_self_eq_zero.mp
  apply Complex.ext
  · exact hu
  · exact (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg u)).2.symm

theorem D_injective (K:Mat4) (hK:(powerFlux-K.conjTranspose*powerFlux*K).PosSemidef) :
    Function.Injective (D K).mulVec := by
  apply (D K).mulVecLin.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hm := flux_monotone K hK (Sum.elim 0 v)
  have hstate : K*ᵥSum.elim 0 v=Sum.elim (B K*ᵥv) (D K*ᵥv) := by
    conv_lhs => arg 1;rw [←blocks K]
    simp [Matrix.fromBlocks_mulVec]
  rw [hstate,flux_quadratic,flux_quadratic] at hm
  change power (B K*ᵥv)-power (D K*ᵥv)≤power (0:Fin 2→ℂ)-power v at hm
  change (D K)*ᵥv=0 at hv
  simp only [hv,power,star_zero,zero_dotProduct,Complex.zero_re,sub_zero,zero_sub] at hm
  apply power_zero
  have hp := power_nonneg v
  have hb := power_nonneg (B K*ᵥv)
  dsimp [power] at hp hb ⊢
  linarith

theorem D_isUnit (K:Mat4) (hK:(powerFlux-K.conjTranspose*powerFlux*K).PosSemidef) : IsUnit (D K) :=
  Matrix.mulVec_injective_iff_isUnit.mp (D_injective K hK)

theorem boundary (K:Mat4) (hD:IsUnit (D K)) : K*leftState K=rightState K := by
  have hi := Matrix.mul_nonsing_inv (D K) ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  conv_lhs => arg 1;rw [←blocks K]
  simp only [leftState,rightState,Matrix.fromBlocks_multiply,mul_one,mul_zero,add_zero,zero_add,
    mul_neg,neg_mul,Matrix.mul_assoc,hi,one_mul,add_neg_cancel]
  rw [sub_eq_add_neg]
  have hic : D K*((D K)⁻¹*C K)=C K := by rw [←mul_assoc,hi,one_mul]
  rw [hic,add_neg_cancel]

theorem flux_difference (K:Mat4) :
    (leftState K).conjTranspose*powerFlux*leftState K-
      (rightState K).conjTranspose*powerFlux*rightState K=
      1-(scattering K).conjTranspose*scattering K := by
  simp only [leftState,rightState,scattering,powerFlux,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply,Matrix.conjTranspose_zero,Matrix.conjTranspose_one,
    Matrix.conjTranspose_neg,mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,
    mul_neg,neg_mul,neg_neg ]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [Matrix.fromBlocks,Matrix.one_apply]
  all_goals ring

theorem scattering_passive (K:Mat4) (hK:(powerFlux-K.conjTranspose*powerFlux*K).PosSemidef) :
    (1-(scattering K).conjTranspose*scattering K).PosSemidef := by
  have hp := hK.conjTranspose_mul_mul_same (leftState K)
  have hb := boundary K (D_isUnit K hK)
  have he : (leftState K).conjTranspose*(powerFlux-K.conjTranspose*powerFlux*K)*leftState K=
      (leftState K).conjTranspose*powerFlux*leftState K-
        (rightState K).conjTranspose*powerFlux*rightState K := by
    rw [←hb]
    simp only [Matrix.conjTranspose_mul,mul_sub,sub_mul,mul_assoc]
  rwa [he,flux_difference] at hp

theorem symplectic_difference (K:Mat4) :
    (leftState K).transpose*symplectic*leftState K-
      (rightState K).transpose*symplectic*rightState K=
      scattering K-(scattering K).transpose := by
  simp only [leftState,rightState,scattering,symplectic,Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply,Matrix.transpose_zero,Matrix.transpose_one,
    Matrix.transpose_neg,mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul,
    mul_neg,neg_mul,neg_neg ]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [Matrix.fromBlocks,Matrix.one_apply]
  all_goals ring

theorem scattering_reciprocal (K:Mat4) (hD:IsUnit (D K))
    (hK:K.transpose*symplectic*K=symplectic) : (scattering K).transpose=scattering K := by
  have hb := boundary K hD
  have he : (leftState K).transpose*symplectic*leftState K-
      (rightState K).transpose*symplectic*rightState K=0 := by
    rw [←hb,Matrix.transpose_mul]
    calc
      _ = (leftState K).transpose*(symplectic-K.transpose*symplectic*K)*leftState K := by
        simp [mul_sub,sub_mul,mul_assoc]
      _ = 0 := by rw [hK,sub_self,mul_zero,zero_mul]
  rw [symplectic_difference] at he
  exact (sub_eq_zero.mp he).symm

def leftWaves (S:Mat4) : Mat4 := Matrix.fromBlocks 1 0 S.toBlocks₁₁ S.toBlocks₁₂
def rightWaves (S:Mat4) : Mat4 := Matrix.fromBlocks S.toBlocks₂₁ S.toBlocks₂₂ 0 1

theorem scattering_of_boundary (K S:Mat4) (hD:IsUnit (D K))
    (h:K*leftWaves S=rightWaves S) : scattering K=S := by
  have hi := Matrix.nonsing_inv_mul (D K) ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have he : Matrix.fromBlocks (A K) (B K) (C K) (D K)*leftWaves S=rightWaves S := by
    rwa [blocks]
  simp only [leftWaves,rightWaves,Matrix.fromBlocks_multiply,mul_one,mul_zero,zero_add,add_zero] at he
  have hc : C K+D K*S.toBlocks₁₁=0 := by
    simpa using congrArg Matrix.toBlocks₂₁ he
  have hd : D K*S.toBlocks₁₂=1 := by simpa using congrArg Matrix.toBlocks₂₂ he
  have h11 : S.toBlocks₁₁= -((D K)⁻¹*C K) := by
    have hm := congrArg (fun M:CMat=>(D K)⁻¹*M) hc
    simp only [mul_add,←mul_assoc,hi,one_mul,mul_zero] at hm
    exact eq_neg_of_add_eq_zero_right hm
  have h12 : S.toBlocks₁₂=(D K)⁻¹ := by
    have hm := congrArg (fun M:CMat=>(D K)⁻¹*M) hd
    simpa only [←mul_assoc,hi,one_mul,mul_one] using hm
  have h21 : A K+B K*S.toBlocks₁₁=S.toBlocks₂₁ := by simpa using congrArg Matrix.toBlocks₁₁ he
  have h22 : B K*S.toBlocks₁₂=S.toBlocks₂₂ := by simpa using congrArg Matrix.toBlocks₁₂ he
  rw [h11] at h21
  rw [h12] at h22
  rw [scattering,←Matrix.fromBlocks_toBlocks S,h11,h12,←h21,←h22]
  simp [sub_eq_add_neg,mul_assoc]

theorem scattering_continuousAt {X:Type*} [TopologicalSpace X] {K:X→Mat4} {x:X}
    (hK:ContinuousAt K x) (hD:IsUnit (D (K x))) : ContinuousAt (fun y=>scattering (K y)) x := by
  have hDc : ContinuousAt (fun y=>D (K y)) x := by
    apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro j
    exact continuousAt_pi.mp (continuousAt_pi.mp hK (Sum.inr i)) (Sum.inr j)
  have hdet : (D (K x)).det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hi : ContinuousAt (fun y=>(D (K y))⁻¹) x := by
    have hmat : ContinuousAt (fun M:CMat=>M⁻¹) (D (K x)) := by
      apply continuousAt_matrix_inv
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
    exact ContinuousAt.comp (f:=fun y=>D (K y)) (x:=x) hmat hDc
  apply continuousAt_pi.mpr;intro i;apply continuousAt_pi.mpr;intro j
  rcases i with i|i <;> rcases j with j|j <;>
    simp only [scattering,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.neg_apply,Matrix.sub_apply]
  · exact (continuousAt_pi.mp (continuousAt_pi.mp (hi.mul (by
      apply continuousAt_pi.mpr;intro l;apply continuousAt_pi.mpr;intro m
      exact continuousAt_pi.mp (continuousAt_pi.mp hK (Sum.inr l)) (Sum.inl m))) i) j).neg
  · exact continuousAt_pi.mp (continuousAt_pi.mp hi i) j
  · have ha : ContinuousAt (fun y=>A (K y) i j) x := continuousAt_pi.mp (continuousAt_pi.mp hK (Sum.inl i)) (Sum.inl j)
    have hb : ContinuousAt (fun y=>B (K y)) x := by
      apply continuousAt_pi.mpr;intro l;apply continuousAt_pi.mpr;intro m
      exact continuousAt_pi.mp (continuousAt_pi.mp hK (Sum.inl l)) (Sum.inr m)
    have hc : ContinuousAt (fun y=>C (K y)) x := by
      apply continuousAt_pi.mpr;intro l;apply continuousAt_pi.mpr;intro m
      exact continuousAt_pi.mp (continuousAt_pi.mp hK (Sum.inr l)) (Sum.inl m)
    exact ha.sub (continuousAt_pi.mp (continuousAt_pi.mp ((hb.mul hi).mul hc) i) j)
  · have hb : ContinuousAt (fun y=>B (K y)) x := by
      apply continuousAt_pi.mpr;intro l;apply continuousAt_pi.mpr;intro m
      exact continuousAt_pi.mp (continuousAt_pi.mp hK (Sum.inl l)) (Sum.inr m)
    exact continuousAt_pi.mp (continuousAt_pi.mp (hb.mul hi) i) j

end GeneralizedResearch.TransferScattering
