import GeneralizedResearch.ChannelPowers
import OQ7.TwoPort

/-! Literal four-port response of a scalar absorbing x channel, a vacuum y
channel, and a reflectionless real half-wave plate. All matrix properties and
powers are derived from the scalar passivity and the plate orthogonality. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace GeneralizedResearch.PlanarFourPort
open scoped Matrix ComplexOrder
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev Vec4 := Fin 4 → ℂ

def absorber (r τ z : ℂ) : Mat4 :=
  !![r,0,τ,0; 0,0,0,z; τ,0,r,0; 0,z,0,0]
def plate (t s : ℝ) : Mat4 :=
  !![1,0,0,0; 0,1,0,0; 0,0,(t:ℂ),-(s:ℂ); 0,0,-(s:ℂ),-(t:ℂ)]
def scattering (r τ z : ℂ) (t s : ℝ) : Mat4 :=
  plate t s * absorber r τ z * plate t s
def reference (z : ℂ) : Mat4 :=
  !![0,0,-z,0; 0,0,0,-z; -z,0,0,0; 0,-z,0,0]
def left : Vec4 := ![0,1,0,0]
def right : Vec4 := ![0,0,0,1]
def xChannels : Matrix (Fin 2) (Fin 4) ℂ := !![1,0,0,0;0,0,1,0]

theorem plate_transpose (t s : ℝ) : (plate t s).transpose = plate t s := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [plate]
theorem plate_conjTranspose (t s : ℝ) : (plate t s).conjTranspose = plate t s := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [plate]
theorem plate_square (t s : ℝ) (hu : t^2+s^2=1) : plate t s * plate t s = 1 := by
  have hc : (t:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast hu
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [plate,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf at hc ⊢ <;> exact hc
theorem absorber_transpose (r τ z : ℂ) : (absorber r τ z).transpose=absorber r τ z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [absorber]
theorem scattering_transpose (r τ z : ℂ) (t s : ℝ) :
    (scattering r τ z t s).transpose=scattering r τ z t s := by
  simp [scattering,Matrix.transpose_mul,plate_transpose,absorber_transpose,mul_assoc]
theorem reference_transpose (z : ℂ) : (reference z).transpose=reference z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [reference]
theorem reference_unitary (z : ℂ) (hz : star z*z=1) :
    (reference z).conjTranspose * reference z=1 := by
  change (starRingEnd ℂ) z*z=1 at hz
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [reference,Matrix.mul_apply,Fin.sum_univ_succ,hz]

theorem absorber_defect (r τ z : ℂ) (hz : star z*z=1) :
    1-(absorber r τ z).conjTranspose*absorber r τ z =
      xChannels.conjTranspose*OQ7.absorptionMatrix r r τ*xChannels := by
  change (starRingEnd ℂ) z*z=1 at hz
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [absorber,xChannels,OQ7.absorptionMatrix,OQ7.scatteringMatrix,
      Matrix.mul_apply,Fin.sum_univ_succ,hz]

theorem scattering_passive (r τ z : ℂ) (t s : ℝ) (hu : t^2+s^2=1)
    (hz : star z*z=1) (hp : OQ7.Passive r r τ) :
    ((1:Mat4)-(scattering r τ z t s).conjTranspose*scattering r τ z t s).PosSemidef := by
  have hb : ((1:Mat4)-(absorber r τ z).conjTranspose*absorber r τ z).PosSemidef := by
    rw [absorber_defect r τ z hz]
    exact hp.conjTranspose_mul_mul_same xChannels
  have he : (1:Mat4)-(scattering r τ z t s).conjTranspose*scattering r τ z t s =
      (plate t s).conjTranspose * (1-(absorber r τ z).conjTranspose*absorber r τ z) * plate t s := by
    simp only [scattering,Matrix.conjTranspose_mul,plate_conjTranspose,
      mul_sub,sub_mul,mul_one,mul_assoc]
    rw [← mul_assoc (plate t s) (plate t s) (absorber r τ z * plate t s),
      plate_square t s hu,one_mul]
  rw [he]
  exact hb.conjTranspose_mul_mul_same (plate t s)

theorem scattering_formula (r τ z : ℂ) (t s : ℝ) :
    scattering r τ z t s =
      !![r,0,τ*(t:ℂ),-τ*(s:ℂ);
         0,0,-z*(s:ℂ),-z*(t:ℂ);
         (t:ℂ)*τ,-(s:ℂ)*z,r*(t:ℂ)^2,-r*(t:ℂ)*(s:ℂ);
         -(s:ℂ)*τ,-(t:ℂ)*z,-r*(t:ℂ)*(s:ℂ),r*(s:ℂ)^2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [scattering,plate,absorber,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf
  all_goals tauto

theorem left_output (r τ z : ℂ) (t s : ℝ) :
    scattering r τ z t s *ᵥ left = ![0,0,-z*(s:ℂ),-z*(t:ℂ)] := by
  rw [scattering_formula]
  ext i; fin_cases i <;> simp [left,Matrix.mulVec,Fin.sum_univ_succ,dotProduct] <;> ring

theorem right_output (r τ z : ℂ) (t s : ℝ) :
    scattering r τ z t s *ᵥ right =
      ![-τ*(s:ℂ),-z*(t:ℂ),-r*(t:ℂ)*(s:ℂ),r*(s:ℂ)^2] := by
  rw [scattering_formula]
  ext i; fin_cases i <;> simp [right,Matrix.mulVec,Fin.sum_univ_succ,dotProduct]

theorem reverse_left (z : ℂ) : ChannelPowers.reverse (reference z) left = (-star z) • right := by
  ext i; fin_cases i <;> simp [ChannelPowers.reverse,reference,left,right]

theorem power_smul (c : ℂ) (u : Vec4) :
    ChannelPowers.power (c • u) = Complex.normSq c * ChannelPowers.power u := by
  simp [ChannelPowers.power,dotProduct,Fin.sum_univ_succ,
    Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

theorem left_unit : ChannelPowers.power left=1 := by
  norm_num [ChannelPowers.power,left,dotProduct,Fin.sum_univ_succ]

theorem right_unit : ChannelPowers.power right=1 := by
  norm_num [ChannelPowers.power,right,dotProduct,Fin.sum_univ_succ]

theorem power4 (u : Vec4) : ChannelPowers.power u =
    Complex.normSq (u 0)+Complex.normSq (u 1)+Complex.normSq (u 2)+Complex.normSq (u 3) := by
  simp [ChannelPowers.power,dotProduct,Fin.sum_univ_succ,Complex.normSq_apply]
  ring

theorem normSq_one (z : ℂ) (hz : star z*z=1) : Complex.normSq z=1 := by
  have h := congrArg Complex.re hz
  simpa [← Complex.normSq_eq_conj_mul_self] using h

theorem power_values (r τ z : ℂ) (t s : ℝ) (hu : t^2+s^2=1) (hz : star z*z=1) :
    ChannelPowers.absorption (scattering r τ z t s) left=0 ∧
      ChannelPowers.absorption (scattering r τ z t s) right=
        (1-t^2)*OQ7.absorptanceLeft r τ := by
  have hn := normSq_one z hz
  unfold ChannelPowers.absorption
  rw [left_output,right_output,power4,power4]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Complex.normSq_zero,Complex.normSq_neg,
    Complex.normSq_mul,Complex.normSq_ofReal,map_pow,hn]
  dsimp [OQ7.absorptanceLeft]
  constructor
  · nlinarith
  · linear_combination -(Complex.normSq τ + Complex.normSq r * (1+s^2)) * hu

theorem forward_left (r τ z : ℂ) (t s : ℝ) (hz : star z*z=1) :
    ChannelPowers.forward (scattering r τ z t s) (reference z) left = (t:ℂ) := by
  unfold ChannelPowers.forward
  rw [left_output]
  simp [reference,left,dotProduct,Fin.sum_univ_succ]
  calc
    star z*(z*(t:ℂ))=(star z*z)*(t:ℂ) := by ring
    _ = (t:ℂ) := by rw [hz,one_mul]

theorem extinction_values (r τ z : ℂ) (t s : ℝ) (hz : star z*z=1) :
    ChannelPowers.extinction (scattering r τ z t s) (reference z) left=2*(1-t) ∧
    ChannelPowers.extinction (scattering r τ z t s) (reference z)
      (ChannelPowers.reverse (reference z) left)=2*(1-t) := by
  have he : ChannelPowers.extinction (scattering r τ z t s) (reference z) left=2*(1-t) := by
    rw [ChannelPowers.extinction,forward_left r τ z t s hz,Complex.ofReal_re]
  exact ⟨he,(ChannelPowers.extinction_reciprocity _ _
    (scattering_transpose r τ z t s) (reference_transpose z) (reference_unitary z hz) left).trans he⟩

theorem reversed_absorption (r τ z : ℂ) (t s : ℝ) (hu : t^2+s^2=1) (hz : star z*z=1) :
    ChannelPowers.absorption (scattering r τ z t s)
      (ChannelPowers.reverse (reference z) left)=(1-t^2)*OQ7.absorptanceLeft r τ := by
  rw [reverse_left]
  have hn : Complex.normSq (-star z)=1 := by
    simpa using normSq_one z hz
  unfold ChannelPowers.absorption
  rw [Matrix.mulVec_smul,power_smul,hn,one_mul]
  exact (power_values r τ z t s hu hz).2

end GeneralizedResearch.PlanarFourPort
