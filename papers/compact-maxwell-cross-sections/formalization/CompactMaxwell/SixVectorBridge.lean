import CompactMaxwell.DipoleBound
import GeneralizedResearch.FiniteHilbertBridge

/-! The physical six-vector involution D conjugate(f), the complete matrix
passivity condition and the abstract dipole theorem are tied to one model. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace CompactMaxwell.SixVectorBridge
open scoped Matrix ComplexOrder
open GeneralizedResearch GeneralizedResearch.FiniteHilbertBridge WithLp
abbrev Six := EuclideanSpace ℂ (Fin 6)
abbrev Mat := Matrix (Fin 6) (Fin 6) ℂ
def sign (i : Fin 6) : ℝ := if i < 3 then 1 else -1
def D : Mat := Matrix.diagonal (fun i => (sign i : ℂ))

theorem sign_square (i : Fin 6) : sign i ^ 2 = 1 := by
  fin_cases i <;> norm_num [sign]

def reversal : ChannelConjugation Six where
  map f := vector (fun i => (sign i : ℂ) * star (f i))
  involution f := by
    ext i
    by_cases hi : i < 3 <;> simp [vector, sign, hi]
  inner_swap f g := by
    simp only [inner_coordinates, vector, ofLp_toLp, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    change star ((sign i : ℂ) * star (f i)) * ((sign i : ℂ) * star (g i)) = star (g i) * f i
    fin_cases i <;> simp [sign] <;> ring

theorem reversal_formula (f : Six) :
    reversal.map f = vector (D *ᵥ star (ofLp f)) := by
  ext i
  simp [reversal, vector, D, Matrix.mulVec_diagonal]

def imagH (A : Mat) : Mat := (1 / (2 * Complex.I)) • (A - A.conjTranspose)
def Q (A : Mat) : Mat := imagH A - A.conjTranspose * A

theorem matrix_reciprocity (A : Mat) (hrec : A.transpose = D * A * D) :
    channelReciprocal reversal (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A) := by
  have hentry (i j : Fin 6) : A j i = (sign i : ℂ) * A i j * (sign j : ℂ) := by
    have h := congrArg (fun B : Mat => B i j) hrec
    simpa [D, Matrix.mul_diagonal, Matrix.diagonal_mul] using h
  intro f g
  simp only [inner_coordinates, reversal, vector, ofLp_toLp, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, Pi.star_apply, star_mul, Complex.conj_ofReal, star_star]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hentry]
  have hi : star (sign i : ℂ) = (sign i : ℂ) := by simp
  have hj : star (sign j : ℂ) = (sign j : ℂ) := by simp
  rw [hi, hj]
  have hs : (sign j : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square j
  linear_combination ((sign i : ℂ) * (f j) * A i j * g i) * hs

theorem matrix_passivity (A : Mat) (hpass : (Q A).PosSemidef) (f : Six) :
    dipoleScattering (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A) f ≤ dipoleWork (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A) f := by
  have h := hpass.dotProduct_mulVec_nonneg (ofLp f)
  have hinner : (star (ofLp f) ⬝ᵥ (Q A *ᵥ ofLp f)).re =
      dipoleWork (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A) f - dipoleScattering (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A) f := by
    unfold Q imagH
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
    have ha : star (ofLp f) ⬝ᵥ (A.conjTranspose *ᵥ ofLp f) =
        star (star (ofLp f) ⬝ᵥ (A *ᵥ ofLp f)) := by
      rw [Matrix.mulVec_conjTranspose, Matrix.dotProduct_star, star_star,
        ← Matrix.dotProduct_mulVec]
    have hnorm : star (ofLp f) ⬝ᵥ ((A.conjTranspose * A) *ᵥ ofLp f) =
        inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A f) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A f) := by
      rw [inner_coordinates, Matrix.ofLp_toEuclideanCLM, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
      simp only [star_star]
    rw [Matrix.sub_mulVec, dotProduct_sub, ha, hnorm, inner_self_eq_norm_sq_to_K]
    unfold dipoleWork dipoleScattering
    rw [inner_coordinates, Matrix.ofLp_toEuclideanCLM]
    simp [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, pow_two]
    ring
  have hr := Complex.nonneg_iff.mp h
  rw [hinner] at hr
  linarith [hr.1]

theorem complete_dipole_bound (A : Mat) (hrec : A.transpose = D * A * D)
    (hpass : (Q A).PosSemidef) (f : Six) (hf : ‖f‖ ^ 2 = 2) {k : ℝ} (hk : 0 < k) :
    let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) A
    let X := dipoleScale k * dipoleWork T f
    0 ≤ X ∧ X ≤ 12 * Real.pi / k ^ 2 ∧
      |dipoleScale k * dipoleAbsorption T f - dipoleScale k * dipoleAbsorption T (reversal.map f)| ≤
        X - k ^ 2 * X ^ 2 / (12 * Real.pi) :=
  dimensional_dipole_bound reversal _ (matrix_reciprocity A hrec) (matrix_passivity A hpass) f hf hk

end CompactMaxwell.SixVectorBridge
