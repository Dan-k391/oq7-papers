import CompactMaxwell.SixVectorBridge
import CompactMaxwell.DipoleEquality

/-! The equality family in all six physical coordinates
(E_x,E_y,E_z,H_x,H_y,H_z), including both extinction endpoints. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace CompactMaxwell.SixVectorEquality
open scoped Matrix ComplexOrder
open GeneralizedResearch GeneralizedResearch.FiniteHilbertBridge WithLp
open SixVectorBridge
def M (t b : ℝ) : Mat :=
  !![1-t, -b, 0, 0, 0, 0;
     -b, 1, 0, 0, b, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, -b, 0, 0, 1-t, 0;
     0, 0, 0, 0, 0, 0]
def A (t b : ℝ) : Mat := (Complex.I / 2) • M t b
def q (t b : ℝ) : Fin 6 → ℂ := ![b, -t, 0, 0, b, 0]
def plus : Six := vector ![1, 0, 0, 0, 1, 0]
def minus : Six := vector ![1, 0, 0, 0, -1, 0]
def T (t b : ℝ) : Six →L[ℂ] Six := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) (A t b)

theorem reciprocal (t b : ℝ) : (A t b).transpose = D * A t b * D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, M, D, sign, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_six]

theorem rank_one_defect {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) :
    Q (A t b) = (1 / 4 : ℂ) • Matrix.vecMulVec (q t b) (star (q t b)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Q, imagH, A, M, q, Matrix.vecMulVec, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_six, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] <;> nlinarith

theorem passive {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) : (Q (A t b)).PosSemidef := by
  rw [rank_one_defect hb]
  exact (Matrix.posSemidef_vecMulVec_self_star (q t b)).smul
    (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 4)

theorem time_reverse : reversal.map plus = minus := by
  ext i
  fin_cases i <;> norm_num [reversal, plus, minus, vector, sign]

theorem incident_norm : ‖plus‖ ^ 2 = 2 := by
  norm_num [plus, vector, EuclideanSpace.norm_sq_eq, Fin.sum_univ_six]

theorem works (t b : ℝ) : dipoleWork (T t b) plus = 1 - t ∧
    dipoleWork (T t b) minus = 1 - t := by
  constructor <;>
    simp [dipoleWork, T, inner_coordinates, Matrix.ofLp_toEuclideanCLM, A, M,
      plus, minus, vector, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Complex.mul_im] <;> ring

theorem scatterings {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) :
    dipoleScattering (T t b) plus = (1 - t) ^ 2 / 2 ∧
    dipoleScattering (T t b) minus = 1 - t := by
  constructor <;>
    simp [dipoleScattering, T, EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM, A, M,
      plus, minus, vector, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem absorptions {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) :
    dipoleAbsorption (T t b) plus = (1 - t ^ 2) / 2 ∧
    dipoleAbsorption (T t b) minus = 0 := by
  unfold dipoleAbsorption
  rw [(works t b).1, (works t b).2, (scatterings hb).1, (scatterings hb).2]
  constructor <;> ring

theorem all_extinctions {k X : ℝ} (hk : 0 < k) (hX0 : 0 ≤ X)
    (hX1 : X ≤ 12 * Real.pi / k ^ 2) :
    ∃ B : Mat, B.transpose = D * B * D ∧ (Q B).PosSemidef ∧
      let U := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 6) B
      dipoleScale k * dipoleWork U plus = X ∧
      dipoleScale k * |dipoleAbsorption U plus - dipoleAbsorption U (reversal.map plus)| =
        X - k ^ 2 * X ^ 2 / (12 * Real.pi) := by
  let t := 1 - X / dipoleScale k
  have hc : 0 < dipoleScale k := by unfold dipoleScale; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact sub_le_self _ (div_nonneg hX0 hc.le)
  have ht0 : -1 ≤ t := by
    have h := (le_div_iff₀ (sq_pos_of_pos hk)).mp hX1
    have he : X / dipoleScale k ≤ 2 := by
      apply (div_le_iff₀ hc).mpr
      unfold dipoleScale
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (sq_pos_of_pos hk)).mpr
      nlinarith
    dsimp [t]
    linarith
  let b := Real.sqrt ((1 - t ^ 2) / 2)
  have hb : b ^ 2 = (1 - t ^ 2) / 2 := Real.sq_sqrt (by nlinarith)
  refine ⟨A t b, reciprocal t b, passive hb, ?_, ?_⟩
  · change dipoleScale k * dipoleWork (T t b) plus = X
    rw [(works t b).1]
    dsimp [t]
    field_simp
    ring
  · change dipoleScale k * |dipoleAbsorption (T t b) plus -
        dipoleAbsorption (T t b) (reversal.map plus)| = _
    rw [time_reverse, (absorptions hb).1, (absorptions hb).2, sub_zero,
      abs_of_nonneg (by nlinarith : 0 ≤ (1 - t ^ 2) / 2)]
    dsimp [t]
    unfold dipoleScale
    field_simp
    ring

end CompactMaxwell.SixVectorEquality
