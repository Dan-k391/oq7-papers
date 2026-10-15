import CompactMaxwell.DipoleBound
import GeneralizedResearch.FiniteHilbertBridge

/-! Literal active coordinates (E_x,H_y,E_y) of the equality tensor. All matrix
entries, loss defect and both illumination powers are checked symbolically. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace CompactMaxwell.DipoleEquality
open scoped Matrix ComplexOrder
open GeneralizedResearch
abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ
def M (t b : ℝ) : Mat := !![1-t, 0, -b; 0, 1-t, -b; -b, b, 1]
def A (t b : ℝ) : Mat := (Complex.I / 2) • M t b
def D : Mat := Matrix.diagonal ![1, -1, 1]
def q (t b : ℝ) : Fin 3 → ℂ := ![b, b, -t]
def imagH (B : Mat) : Mat := (1 / (2 * Complex.I)) • (B - B.conjTranspose)
def defect (t b : ℝ) : Mat := imagH (A t b) - (A t b).conjTranspose * A t b
def plus : Fin 3 → ℂ := ![1, 1, 0]
def minus : Fin 3 → ℂ := ![1, -1, 0]
def work (B : Mat) (f : Fin 3 → ℂ) : ℝ := (star f ⬝ᵥ (B *ᵥ f)).im
def power (B : Mat) (f : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq ((B *ᵥ f) i)

theorem reciprocal (t b : ℝ) : (A t b).transpose = D * A t b * D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, M, D, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_three] <;> ring

theorem rank_one_defect {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) :
    defect t b = (1 / 4 : ℂ) • Matrix.vecMulVec (q t b) (star (q t b)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [defect, imagH, A, M, q, Matrix.vecMulVec, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] <;> nlinarith

theorem passive {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) : (defect t b).PosSemidef := by
  rw [rank_one_defect hb]
  have h : (Matrix.vecMulVec (q t b) (star (q t b))).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  exact h.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 4)

theorem forward_works (t b : ℝ) :
    work (A t b) plus = 1 - t ∧ work (A t b) minus = 1 - t := by
  constructor <;>
    simp [work, A, M, plus, minus, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem scattered_powers {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) :
    power (A t b) plus = (1 - t) ^ 2 / 2 ∧ power (A t b) minus = 1 - t := by
  constructor <;>
    simp [power, A, M, plus, minus, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    nlinarith

theorem absorption_powers {t b : ℝ} (hb : b ^ 2 = (1 - t ^ 2) / 2) :
    work (A t b) plus - power (A t b) plus = (1 - t ^ 2) / 2 ∧
    work (A t b) minus - power (A t b) minus = 0 := by
  rw [(forward_works t b).1, (forward_works t b).2,
    (scattered_powers hb).1, (scattered_powers hb).2]
  constructor <;> ring

theorem saturates_dimensional_parabola {t b k : ℝ}
    (hb : b ^ 2 = (1 - t ^ 2) / 2) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) (hk : 0 < k) :
    let X := dipoleScale k * work (A t b) plus
    let Δ := dipoleScale k * |(work (A t b) plus - power (A t b) plus) -
      (work (A t b) minus - power (A t b) minus)|
    Δ = X - k ^ 2 * X ^ 2 / (12 * Real.pi) := by
  dsimp only
  rw [(absorption_powers hb).1, (absorption_powers hb).2, sub_zero,
    (forward_works t b).1, abs_of_nonneg (by nlinarith : 0 ≤ (1 - t ^ 2) / 2)]
  unfold dipoleScale
  field_simp
  ring

def N (a : ℝ) : Mat := !![(a^2 : ℝ), (-a^2/2 : ℝ), -a; (a^2/2 : ℝ), 0, -a; -a, a, 1]
def v (a : ℝ) : Fin 3 → ℂ := ![a, 0, -1]

theorem bare_loss (a : ℝ) : imagH (Complex.I • N a) =
    Matrix.vecMulVec (v a) (star (v a)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [imagH, N, v, Matrix.vecMulVec, Matrix.conjTranspose_apply,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, pow_two] <;> ring

theorem dressing_equation {t b a : ℝ} (hab : a * b = 1 - t)
    (hb : b = a * (1 + t) / 2) (ha : a ^ 2 * (1 + t) = 2 * (1 - t)) :
    M t b * (1 + N a) = 2 • N a := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [M, N, Matrix.mul_apply, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
      nlinarith [congrArg (fun r : ℝ => a * r) hab]

end CompactMaxwell.DipoleEquality
