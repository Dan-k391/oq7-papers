import GeneralizedResearch.FiniteHilbertBridge

/-! Exact rational tensor and static response in Theorem 7.1. This checks
the coefficient algebra and loss floor, not the dynamic small-radius remainder. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace FixedResource.SphereAlgebra
open scoped Matrix
abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ
def chi : Mat := !![1+Complex.I/2, Complex.I/5, 0;
  Complex.I/5, 2+Complex.I/2, 0; 0, 0, 1+Complex.I/2]
def d : ℂ := (1979 + 450 * Complex.I) / 100
def L : Mat := !![3-9*(5+Complex.I/2)/d, 9*Complex.I/(5*d), 0;
  9*Complex.I/(5*d), 3-9*(4+Complex.I/2)/d, 0; 0, 0, 3-9/(4+Complex.I/2)]
def plus : Fin 3 → ℂ := ![1, Complex.I, 0]
def minus : Fin 3 → ℂ := ![1, -Complex.I, 0]
def quad (M : Mat) (v : Fin 3 → ℂ) : ℂ := star v ⬝ᵥ (M *ᵥ v)
def power (v : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem reciprocal : chi.transpose = chi := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem static_response : (chi + (3 : ℂ) • (1 : Mat)) * L = (3 : ℂ) • chi := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [chi, L, d, Matrix.mul_apply, Fin.sum_univ_three,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
      Matrix.ofNat_apply]

theorem static_extinction_coefficient : (quad L plus).im / 2 = 931950 / 4118941 := by
  norm_num [quad, L, d, plus, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]

theorem static_scattering_difference :
    (power (L *ᵥ plus) - power (L *ᵥ minus)) / 2 = 324000 / 4118941 := by
  norm_num [power, L, d, plus, minus, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem normalized_coefficient :
    ((power (L *ᵥ plus) - power (L *ᵥ minus)) / 2) / ((quad L plus).im / 2) = 720 / 2071 ∧
    (2 / 9 : ℝ) * (720 / 2071) = 160 / 2071 := by
  rw [static_scattering_difference, static_extinction_coefficient]
  norm_num

theorem loss_decomposition (v : Fin 3 → ℂ) :
    (quad chi v).im = 3 / 10 * (Complex.normSq (v 0) + Complex.normSq (v 1)) +
      1 / 5 * Complex.normSq (v 0 + v 1) + 1 / 2 * Complex.normSq (v 2) := by
  simp [quad, chi, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  ring

theorem loss_floor (v : Fin 3 → ℂ) : 3 / 10 * power v ≤ (quad chi v).im := by
  rw [loss_decomposition]
  simp only [power, Fin.sum_univ_three]
  nlinarith [Complex.normSq_nonneg (v 2), Complex.normSq_nonneg (v 0 + v 1)]

theorem loss_upper (v : Fin 3 → ℂ) : (quad chi v).im ≤ 7 / 10 * power v := by
  have he : (quad chi v).im = 7 / 10 * (Complex.normSq (v 0) + Complex.normSq (v 1)) -
      1 / 5 * Complex.normSq (v 0 - v 1) + 1 / 2 * Complex.normSq (v 2) := by
    simp [quad, chi, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.normSq_apply,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [he]
  simp only [power, Fin.sum_univ_three]
  nlinarith [Complex.normSq_nonneg (v 2), Complex.normSq_nonneg (v 0 - v 1)]

theorem real_permittivity (v : Fin 3 → ℂ) :
    power v ≤ (quad (1 + chi) v).re ∧ (quad (1 + chi) v).re ≤ 3 * power v := by
  have he : (quad (1 + chi) v).re =
      2 * Complex.normSq (v 0) + 3 * Complex.normSq (v 1) + 2 * Complex.normSq (v 2) := by
    simp [quad, chi, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.normSq_apply,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [he]
  simp only [power, Fin.sum_univ_three]
  constructor <;> nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1),
    Complex.normSq_nonneg (v 2)]

end FixedResource.SphereAlgebra
