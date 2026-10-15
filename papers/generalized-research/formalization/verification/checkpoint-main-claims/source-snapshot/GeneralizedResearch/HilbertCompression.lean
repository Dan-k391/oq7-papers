import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

/-! Exact two-dimensional real compression in an arbitrary Hilbert space.
The positive slack is the Gram matrix of actual projection residuals. -/

noncomputable section
namespace GeneralizedResearch
namespace HilbertCompression
open scoped Matrix
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def B (u v : Fin 2 → H) : Mat2 := fun i j => inner ℝ (u i) (v j)
def residual (u v : Fin 2 → H) (j : Fin 2) : H :=
  v j - ((B u v 0 j) • u 0 + (B u v 1 j) • u 1)

theorem residual_gram (u v : Fin 2 → H) (hu : Orthonormal ℝ u) :
    Matrix.gram ℝ (residual u v) = Matrix.gram ℝ v - (B u v).transpose * B u v := by
  have hoo := orthonormal_iff_ite.mp hu
  have h00 : inner ℝ (u 0) (u 0) = 1 := by simpa using hoo 0 0
  have h01 : inner ℝ (u 0) (u 1) = 0 := by simpa using hoo 0 1
  have h10 : inner ℝ (u 1) (u 0) = 0 := by simpa using hoo 1 0
  have h11 : inner ℝ (u 1) (u 1) = 1 := by simpa using hoo 1 1
  ext i j
  simp only [Matrix.gram_apply, residual, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [h00, h01, h10, h11]
  simp only [B]
  rw [real_inner_comm (v i) (u 0), real_inner_comm (v i) (u 1)]
  ring

theorem projection_gap_posSemidef (u v : Fin 2 → H) (hu : Orthonormal ℝ u) :
    (Matrix.gram ℝ v - (B u v).transpose * B u v).PosSemidef := by
  rw [← residual_gram u v hu]
  exact Matrix.posSemidef_gram ℝ _

theorem symmetric_projection_gap_posSemidef (u v : Fin 2 → H)
    (hu : Orthonormal ℝ u) (hB : (B u v).IsHermitian) :
    (Matrix.gram ℝ v - B u v ^ 2).PosSemidef := by
  have ht : (B u v).transpose = B u v := by simpa using hB.eq
  simpa only [ht, pow_two] using projection_gap_posSemidef u v hu

theorem contraction_gram_posSemidef (u : Fin 2 → H) (hu : Orthonormal ℝ u)
    (T : H →L[ℝ] H) (hT : ‖T‖ ≤ 1) :
    ((1 : Mat2) - Matrix.gram ℝ (T ∘ u)).PosSemidef := by
  have hgram : Matrix.gram ℝ u = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr hu
  have hg := Matrix.posSemidef_opNorm_smul_gram_sub_gram u T
  rw [hgram] at hg
  have hc : 0 ≤ 1 - ‖T‖ ^ 2 := by nlinarith [norm_nonneg T]
  have hs : ((1 - ‖T‖ ^ 2) • (1 : Mat2)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  have h := hs.add hg
  convert h using 1
  ext i j
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  ring

end HilbertCompression
end GeneralizedResearch
