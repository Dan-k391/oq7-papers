import OQ7.Phase
import OQ7.MatchingSheet
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7
open Filter
open scoped Topology Matrix.Norms.Elementwise

def transferUnitPhase (F : Mat2) : ℂ :=
  unitPhase (transferReflectionLeft (waveTransfer F))
    (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))

def transferHalfAsymmetry (F : Mat2) : ℝ :=
  halfAsymmetry (transferReflectionLeft (waveTransfer F))
    (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))

theorem unitPhase_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f g t : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (ht : ContDiffAt ℝ n t x)
    (hfx : f x ≠ 0) (hgx : g x ≠ 0) (htx : t x ≠ 0) :
    ContDiffAt ℝ n (fun y => unitPhase (f y) (g y) (t y)) x := by
  have hfg := hf.mul hg
  have hns := (matching_complex_normSq_contDiff n).contDiffAt.comp x hfg
  have hnorm : ContDiffAt ℝ n (fun y => ‖f y * g y‖) x := by
    convert hns.sqrt (Complex.normSq_pos.mpr (mul_ne_zero hfx hgx)).ne' using 1
    ext y
    exact (RCLike.sqrt_normSq_eq_norm (z := f y * g y)).symm
  have htn := (matching_complex_normSq_contDiff n).contDiffAt.comp x ht
  have hdenR := htn.mul hnorm
  have hden := (matching_complex_ofReal_contDiff n).contDiffAt.comp x hdenR
  have hden0 : ((transmissionPower (t x) * ‖f x * g x‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (phase_denominator_pos hfx hgx htx).ne'
  have hstar : ContDiffAt ℝ n (fun y => star (t y)) x := by
    simpa only [RCLike.conjCLE_apply, Function.comp_def, Complex.star_def] using
      (RCLike.conjCLE (K := ℂ)).contDiff.contDiffAt.comp x ht
  unfold unitPhase phaseProduct transmissionPower
  simpa only [div_eq_mul_inv] using! (hfg.mul (hstar.pow 2)).mul (hden.inv hden0)

theorem transferUnitPhase_contDiffAt (n : WithTop ℕ∞) (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0)
    (hL : transferReflectionLeft (waveTransfer F) ≠ 0)
    (hR : transferReflectionRight (waveTransfer F) ≠ 0) :
    ContDiffAt ℝ n transferUnitPhase F := by
  have hw := (waveTransfer_contDiff n).contDiffAt (x := F)
  have he (i j : Fin 2) : ContDiffAt ℝ n (fun X : Mat2 => waveTransfer X i j) F :=
    (contDiff_apply_apply ℝ ℂ i j).contDiffAt.comp F hw
  have hdivide {f : Mat2 → ℂ} (hf : ContDiffAt ℝ n f F) :
      ContDiffAt ℝ n (fun X => f X / waveTransfer X 1 1) F := by
    simpa only [div_eq_mul_inv] using! hf.mul ((he 1 1).inv hd)
  exact unitPhase_contDiffAt (hdivide (he 1 0).neg) (hdivide (he 0 1))
    (hdivide (contDiffAt_const (c := (1 : ℂ)))) hL hR (one_div_ne_zero hd)

theorem transferHalfAsymmetry_contDiffAt (n : WithTop ℕ∞) (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0) : ContDiffAt ℝ n transferHalfAsymmetry F := by
  have hw := (waveTransfer_contDiff n).contDiffAt (x := F)
  have he (i j : Fin 2) : ContDiffAt ℝ n (fun X : Mat2 => waveTransfer X i j) F :=
    (contDiff_apply_apply ℝ ℂ i j).contDiffAt.comp F hw
  have hdivide {f : Mat2 → ℂ} (hf : ContDiffAt ℝ n f F) :
      ContDiffAt ℝ n (fun X => f X / waveTransfer X 1 1) F := by
    simpa only [div_eq_mul_inv] using! hf.mul ((he 1 1).inv hd)
  have hn (f : Mat2 → ℂ) (hf : ContDiffAt ℝ n f F) :
      ContDiffAt ℝ n (fun X => Complex.normSq (f X)) F :=
    (matching_complex_normSq_contDiff n).contDiffAt.comp F hf
  have hL := hn _ (hdivide (he 1 0).neg)
  have hR := hn _ (hdivide (he 0 1))
  unfold transferHalfAsymmetry halfAsymmetry absorptanceLeft absorptanceRight
  convert (hR.sub hL).div_const 2 using 1
  ext X
  unfold transferReflectionLeft transferReflectionRight
  ring

theorem unitPhase_real_opposite {p r t : ℝ} (hp : 0 < p) (hr : 0 < r) (ht : 0 < t) :
    unitPhase (p : ℂ) (-(r : ℂ)) (t : ℂ) = -1 := by
  have hn : ‖(p : ℂ) * -(r : ℂ)‖ = p * r := by
    rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp, abs_of_pos hr]
  unfold unitPhase phaseProduct transmissionPower
  rw [hn]
  simp only [Complex.normSq_ofReal, Complex.star_def, Complex.conj_ofReal]
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp

theorem triangularMatchingTransfer_halfAsymmetry {A h : ℝ}
    (hd : A + h + A⁻¹ ≠ 0) :
    transferHalfAsymmetry (triangularMatchingTransfer A h) =
      2 * h * (A⁻¹ - A) / (A + h + A⁻¹) ^ 2 := by
  unfold transferHalfAsymmetry
  rw [triangularMatchingTransfer_wave]
  unfold halfAsymmetry absorptanceLeft absorptanceRight
  simp only [transferReflectionLeft, transferReflectionRight, transferTransmissionRight,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.normSq_neg, Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
  generalize A⁻¹ = z at *
  field_simp
  ring

theorem triangularMatchingTransfer_unitPhase {A h : ℝ}
    (hA : 0 < A) (hh : 0 < h) (hgap : h < A⁻¹ - A) :
    transferUnitPhase (triangularMatchingTransfer A h) = -1 := by
  have hd : 0 < A + h + A⁻¹ := by positivity
  have hL : 0 < (A⁻¹ - A - h) / (A + h + A⁻¹) := by apply div_pos _ hd; linarith
  have hR : 0 < (A⁻¹ - A + h) / (A + h + A⁻¹) := by apply div_pos _ hd; linarith
  have ht : 0 < 2 / (A + h + A⁻¹) := div_pos (by norm_num) hd
  have hu := unitPhase_real_opposite hL hR ht
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  unfold transferUnitPhase
  rw [triangularMatchingTransfer_wave]
  convert hu using 1
  all_goals
    simp only [transferReflectionLeft, transferReflectionRight, transferTransmissionRight,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals congr 1 <;> push_cast <;> field_simp [hAc] <;> ring

#print axioms unitPhase_contDiffAt
#print axioms transferUnitPhase_contDiffAt
#print axioms transferHalfAsymmetry_contDiffAt
#print axioms unitPhase_real_opposite
#print axioms triangularMatchingTransfer_halfAsymmetry
#print axioms triangularMatchingTransfer_unitPhase
end OQ7
