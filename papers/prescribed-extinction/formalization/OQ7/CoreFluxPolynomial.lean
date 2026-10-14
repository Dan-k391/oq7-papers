import OQ7.CoreAlgebra
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7.CoreConstruction
open scoped Matrix Matrix.Norms.Operator
open Filter
open scoped Topology

def quadraticFluxVariation (J : Mat2) : Mat2 := -(J.conjTranspose * fluxForm * J)

def determinantPolar (X Y : Mat2) : ℂ :=
  X 0 0 * Y 1 1 + Y 0 0 * X 1 1 - X 0 1 * Y 1 0 - Y 0 1 * X 1 0

def fluxDeterminantTail (g : ℝ) (J : Mat2) (t : ℝ) : ℂ :=
  2 * (g : ℂ) * quadraticFluxVariation J 1 1 + (linearFluxVariation g J).det +
    (t : ℂ) * determinantPolar (linearFluxVariation g J) (quadraticFluxVariation J) +
      (t : ℂ) ^ 2 * (quadraticFluxVariation J).det

theorem limitingSheet_fluxDefect_polynomial (g t : ℝ) (J : Mat2) :
    fluxDefect (limitingSheet g + t • J) =
      fluxDefect (limitingSheet g) + t • linearFluxVariation g J +
        t ^ 2 • quadraticFluxVariation J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fluxDefect, linearFluxVariation, quadraticFluxVariation,
      limitingSheet_explicit, fluxForm, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
  all_goals ring

theorem limitingSheet_fluxDeterminant_polynomial (g t : ℝ) (J : Mat2) :
    (fluxDefect (limitingSheet g + t • J)).det =
      (2 * (g : ℂ) * linearFluxVariation g J 1 1) * (t : ℂ) +
        (t : ℂ) ^ 2 * fluxDeterminantTail g J t := by
  rw [limitingSheet_fluxDefect_polynomial, limitingSheet_fluxDefect]
  unfold fluxDeterminantTail determinantPolar
  simp [Matrix.det_fin_two, Complex.real_smul]
  ring

theorem core_fluxDeterminant_polynomial {P Q g t : ℝ} (hQ : Q ≠ 0) :
    (fluxDefect (limitingSheet g + t • coreJ P Q g)).det =
      ((g : ℂ) ^ 4 / (3 * (Q : ℂ) ^ 2)) * (t : ℂ) +
        (t : ℂ) ^ 2 * fluxDeterminantTail g (coreJ P Q g) t := by
  rw [limitingSheet_fluxDeterminant_polynomial, core_linear_determinant_coefficient hQ]

theorem core_fluxDeterminant_real_polynomial {P Q g t : ℝ} (hQ : Q ≠ 0) :
    (fluxDefect (limitingSheet g + t • coreJ P Q g)).det.re =
      g ^ 4 / (3 * Q ^ 2) * t + t ^ 2 * (fluxDeterminantTail g (coreJ P Q g) t).re := by
  rw [core_fluxDeterminant_polynomial hQ]
  have he : (g : ℂ) ^ 4 / (3 * (Q : ℂ) ^ 2) = ((g ^ 4 / (3 * Q ^ 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, ← Complex.ofReal_pow]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]

theorem fluxDeterminantTail_continuous (g : ℝ) (J : Mat2) :
    Continuous (fluxDeterminantTail g J) := by
  unfold fluxDeterminantTail
  fun_prop

theorem scaled_fluxDefect_sub (F F0 : Mat2) (t : ℝ) :
    t • (fluxDefect F - fluxDefect F0) =
      -(((t • (F - F0)).conjTranspose * fluxForm * F) +
        F0.conjTranspose * fluxForm * (t • (F - F0))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fluxDefect, fluxForm, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
  all_goals ring

theorem limitingSheet_scaledFluxVariation_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → Mat2} {s : ι → ℝ} {g : ℝ} {J : Mat2}
    (hF : Tendsto F l (𝓝 (limitingSheet g)))
    (hD : Tendsto (fun x => s x • (F x - limitingSheet g)) l (𝓝 J)) :
    Tendsto (fun x => s x • (fluxDefect (F x) - fluxDefect (limitingSheet g)))
      l (𝓝 (linearFluxVariation g J)) := by
  have hc : Continuous (fun X : Mat2 => X.conjTranspose) := continuous_id.matrix_conjTranspose
  have hDs := (hc.tendsto J).comp hD
  have hSigma : Tendsto (fun _ : ι => fluxForm) l (𝓝 fluxForm) := tendsto_const_nhds
  have hF0 : Tendsto (fun _ : ι => (limitingSheet g).conjTranspose)
    l (𝓝 (limitingSheet g).conjTranspose) := tendsto_const_nhds
  have h := (((hDs.mul hSigma).mul hF).add ((hF0.mul hSigma).mul hD)).neg
  simpa only [Function.comp_apply, scaled_fluxDefect_sub, linearFluxVariation] using h

theorem limitingSheet_scaledFluxDeterminant_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → Mat2} {s : ι → ℝ} {g : ℝ} {J : Mat2}
    (hF : Tendsto F l (𝓝 (limitingSheet g)))
    (hD : Tendsto (fun x => s x • (F x - limitingSheet g)) l (𝓝 J)) :
    Tendsto (fun x => (s x : ℂ) * (fluxDefect (F x)).det)
      l (𝓝 (2 * (g : ℂ) * linearFluxVariation g J 1 1)) := by
  have hc : Continuous fluxDefect := by unfold fluxDefect; fun_prop
  have hB := (hc.tendsto (limitingSheet g)).comp hF
  have hV := limitingSheet_scaledFluxVariation_tendsto hF hD
  have h00 := (continuous_apply_apply (0 : Fin 2) (0 : Fin 2)).tendsto _ |>.comp hB
  have h01 := (continuous_apply_apply (0 : Fin 2) (1 : Fin 2)).tendsto _ |>.comp hB
  have h11 := (continuous_apply_apply (1 : Fin 2) (1 : Fin 2)).tendsto _ |>.comp hV
  have h10 := (continuous_apply_apply (1 : Fin 2) (0 : Fin 2)).tendsto _ |>.comp hV
  change Tendsto (fun x => fluxDefect (F x) 0 0) l (𝓝 (fluxDefect (limitingSheet g) 0 0)) at h00
  change Tendsto (fun x => fluxDefect (F x) 0 1) l (𝓝 (fluxDefect (limitingSheet g) 0 1)) at h01
  change Tendsto (fun x => (s x • (fluxDefect (F x) - fluxDefect (limitingSheet g))) 1 1)
    l (𝓝 (linearFluxVariation g J 1 1)) at h11
  change Tendsto (fun x => (s x • (fluxDefect (F x) - fluxDefect (limitingSheet g))) 1 0)
    l (𝓝 (linearFluxVariation g J 1 0)) at h10
  simp [limitingSheet_fluxDefect, Complex.real_smul] at h00 h01 h11 h10
  have h := (h00.mul h11).sub (h01.mul h10)
  simpa [Function.comp_def, limitingSheet_fluxDefect, Complex.real_smul,
    Matrix.det_fin_two, mul_sub, mul_left_comm, mul_assoc] using h

#print axioms limitingSheet_fluxDefect_polynomial
#print axioms limitingSheet_fluxDeterminant_polynomial
#print axioms core_fluxDeterminant_polynomial
#print axioms core_fluxDeterminant_real_polynomial
#print axioms fluxDeterminantTail_continuous
#print axioms scaled_fluxDefect_sub
#print axioms limitingSheet_scaledFluxVariation_tendsto
#print axioms limitingSheet_scaledFluxDeterminant_tendsto
end OQ7.CoreConstruction
