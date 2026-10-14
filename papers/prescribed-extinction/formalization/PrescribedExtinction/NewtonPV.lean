import PrescribedExtinction.NewtonBoundary
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual classical Newton Hessian and its angular cancellation under
polar change of variables. No identification with distributional derivatives
is assumed. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology NNReal

def newtonHessianKernel (i j : Fin 3) (x : Position) : ℝ :=
  (3 * x i * x j - ‖x‖ ^ 2 * (if i = j then 1 else 0)) / (4 * Real.pi * ‖x‖ ^ 5)

theorem newtonHessianKernel_classical (i j : Fin 3) (x : Position) (hx : x ≠ 0) :
    (newtonHessianKernel i j x : ℂ) =
      lineDeriv ℝ (fun y : Position => lineDeriv ℝ (outgoingGreen 0) y (basisR j)) x (basisR i) :=
  (newton_classical_hessian x hx i j).symm

theorem newtonHessianKernel_smul (i j : Fin 3) (n : UnitSphere) (r : ℝ) (hr : 0 < r) :
    newtonHessianKernel i j (r • (n : Position)) =
      (3 * (n : Position) i * (n : Position) j - (if i = j then 1 else 0)) /
        (4 * Real.pi * r ^ 3) := by
  simp only [newtonHessianKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    unitSphere_norm, mul_one, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> field_simp

theorem integral_polar_actual (f : Position → ℝ) :
    (∫ x, f x) = ∫ p : UnitSphere × Ioi (0 : ℝ), f (p.2.1 • (p.1 : Position))
      ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
  calc
    _ = ∫ x : ({(0 : Position)}ᶜ : Set Position), f x ∂((volume : Measure Position).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure Position).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd Position))
        (fun p => f (((homeomorphUnitSphereProd Position).symm p : ({(0 : Position)}ᶜ : Set Position)) : Position))
      simpa [sphereArea, Position, homeomorphUnitSphereProd_symm_apply_coe] using h

theorem newtonHessian_radial_integral_zero (i j : Fin 3) (w : ℝ → ℝ) :
    (∫ x : Position, w ‖x‖ * newtonHessianKernel i j x) = 0 := by
  rw [integral_polar_actual]
  have he : (fun p : UnitSphere × Ioi (0 : ℝ) =>
      w ‖p.2.1 • (p.1 : Position)‖ * newtonHessianKernel i j (p.2.1 • (p.1 : Position))) =
      (fun p => (3 * (p.1 : Position) i * (p.1 : Position) j - (if i = j then 1 else 0)) *
        (w p.2.1 / (4 * Real.pi * p.2.1 ^ 3))) := by
    funext p
    rw [newtonHessianKernel_smul i j p.1 p.2.1 p.2.2]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (mem_Ioi.mp p.2.2), unitSphere_norm, mul_one]
    ring
  rw [he]
  have h := integral_prod_mul (μ := sphereArea) (ν := Measure.volumeIoiPow 2)
    (fun n : UnitSphere => 3 * (n : Position) i * (n : Position) j - (if i = j then 1 else 0))
    (fun r : Ioi (0 : ℝ) => w r / (4 * Real.pi * (r : ℝ) ^ 3))
  exact h.trans (by rw [sphere_newton_angular_cancellation, zero_mul])

theorem newtonHessianKernel_measurable (i j : Fin 3) : Measurable (newtonHessianKernel i j) := by
  unfold newtonHessianKernel
  fun_prop

theorem newtonHessianKernel_norm_le (i j : Fin 3) (x : Position) :
    ‖newtonHessianKernel i j x‖ ≤ Real.pi⁻¹ * ‖x‖⁻¹ ^ 3 := by
  by_cases hx : x = 0
  · subst x; simp [newtonHessianKernel]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi := PiLp.norm_apply_le x i
  have hj := PiLp.norm_apply_le x j
  have hp : |x i| * |x j| ≤ ‖x‖ * ‖x‖ :=
    mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
  have hδ : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  have hNum : |3 * x i * x j - ‖x‖ ^ 2 * (if i = j then 1 else 0)| ≤ 4 * ‖x‖ ^ 2 := by
    calc
      _ ≤ |3 * x i * x j| + |‖x‖ ^ 2 * (if i = j then (1 : ℝ) else 0)| := abs_sub _ _
      _ = 3 * (|x i| * |x j|) + ‖x‖ ^ 2 * |(if i = j then (1 : ℝ) else 0)| := by
        split_ifs <;> simp [abs_mul, mul_assoc]
      _ ≤ 3 * (‖x‖ * ‖x‖) + ‖x‖ ^ 2 * 1 := by gcongr
      _ = _ := by ring
  calc
    _ = |3 * x i * x j - ‖x‖ ^ 2 * (if i = j then (1 : ℝ) else 0)| /
        (4 * Real.pi * ‖x‖ ^ 5) := by
          simp [newtonHessianKernel, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ (4 * ‖x‖ ^ 2) / (4 * Real.pi * ‖x‖ ^ 5) :=
      div_le_div_of_nonneg_right hNum (by positivity)
    _ = _ := by field_simp

theorem scalarTest_global_lipschitz (φ : ScalarTest) :
    ∃ L : ℝ≥0, LipschitzWith L (φ : Position → ℝ) := by
  have hc : Continuous (fderiv ℝ (φ : Position → ℝ)) := φ.contDiff.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (φ.contDiff.differentiable (by norm_num)) ?_⟩
  intro x
  exact_mod_cast (hC x).trans (Real.le_coe_toNNReal C)

end OQ7Prescribed
