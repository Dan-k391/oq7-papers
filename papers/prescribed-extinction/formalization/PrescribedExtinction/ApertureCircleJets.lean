import PrescribedExtinction.ApertureOscillation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def apertureCircleDirection (θ : ℝ) : ℂ := circleMap 0 1 θ

theorem apertureCircleDirection_norm (θ : ℝ) : ‖apertureCircleDirection θ‖ = 1 := by
  simp [apertureCircleDirection]

@[fun_prop] theorem apertureCircleDirection_continuous : Continuous apertureCircleDirection := by
  unfold apertureCircleDirection
  fun_prop

def apertureDirectionalJet (n : ℕ) (w : ℂ → ℂ) (x : ℂ) (r θ : ℝ) : ℂ :=
  iteratedFDeriv ℝ n w (x + r • apertureCircleDirection θ) (fun _ => apertureCircleDirection θ)

def apertureCircleJet (n : ℕ) (w : ℂ → ℂ) (x : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, apertureDirectionalJet n w x r θ

theorem apertureDirectionalJet_continuous (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) :
    Continuous (fun p : ℝ × ℝ => apertureDirectionalJet n w x p.1 p.2) := by
  have hn : Continuous (iteratedFDeriv ℝ n w) := hw.continuous_iteratedFDeriv (m := n) (by simp)
  unfold apertureDirectionalJet
  fun_prop

theorem apertureDirectionalJet_hasDerivAt (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t => apertureDirectionalJet n w x t θ)
      (apertureDirectionalJet (n + 1) w x r θ) r := by
  have hn : Differentiable ℝ (iteratedFDeriv ℝ n w) :=
    hw.differentiable_iteratedFDeriv (m := n) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have he := (hn (x + r • apertureCircleDirection θ)).hasFDerivAt.continuousMultilinear_apply_const
    (fun _ => apertureCircleDirection θ)
  have hl : HasDerivAt (fun t : ℝ => x + t • apertureCircleDirection θ) (apertureCircleDirection θ) r :=
    by simpa only [one_smul, id_eq] using
      ((hasDerivAt_id r).smul_const (apertureCircleDirection θ)).const_add x
  convert he.comp_hasDerivAt r hl using 1
  · rfl
  · exact iteratedFDeriv_succ_apply_left (fun _ => apertureCircleDirection θ)

theorem apertureDirectionalJet_norm_le (n : ℕ) (w : ℂ → ℂ) (x : ℂ) (r θ C : ℝ)
    (hC : ∀ y, ‖iteratedFDeriv ℝ n w y‖ ≤ C) :
    ‖apertureDirectionalJet n w x r θ‖ ≤ C := by
  have hn := (iteratedFDeriv ℝ n w (x + r • apertureCircleDirection θ)).le_opNorm
    (fun _ => apertureCircleDirection θ)
  simpa only [apertureDirectionalJet, apertureCircleDirection_norm, Finset.prod_const_one, mul_one] using hn.trans
    (mul_le_mul_of_nonneg_right (hC _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem apertureCircleJet_zero (w : ℂ → ℂ) (x : ℂ) (r : ℝ) :
    apertureCircleJet 0 w x r = Real.circleAverage w x r := by
  unfold apertureCircleJet Real.circleAverage apertureDirectionalJet apertureCircleDirection
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp [circleMap, Complex.real_smul]

theorem apertureCircleJet_continuous (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) : Continuous (apertureCircleJet n w x) := by
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun r θ => apertureDirectionalJet n w x r θ)
    (μ := volume)
    (apertureDirectionalJet_continuous n w hw x) 0 (2 * Real.pi)).const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem apertureCircleJet_hasDerivAt (n : ℕ) (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r : ℝ) :
    HasDerivAt (apertureCircleJet n w x) (apertureCircleJet (n + 1) w x r) r := by
  obtain ⟨C, _, hC⟩ := hc.exists_bound_iteratedFDeriv hw (n + 1)
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  have hcn (j : ℕ) (t : ℝ) : Continuous (fun θ => apertureDirectionalJet j w x t θ) :=
    (apertureDirectionalJet_continuous j w hw x).comp (continuous_const.prodMk continuous_id)
  have hp := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := univ) (x₀ := r) (bound := fun _ => C)
    (F := fun t θ => apertureDirectionalJet n w x t θ)
    (F' := fun t θ => apertureDirectionalJet (n + 1) w x t θ)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun t => (hcn n t).measurable.aestronglyMeasurable))
    ((hcn n r).intervalIntegrable 0 (2 * Real.pi)).1
    (hcn (n + 1) r).measurable.aestronglyMeasurable
    (ae_of_all μ (fun θ t _ => apertureDirectionalJet_norm_le (n + 1) w x t θ C (hC _ le_rfl)))
    (integrable_const C)
    (ae_of_all μ (fun θ t _ => apertureDirectionalJet_hasDerivAt n w hw x t θ))
  have he := hp.2.const_smul ((2 * Real.pi)⁻¹)
  have hf : apertureCircleJet n w x = fun t =>
      (2 * Real.pi)⁻¹ • ∫ θ, apertureDirectionalJet n w x t θ ∂μ := by
    funext t
    rw [apertureCircleJet, intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi)]
  rw [hf]
  convert he using 1
  rw [apertureCircleJet, intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi)]

theorem apertureCircleJet_norm_le (n : ℕ) (w : ℂ → ℂ) (x : ℂ) (r C : ℝ)
    (hC : ∀ y, ‖iteratedFDeriv ℝ n w y‖ ≤ C) : ‖apertureCircleJet n w x r‖ ≤ C := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi) (C := C)
    (f := fun θ => apertureDirectionalJet n w x r θ)
    (fun θ _ => apertureDirectionalJet_norm_le n w x r θ C hC)
  simp only [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hi
  rw [apertureCircleJet, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = C := by field_simp

end OQ7Prescribed
