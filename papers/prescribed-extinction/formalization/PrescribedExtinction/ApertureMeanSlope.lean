import PrescribedExtinction.ApertureCircleParity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def apertureMeanSlope (w : ℂ → ℂ) (x : ℂ) (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, apertureCircleJet 2 w x (t * r)

def apertureMeanSlopeDeriv (w : ℂ → ℂ) (x : ℂ) (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, t • apertureCircleJet 3 w x (t * r)

theorem apertureMeanSlope_continuous (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) : Continuous (apertureMeanSlope w x) := by
  have hj := apertureCircleJet_continuous 2 w hw x
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun r t => apertureCircleJet 2 w x (t * r))
    (by fun_prop) 0 1

theorem apertureMeanSlopeDeriv_continuous (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ℂ) : Continuous (apertureMeanSlopeDeriv w x) := by
  have hj := apertureCircleJet_continuous 3 w hw x
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun r t => t • apertureCircleJet 3 w x (t * r))
    (by fun_prop) 0 1

theorem apertureMeanSlope_first_jet (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r : ℝ) :
    r • apertureMeanSlope w x r = apertureCircleJet 1 w x r := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := r) (f := apertureCircleJet 1 w x) (f' := apertureCircleJet 2 w x)
    (fun t _ => apertureCircleJet_hasDerivAt 1 w hw hc x t)
    ((apertureCircleJet_continuous 2 w hw x).intervalIntegrable 0 r)
  rw [apertureCircleJet_first_zero w hw hc x, sub_zero] at he
  have hs := intervalIntegral.smul_integral_comp_mul_right (apertureCircleJet 2 w x) (a := 0) (b := 1) r
  simp only [zero_mul, one_mul] at hs
  exact hs.trans he

theorem apertureMeanSlope_norm_le (w : ℂ → ℂ) (x : ℂ) (r C : ℝ)
    (hC : ∀ y, ‖iteratedFDeriv ℝ 2 w y‖ ≤ C) : ‖apertureMeanSlope w x r‖ ≤ C := by
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := C) (f := fun t => apertureCircleJet 2 w x (t * r))
    (fun t _ => apertureCircleJet_norm_le 2 w x (t * r) C hC)
  simpa only [apertureMeanSlope, sub_zero, abs_one, mul_one] using he

theorem apertureMeanSlopeDeriv_norm_le (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r C : ℝ)
    (hr : 0 ≤ r) (hC : ∀ y, ‖iteratedFDeriv ℝ 4 w y‖ ≤ C) :
    ‖apertureMeanSlopeDeriv w x r‖ ≤ C * r / 3 := by
  have he := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun t => t • apertureCircleJet 3 w x (t * r))
    (g := fun t => C * r * t ^ 2) (by norm_num)
    (ae_of_all _ (fun t ht => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      calc
        _ ≤ t * (C * (t * r)) := mul_le_mul_of_nonneg_left
          (apertureCircleJet_third_norm_le w hw hc x (t * r) C (mul_nonneg ht.1.le hr) hC) ht.1.le
        _ = _ := by ring))
    ((show Continuous (fun t : ℝ => C * r * t ^ 2) by fun_prop).intervalIntegrable 0 1)
  change ‖apertureMeanSlopeDeriv w x r‖ ≤ ∫ t in (0 : ℝ)..1, C * r * t ^ 2 at he
  norm_num [intervalIntegral.integral_const_mul] at he
  simpa only [one_mul, div_eq_mul_inv] using he

theorem apertureMeanSlope_hasDerivAt (w : ℂ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w) (x : ℂ) (r : ℝ) :
    HasDerivAt (apertureMeanSlope w x) (apertureMeanSlopeDeriv w x r) r := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_bound_iteratedFDeriv hw 3
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have h2 : Continuous (apertureCircleJet 2 w x) := apertureCircleJet_continuous 2 w hw x
  have h3 : Continuous (apertureCircleJet 3 w x) := apertureCircleJet_continuous 3 w hw x
  have hF (v : ℝ) : Continuous (fun t => apertureCircleJet 2 w x (t * v)) :=
    h2.comp (continuous_id.mul continuous_const)
  have hG (v : ℝ) : Continuous (fun t : ℝ => t • apertureCircleJet 3 w x (t * v)) :=
    continuous_id.smul (h3.comp (continuous_id.mul continuous_const))
  have hbound : ∀ᵐ t ∂μ, ∀ v ∈ univ, ‖t • apertureCircleJet 3 w x (t * v)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro v _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_left (apertureCircleJet_norm_le 3 w x (t * v) C (hC 3 le_rfl))
      ht.1.le).trans (by nlinarith [ht.2])
  have hdiff (v t : ℝ) : HasDerivAt (fun y => apertureCircleJet 2 w x (t * y))
      (t • apertureCircleJet 3 w x (t * v)) v := by
    simpa [Function.comp_def] using
      (apertureCircleJet_hasDerivAt 2 w hw hc x (t * v)).scomp v ((hasDerivAt_id v).const_mul t)
  have hp := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := univ) (x₀ := r) (bound := fun _ => C)
    (F := fun v t => apertureCircleJet 2 w x (t * v))
    (F' := fun v t => t • apertureCircleJet 3 w x (t * v))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun v => (hF v).measurable.aestronglyMeasurable))
    ((hF r).intervalIntegrable 0 1).1
    (hG r).measurable.aestronglyMeasurable hbound (integrable_const C)
    (ae_of_all μ (fun t v _ => hdiff v t))
  have hf : apertureMeanSlope w x = fun v => ∫ t, apertureCircleJet 2 w x (t * v) ∂μ := by
    funext v
    rw [apertureMeanSlope, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hf]
  convert hp.2 using 1
  rw [apertureMeanSlopeDeriv, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

end OQ7Prescribed
