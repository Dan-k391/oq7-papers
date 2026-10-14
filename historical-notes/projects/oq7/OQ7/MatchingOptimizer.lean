import OQ7.MatchingTarget
import OQ7.PhaseSmooth

noncomputable section
namespace OQ7
open ScalarEnvelope
open scoped Matrix Topology Matrix.Norms.Elementwise

theorem targetSheet_unitPhase {T a : ℝ} (h : ActiveTarget T a) :
    transferUnitPhase (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) = -1 :=
  triangularMatchingTransfer_unitPhase (targetSheetA_properties h).1
    (targetSheetH_pos h) (targetSheet_reflection_gap h)

theorem triangularMatchingTransfer_reflections_ne_zero {A h : ℝ}
    (hA : 0 < A) (hh : 0 < h) (hgap : h < A⁻¹ - A) :
    transferReflectionLeft (waveTransfer (triangularMatchingTransfer A h)) ≠ 0 ∧
    transferReflectionRight (waveTransfer (triangularMatchingTransfer A h)) ≠ 0 := by
  have hd := triangularMatchingTransfer_denominator_ne_zero hA hh
  have hL : ((A + h - A⁻¹) / 2 : ℝ) ≠ 0 := by linarith
  have hR : ((A - h - A⁻¹) / 2 : ℝ) ≠ 0 := by linarith
  rw [triangularMatchingTransfer_wave] at hd ⊢
  constructor
  · apply div_ne_zero _ hd
    apply neg_ne_zero.mpr
    change (((A + h - A⁻¹) / 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast hL
  · apply div_ne_zero _ hd
    change (((A - h - A⁻¹) / 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast hR

theorem targetSheet_halfAsymmetry {T a : ℝ} (h : ActiveTarget T a) :
    transferHalfAsymmetry (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) =
      x0 T a := by
  have hA := targetSheetA_properties h
  have hh := targetSheetH_pos h
  have hv := targetSheetV_gt_two h
  have hg := targetSheet_reflection_gap h
  have ht := Real.sqrt_pos.mpr h.transmission_pos
  have hts := Real.sq_sqrt h.transmission_pos.le
  have hr : 0 ≤ (targetSheetV T a) ^ 2 - 4 := by nlinarith
  have hds := Real.sq_sqrt hr
  have hden : targetSheetA T a + targetSheetH T a + (targetSheetA T a)⁻¹ =
      targetSheetV T a + targetSheetH T a := by linarith only [hA.2.2]
  have hformula : transferHalfAsymmetry
      (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) =
      targetSheetH T a * Real.sqrt ((targetSheetV T a) ^ 2 - 4) * T / 2 := by
    rw [triangularMatchingTransfer_halfAsymmetry
      (add_pos (add_pos hA.1 hh) (inv_pos.mpr hA.1)).ne',
      targetSheet_inverse_gap h, hden, targetSheetV_add_H]
    field_simp
    rw [hts]
  have hnonneg : 0 ≤ transferHalfAsymmetry
      (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) := by
    rw [hformula]
    exact div_nonneg (mul_nonneg (mul_nonneg hh.le (Real.sqrt_nonneg _))
      h.transmission_pos.le) (by norm_num)
  have hsrad : 0 ≤ 1 - 2 * a := by nlinarith [h.absorptance_lt, sq_nonneg T]
  have hss : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hsrad
  have ha : a = (1 - (s a) ^ 2) / 2 := by linarith
  have hscalar : (b T a) ^ 2 - (y0 T a) ^ 2 =
      (1 - s a) ^ 2 * ((1 + s a) ^ 2 - 4 * T) / 4 := by
    change (1 - T - a) ^ 2 - (s a - T) ^ 2 = _
    generalize s a = u at ha ⊢
    rw [ha]
    ring
  have hsquare : (transferHalfAsymmetry
      (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))) ^ 2 =
      (b T a) ^ 2 - (y0 T a) ^ 2 := by
    rw [hformula, hscalar]
    simp only [div_pow, mul_pow]
    rw [hds]
    unfold targetSheetH targetSheetV
    field_simp
    have ht4 : (Real.sqrt T) ^ 4 = T ^ 2 := by
      calc
        _ = ((Real.sqrt T) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hts]
    rw [hts, ht4]
    ring
  have hx := (active_target_properties h).2.2.2.1
  have hxs := x0_sq h
  nlinarith

theorem targetSheet_unitPhase_contDiffAt (n : WithTop ℕ∞) {T a : ℝ} (h : ActiveTarget T a) :
    ContDiffAt ℝ n transferUnitPhase
      (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) := by
  have hA := (targetSheetA_properties h).1
  have hh := targetSheetH_pos h
  have hR := triangularMatchingTransfer_reflections_ne_zero hA hh (targetSheet_reflection_gap h)
  exact transferUnitPhase_contDiffAt n _
    (triangularMatchingTransfer_denominator_ne_zero hA hh) hR.1 hR.2

#print axioms targetSheet_unitPhase
#print axioms triangularMatchingTransfer_reflections_ne_zero
#print axioms targetSheet_halfAsymmetry
#print axioms targetSheet_unitPhase_contDiffAt
end OQ7
