import OQ7.MatchingSheet
import OQ7.Envelope
import OQ7.CoreAlgebra

noncomputable section
namespace OQ7
open ScalarEnvelope
open scoped Matrix Topology Matrix.Norms.Elementwise

def smallSheetRoot (v : ℝ) : ℝ := (v - Real.sqrt (v ^ 2 - 4)) / 2
def targetSheetV (T a : ℝ) : ℝ := (1 + s a) / Real.sqrt T
def targetSheetH (T a : ℝ) : ℝ := (1 - s a) / Real.sqrt T
def targetSheetA (T a : ℝ) : ℝ := smallSheetRoot (targetSheetV T a)

theorem smallSheetRoot_properties {v : ℝ} (hv : 2 < v) :
    0 < smallSheetRoot v ∧ smallSheetRoot v < 1 ∧
      smallSheetRoot v + (smallSheetRoot v)⁻¹ = v := by
  have hr : 0 < v ^ 2 - 4 := by nlinarith
  have hd := Real.sqrt_nonneg (v ^ 2 - 4)
  have hds := Real.sq_sqrt hr.le
  have hless : Real.sqrt (v ^ 2 - 4) < v := by nlinarith
  have hmore : v - 2 < Real.sqrt (v ^ 2 - 4) := by
    nlinarith [sq_nonneg (Real.sqrt (v ^ 2 - 4) - (v - 2))]
  have hA : 0 < smallSheetRoot v := by unfold smallSheetRoot; linarith
  have hA1 : smallSheetRoot v < 1 := by unfold smallSheetRoot; linarith
  have hp : smallSheetRoot v * (v - smallSheetRoot v) = 1 := by
    unfold smallSheetRoot
    nlinarith
  have hinv : (smallSheetRoot v)⁻¹ = v - smallSheetRoot v := by
    rw [inv_eq_one_div]
    apply (div_eq_iff hA.ne').mpr
    nlinarith only [hp]
  exact ⟨hA, hA1, by rw [hinv]; ring⟩

theorem active_target_s_lt_one {T a : ℝ} (h : ActiveTarget T a) : s a < 1 := by
  have hs := (active_target_properties h).1
  have hr : 0 ≤ 1 - 2 * a := by nlinarith [h.absorptance_lt, sq_nonneg T]
  have hsq : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hr
  nlinarith [h.absorptance_pos]

theorem targetSheetV_gt_two {T a : ℝ} (h : ActiveTarget T a) : 2 < targetSheetV T a := by
  have ht := Real.sqrt_pos.mpr h.transmission_pos
  have hts := Real.sq_sqrt h.transmission_pos.le
  have htl : Real.sqrt T < 1 := by
    apply (Real.sqrt_lt h.transmission_pos.le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    simpa using h.transmission_lt_one
  have hy := (active_target_properties h).2.1
  unfold y0 at hy
  unfold targetSheetV
  apply (lt_div_iff₀ ht).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr htl)]

theorem targetSheetH_pos {T a : ℝ} (h : ActiveTarget T a) : 0 < targetSheetH T a := by
  exact div_pos (sub_pos.mpr (active_target_s_lt_one h)) (Real.sqrt_pos.mpr h.transmission_pos)

theorem targetSheetA_properties {T a : ℝ} (h : ActiveTarget T a) :
    0 < targetSheetA T a ∧ targetSheetA T a < 1 ∧
      targetSheetA T a + (targetSheetA T a)⁻¹ = targetSheetV T a :=
  smallSheetRoot_properties (targetSheetV_gt_two h)

theorem targetSheetV_add_H {T a : ℝ} :
    targetSheetV T a + targetSheetH T a = 2 / Real.sqrt T := by
  unfold targetSheetV targetSheetH
  ring

theorem targetSheetV_sub_H {T a : ℝ} :
    targetSheetV T a - targetSheetH T a = 2 * s a / Real.sqrt T := by
  unfold targetSheetV targetSheetH
  ring

theorem targetSheet_response {T a : ℝ} (h : ActiveTarget T a) :
    matchingResponse (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a)) =
      (T, a) := by
  have hA := targetSheetA_properties h
  have hH := targetSheetH_pos h
  have ht := Real.sqrt_pos.mpr h.transmission_pos
  have hts := Real.sq_sqrt h.transmission_pos.le
  have hs := (active_target_properties h).1
  have hr : 0 ≤ 1 - 2 * a := by nlinarith [h.absorptance_lt, sq_nonneg T]
  have hss : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hr
  rw [triangularMatchingTransfer_response hA.1.ne'
    (show targetSheetA T a + targetSheetH T a + (targetSheetA T a)⁻¹ ≠ 0 from
      (add_pos (add_pos hA.1 hH) (inv_pos.mpr hA.1)).ne'),
    hA.2.2, targetSheetV_add_H]
  apply Prod.ext
  · dsimp
    field_simp
    nlinarith
  · dsimp
    unfold targetSheetH targetSheetV
    field_simp
    nlinarith

def targetMatchingLogs (g T a : ℝ) : ℝ × ℝ :=
  ((Real.log (targetSheetA T a) + Real.log (targetSheetH T a / g)) / 2,
    (Real.log (targetSheetA T a) - Real.log (targetSheetH T a / g)) / 2)

theorem targetSheet_inverse_gap {T a : ℝ} (h : ActiveTarget T a) :
    (targetSheetA T a)⁻¹ - targetSheetA T a =
      Real.sqrt ((targetSheetV T a) ^ 2 - 4) := by
  have hp := (targetSheetA_properties h).2.2
  unfold targetSheetA smallSheetRoot at hp ⊢
  linarith

theorem targetSheet_reflection_gap {T a : ℝ} (h : ActiveTarget T a) :
    targetSheetH T a < (targetSheetA T a)⁻¹ - targetSheetA T a := by
  have hv := targetSheetV_gt_two h
  have hh := targetSheetH_pos h
  have hs := (active_target_properties h).2.1
  unfold y0 at hs
  have ht := Real.sqrt_pos.mpr h.transmission_pos
  have hts := Real.sq_sqrt h.transmission_pos.le
  have hdiff : (targetSheetV T a) ^ 2 - (targetSheetH T a) ^ 2 =
      4 * s a / T := by
    calc
      _ = 4 * s a / (Real.sqrt T) ^ 2 := by
        unfold targetSheetV targetSheetH
        field_simp
        ring
      _ = _ := by rw [hts]
  have hlt : 4 < 4 * s a / T := (lt_div_iff₀ h.transmission_pos).mpr (by linarith)
  rw [targetSheet_inverse_gap h]
  have hr : 0 ≤ (targetSheetV T a) ^ 2 - 4 := by nlinarith
  have hsq := Real.sq_sqrt hr
  have hd := Real.sqrt_nonneg ((targetSheetV T a) ^ 2 - 4)
  nlinarith

theorem targetMatchingLogs_sum (g T a : ℝ) :
    (targetMatchingLogs g T a).1 + (targetMatchingLogs g T a).2 =
      Real.log (targetSheetA T a) := by
  unfold targetMatchingLogs
  ring

theorem targetMatchingLogs_diff (g T a : ℝ) :
    (targetMatchingLogs g T a).1 - (targetMatchingLogs g T a).2 =
      Real.log (targetSheetH T a / g) := by
  unfold targetMatchingLogs
  ring

theorem targetMatchingLogs_exp {g T a : ℝ} (hg : 0 < g) (h : ActiveTarget T a) :
    Real.exp ((targetMatchingLogs g T a).1 + (targetMatchingLogs g T a).2) =
      targetSheetA T a ∧
    g * Real.exp ((targetMatchingLogs g T a).1 - (targetMatchingLogs g T a).2) =
      targetSheetH T a := by
  rw [targetMatchingLogs_sum, targetMatchingLogs_diff,
    Real.exp_log (targetSheetA_properties h).1,
    Real.exp_log (div_pos (targetSheetH_pos h) hg)]
  constructor
  · rfl
  · field_simp

theorem targetMatchingLogs_coated_sheet {g T a : ℝ} (hg : 0 < g) (h : ActiveTarget T a) :
    logCoatedTransfer (CoreConstruction.limitingSheet g) (targetMatchingLogs g T a) =
      triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a) := by
  have he := targetMatchingLogs_exp hg h
  have he' : Real.exp ((targetMatchingLogs g T a).1 - (targetMatchingLogs g T a).2) * g =
      targetSheetH T a := by nlinarith only [he.2]
  have hs : -(targetMatchingLogs g T a).1 - (targetMatchingLogs g T a).2 =
      -((targetMatchingLogs g T a).1 + (targetMatchingLogs g T a).2) := by ring
  rw [CoreConstruction.limitingSheet_explicit]
  ext i j
  fin_cases i <;> fin_cases j
  · change (Real.exp ((targetMatchingLogs g T a).1 + (targetMatchingLogs g T a).2) : ℂ) * 1 =
      (targetSheetA T a : ℂ)
    rw [he.1, mul_one]
  · change (Real.exp ((targetMatchingLogs g T a).2 - (targetMatchingLogs g T a).1) : ℂ) * 0 = 0
    exact mul_zero _
  · change (Real.exp ((targetMatchingLogs g T a).1 - (targetMatchingLogs g T a).2) : ℂ) *
      -(g : ℂ) = -(targetSheetH T a : ℂ)
    exact_mod_cast (show Real.exp ((targetMatchingLogs g T a).1 -
      (targetMatchingLogs g T a).2) * -g = -targetSheetH T a by nlinarith only [he'])
  · change (Real.exp (-(targetMatchingLogs g T a).1 - (targetMatchingLogs g T a).2) : ℂ) * 1 =
      (((targetSheetA T a)⁻¹ : ℝ) : ℂ)
    rw [hs, Real.exp_neg, he.1, mul_one]

theorem targetMatchingLogs_response {g T a : ℝ} (hg : 0 < g) (h : ActiveTarget T a) :
    matchingLogResponse (CoreConstruction.limitingSheet g, targetMatchingLogs g T a) =
      (T, a) := by
  unfold matchingLogResponse
  rw [targetMatchingLogs_coated_sheet hg h, targetSheet_response h]

#print axioms smallSheetRoot_properties
#print axioms active_target_s_lt_one
#print axioms targetSheetV_gt_two
#print axioms targetSheetH_pos
#print axioms targetSheetA_properties
#print axioms targetSheetV_add_H
#print axioms targetSheetV_sub_H
#print axioms targetSheet_response
#print axioms targetSheet_inverse_gap
#print axioms targetSheet_reflection_gap
#print axioms targetMatchingLogs_sum
#print axioms targetMatchingLogs_diff
#print axioms targetMatchingLogs_exp
#print axioms targetMatchingLogs_coated_sheet
#print axioms targetMatchingLogs_response
end OQ7
