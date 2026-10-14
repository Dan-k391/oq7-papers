import OQ7.MatchingOptimizer
import OQ7.QuadraticRates
import OQ7.Scattering

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7
open Filter Asymptotics ScalarEnvelope
open scoped Topology Matrix.Norms.Elementwise ComplexOrder

def transferResponseAsymmetry (F : Mat2) : ℝ :=
  responseAsymmetry (transferReflectionLeft (waveTransfer F))
    (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))

theorem matchingResponse_eq_physical {F : Mat2} (hdet : F.det = 1) :
    matchingResponse F =
      (transmissionPower (transferTransmissionRight (waveTransfer F)),
        meanAbsorptance (transferReflectionLeft (waveTransfer F))
          (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))) := by
  apply Prod.ext
  · exact matchingTransmissionPower_physical hdet
  · exact matchingMeanAbsorptance_physical hdet

theorem transfer_exact_targets {T a : ℝ} {F : Mat2} (hdet : F.det = 1)
    (htarget : matchingResponse F = (T, a)) :
    transmissionPower (transferTransmissionRight (waveTransfer F)) = T ∧
      meanAbsorptance (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F)) = a := by
  rw [matchingResponse_eq_physical hdet] at htarget
  exact ⟨congrArg Prod.fst htarget, congrArg Prod.snd htarget⟩

theorem transferNormalizedDet_eq_fluxdet_re {F : Mat2}
    (hp : (fluxDefect F).PosSemidef) (hdet : F.det = 1) :
    normalizedAbsorptionDet (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F)) =
        (fluxDefect F).det.re := by
  have he := congrArg Complex.re (passive_transfer_absorption_det_ratio F hp hdet)
  simpa only [Complex.div_ofReal_re, normalizedAbsorptionDet, transmissionPower] using he

theorem transfer_sharp_coordinates_valid {T a : ℝ} (h : ActiveTarget T a) {F : Mat2}
    (hp : (fluxDefect F).PosSemidef) (hdet : F.det = 1)
    (htarget : matchingResponse F = (T, a)) :
    0 ≤ |transferHalfAsymmetry F| ∧ |transferHalfAsymmetry F| ≤ x0 T a := by
  have hs := passive_transfer_scattering F hp hdet
  have ht := transfer_exact_targets hdet htarget
  have ha : ActiveTarget (transmissionPower (transferTransmissionRight (waveTransfer F)))
      (meanAbsorptance (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))) := by
    rw [ht.1, ht.2]
    exact h
  have hc : 0 ≤ normalizedAbsorptionDet (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F)) :=
    div_nonneg (passive_det_nonneg hs) (by rw [ht.1]; exact h.transmission_pos.le)
  have hb := active_matrix_deficit hs ha
  rw [ht.1, ht.2, responseAsymmetry_eq] at hb
  have halpha := (active_target_properties h).2.2.2.2.2.2.2
  have hnonneg := mul_nonneg halpha.le hc
  refine ⟨abs_nonneg _, ?_⟩
  change |halfAsymmetry (transferReflectionLeft (waveTransfer F))
    (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))| ≤ x0 T a
  unfold D0 at hb
  linarith

theorem transfer_phase_remainder {T a : ℝ} {F : Mat2}
    (hp : (fluxDefect F).PosSemidef) (hdet : F.det = 1)
    (htarget : matchingResponse F = (T, a))
    (hL : transferReflectionLeft (waveTransfer F) ≠ 0)
    (hR : transferReflectionRight (waveTransfer F) ≠ 0) :
    ScalarEnvelope.F T a |transferHalfAsymmetry F| - T * (fluxDefect F).det.re =
      T * ‖transferReflectionLeft (waveTransfer F) * transferReflectionRight (waveTransfer F)‖ *
        ‖transferUnitPhase F + 1‖ ^ 2 := by
  have ht := transfer_exact_targets hdet htarget
  have htn := passive_transfer_transmission_ne_zero F hp
  have hd := passive_transfer_denominator_ne_zero F hp
  have he := congrArg Complex.re (transfer_absorption_fluxDefect_det F hd hdet)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hphase := absorption_det_phase_norm hL hR htn
  rw [ht.1, ht.2] at hphase
  change ScalarEnvelope.F T a |transferHalfAsymmetry F| -
    (absorptionMatrix (transferReflectionLeft (waveTransfer F))
      (transferReflectionRight (waveTransfer F)) (transferTransmissionRight (waveTransfer F))).det.re =
    T * ‖transferReflectionLeft (waveTransfer F) * transferReflectionRight (waveTransfer F)‖ *
      ‖transferUnitPhase F + 1‖ ^ 2 at hphase
  change (absorptionMatrix _ _ _).det.re =
    transmissionPower (transferTransmissionRight (waveTransfer F)) * (fluxDefect F).det.re at he
  rw [ht.1] at he
  simpa only [he] using hphase

theorem transferUnitPhase_nonzero_entries {F : Mat2} (hz : transferUnitPhase F ≠ 0) :
    transferReflectionLeft (waveTransfer F) ≠ 0 ∧
      transferReflectionRight (waveTransfer F) ≠ 0 ∧
        transferTransmissionRight (waveTransfer F) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    exact hz (by simp [transferUnitPhase, unitPhase, phaseProduct, h0])
  · intro h0
    exact hz (by simp [transferUnitPhase, unitPhase, phaseProduct, h0])
  · intro h0
    exact hz (by simp [transferUnitPhase, unitPhase, phaseProduct, h0])

theorem transfer_halfAsymmetry_quadratic_rate {T a : ℝ} (h : ActiveTarget T a)
    {F : ℕ → Mat2}
    (hconv : Tendsto F atTop (𝓝 (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))))
    (hrate : (fun m => F m - triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))
      =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2)) :
    (fun m => x0 T a - |transferHalfAsymmetry (F m)|)
      =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
  have hd := (transferHalfAsymmetry_contDiffAt 1
    (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))
    (triangularMatchingTransfer_denominator_ne_zero
      (targetSheetA_properties h).1 (targetSheetH_pos h))).differentiableAt one_ne_zero
  have hr := differentiable_sequence_reciprocal_square_rate hd hconv hrate
  have ht : Tendsto (fun m => transferHalfAsymmetry (F m)) atTop (𝓝 (x0 T a)) := by
    simpa only [targetSheet_halfAsymmetry h, Function.comp_def] using! hd.continuousAt.tendsto.comp hconv
  have hpos := ht.eventually (eventually_gt_nhds (active_target_properties h).2.2.2.1)
  apply hr.neg_left.congr' ?_ EventuallyEq.rfl
  filter_upwards [hpos] with m hm
  simp only [targetSheet_halfAsymmetry h, abs_of_pos hm]
  ring

theorem transfer_unitPhase_quadratic_rate {T a : ℝ} (h : ActiveTarget T a)
    {F : ℕ → Mat2}
    (hconv : Tendsto F atTop (𝓝 (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))))
    (hrate : (fun m => F m - triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))
      =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2)) :
    (fun m => transferUnitPhase (F m) + 1)
      =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
  have hd := (targetSheet_unitPhase_contDiffAt 1 h).differentiableAt one_ne_zero
  simpa only [targetSheet_unitPhase h, sub_neg_eq_add] using
    differentiable_sequence_reciprocal_square_rate hd hconv hrate

theorem transfer_reflection_product_tendsto {T a : ℝ} (h : ActiveTarget T a)
    {F : ℕ → Mat2}
    (hconv : Tendsto F atTop (𝓝 (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))))
    (htarget : ∀ᶠ m : ℕ in atTop, (F m).det = 1 ∧ matchingResponse (F m) = (T, a)) :
    Tendsto (fun m => T * ‖transferReflectionLeft (waveTransfer (F m)) *
      transferReflectionRight (waveTransfer (F m))‖) atTop (𝓝 (T * y0 T a)) := by
  have hd := (transferHalfAsymmetry_contDiffAt 1
    (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))
    (triangularMatchingTransfer_denominator_ne_zero
      (targetSheetA_properties h).1 (targetSheetH_pos h))).differentiableAt one_ne_zero
  have ht : Tendsto (fun m => |transferHalfAsymmetry (F m)|) atTop (𝓝 (x0 T a)) := by
    simpa only [targetSheet_halfAsymmetry h, abs_of_pos (active_target_properties h).2.2.2.1,
      Function.comp_def] using! (hd.continuousAt.tendsto.comp hconv).abs
  have hs := ((tendsto_const_nhds (x := (b T a) ^ 2)).sub (ht.pow 2)).sqrt
  have hroot : Real.sqrt ((b T a) ^ 2 - (x0 T a) ^ 2) = y0 T a := by
    rw [x0_sq h]
    have hp : (b T a) ^ 2 - ((b T a) ^ 2 - (y0 T a) ^ 2) = (y0 T a) ^ 2 := by ring
    rw [hp, Real.sqrt_sq_eq_abs, abs_of_pos (active_target_properties h).2.1]
  rw [hroot] at hs
  apply (hs.const_mul T).congr'
  filter_upwards [htarget] with m hm
  have he := transfer_exact_targets hm.1 hm.2
  have hr := reflection_product_sqrt (transferReflectionLeft (waveTransfer (F m)))
    (transferReflectionRight (waveTransfer (F m))) (transferTransmissionRight (waveTransfer (F m)))
  rw [he.1, he.2] at hr
  dsimp [transferHalfAsymmetry]
  rw [hr, norm_mul]

/-- Analytic sharp-response conversion. Its finite-transfer passivity, determinant,
exact target and norm-rate hypotheses are discharged by the actual multilayer
construction in the final physical theorem. -/
theorem transfer_sharp_deficit_limit {T a C : ℝ} (h : ActiveTarget T a) (F : ℕ → Mat2)
    (hpassive : ∀ᶠ m : ℕ in atTop, (fluxDefect (F m)).PosSemidef ∧
      (F m).det = 1 ∧ matchingResponse (F m) = (T, a))
    (hconv : Tendsto F atTop (𝓝 (triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))))
    (hrate : (fun m => F m - triangularMatchingTransfer (targetSheetA T a) (targetSheetH T a))
      =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2))
    (hc : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (fluxDefect (F m)).det.re) atTop (𝓝 C)) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (D0 T a - transferResponseAsymmetry (F m)))
      atTop (𝓝 (alpha T a * C)) := by
  have hx : ∀ᶠ m : ℕ in atTop, 0 ≤ |transferHalfAsymmetry (F m)| ∧
      |transferHalfAsymmetry (F m)| ≤ x0 T a := by
    filter_upwards [hpassive] with m hm
    exact transfer_sharp_coordinates_valid h hm.1 hm.2.1 hm.2.2
  have hzrate := transfer_unitPhase_quadratic_rate h hconv hrate
  have hzsq := reciprocal_square_norm_rate_of_isBigO hzrate
  have hzlimit : Tendsto (fun m => transferUnitPhase (F m)) atTop (𝓝 (-1 : ℂ)) := by
    simpa only [targetSheet_unitPhase h, Function.comp_def] using!
      ((targetSheet_unitPhase_contDiffAt 1 h).continuousAt.tendsto.comp hconv)
  have hnz := hzlimit.eventually (eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 0))
  have htarget : ∀ᶠ m : ℕ in atTop, (F m).det = 1 ∧ matchingResponse (F m) = (T, a) :=
    hpassive.mono (fun _ hm => hm.2)
  have hpref := transfer_reflection_product_tendsto h hconv htarget
  have hphase : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      (ScalarEnvelope.F T a |transferHalfAsymmetry (F m)| - T * (fluxDefect (F m)).det.re))
        atTop (𝓝 0) := by
    have ht := hpref.mul hzsq
    rw [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hpassive, hnz] with m hm hzm
    have hentries := transferUnitPhase_nonzero_entries hzm
    rw [transfer_phase_remainder hm.1 hm.2.1 hm.2.2 hentries.1 hentries.2.1]
    ring
  have hsharp := sharp_deficit_limit_of_quadratic_rates h
    (fun m => |transferHalfAsymmetry (F m)|) (fun m => (fluxDefect (F m)).det.re)
    hx hc hphase (transfer_halfAsymmetry_quadratic_rate h hconv hrate)
  simpa only [transferResponseAsymmetry, responseAsymmetry_eq, transferHalfAsymmetry] using hsharp

#print axioms matchingResponse_eq_physical
#print axioms transfer_exact_targets
#print axioms transferNormalizedDet_eq_fluxdet_re
#print axioms transfer_sharp_coordinates_valid
#print axioms transfer_phase_remainder
#print axioms transferUnitPhase_nonzero_entries
#print axioms transfer_halfAsymmetry_quadratic_rate
#print axioms transfer_unitPhase_quadratic_rate
#print axioms transfer_reflection_product_tendsto
#print axioms transfer_sharp_deficit_limit
end OQ7
