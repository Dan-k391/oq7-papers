import OQ7.PhysicalCellRemainder
import OQ7.CoreInsertion
import OQ7.InsertionRemainder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OQ7.CoreConstruction
open Filter
open scoped Topology Matrix Matrix.Norms.Operator

/-- The full repeated actual finite-layer core has the checkpoint's J/m² correction
and one uniform fourth-order error bound in the genuine operator norm. -/
theorem actual_repeatedCore_quartic_remainder_norm_bound {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M) -
        (1 / (m : ℂ) ^ 2) • coreJ P Q (k * M)‖ ≤ C / (m : ℝ) ^ 4 := by
  obtain ⟨Ce, hCe, he⟩ := actual_core_doubleInsertion_quartic_norm_bound hP hQ k M
  obtain ⟨Cr, hCr, hr⟩ := coreCellPerturbation_coefficientRemainder_norm_bound hP hQ k M
  let G : Mat2 := sheetGenerator (k * M)
  let S : Mat2 := G * coreH P Q (k * M) * G
  let C : ℝ := Ce + Cr * Real.exp ‖G‖ + ‖S‖ / 6
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [he, hr, eventually_gt_atTop (0 : ℕ)] with m hem hrm hm
  have hmn : m ≠ 0 := hm.ne'
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmr : (m : ℝ) ≠ 0 := hmp.ne'
  let a : Mat2 := linearizedCore (k * M) (1 / (m : ℂ))
  let w : Mat2 := coreCellPerturbation k P Q M m
  let v : Mat2 := (1 / (m : ℂ) ^ 3) • coreH P Q (k * M) +
    (1 / (m : ℂ) ^ 4) • coreK4 P Q (k * M)
  have har : ‖firstInsertion a (w - v) m‖ ≤ (Cr * Real.exp ‖G‖) / (m : ℝ) ^ 4 := by
    rw [show a = (1 : Mat2) + (1 / (m : ℝ)) • G from
      linearizedCore_reciprocal_eq_real (k * M) m]
    apply norm_firstInsertion_quintic_reciprocal_le G (w - v) hCr.le hm
    simpa only [w, v, sub_add_eq_sub_sub] using hrm
  have hid : strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M) -
      (1 / (m : ℂ) ^ 2) • coreJ P Q (k * M) =
        insertionError a w m + firstInsertion a (w - v) m -
          (1 / (6 * (m : ℂ) ^ 4)) • S := by
    simp only [insertionError, firstInsertion_sub]
    rw [show a ^ m = limitingSheet (k * M) from
      linearizedCore_reciprocal_fullPower hmn]
    rw [show firstInsertion a v m = (1 / (m : ℂ) ^ 2) • coreJ P Q (k * M) -
      (1 / (6 * (m : ℂ) ^ 4)) • S from core_firstInsertion_reciprocal hmn P Q (k * M)]
    rw [show a + w = strippedCellTransfer k P Q M m from
      (strippedCellTransfer_eq_linearized_add k P Q M m).symm]
    abel
  have hs : ‖(1 / (6 * (m : ℂ) ^ 4)) • S‖ = (‖S‖ / 6) / (m : ℝ) ^ 4 := by
    simp only [norm_smul, norm_div, norm_one, norm_mul, norm_pow, norm_natCast]
    norm_num
    field_simp
  rw [hid]
  calc
    ‖insertionError a w m + firstInsertion a (w - v) m -
        (1 / (6 * (m : ℂ) ^ 4)) • S‖ ≤
      ‖insertionError a w m‖ + ‖firstInsertion a (w - v) m‖ +
        ‖(1 / (6 * (m : ℂ) ^ 4)) • S‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Ce / (m : ℝ) ^ 4 + (Cr * Real.exp ‖G‖) / (m : ℝ) ^ 4 +
        (‖S‖ / 6) / (m : ℝ) ^ 4 := add_le_add (add_le_add hem har) hs.le
    _ = C / (m : ℝ) ^ 4 := by dsimp [C]; ring

theorem physicalUnmatchedCore_quartic_remainder_norm_bound {k P Q : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : Q ≠ 0) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖stackTransfer k (physicalUnmatchedCore k P Q M m) -
        ((-1 : ℂ) ^ (m + 1)) • (limitingSheet (k * M) +
          (1 / (m : ℂ) ^ 2) • coreJ P Q (k * M))‖ ≤ C / (m : ℝ) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := actual_repeatedCore_quartic_remainder_norm_bound hP hQ k M
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with m hm
  rw [physicalUnmatchedCore_transferFactorization hk (by linarith : 0 < P),
    ← smul_sub, norm_smul]
  simpa only [norm_pow, norm_neg, norm_one, one_pow, one_mul, sub_add_eq_sub_sub] using hm

theorem actual_repeatedCore_quadratic_convergence_norm_bound {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M)‖ ≤ C / (m : ℝ) ^ 2 := by
  obtain ⟨Cr, hCr, hr⟩ := actual_repeatedCore_quartic_remainder_norm_bound hP hQ k M
  let J : Mat2 := coreJ P Q (k * M)
  refine ⟨Cr + ‖J‖, by positivity, ?_⟩
  filter_upwards [hr, eventually_gt_atTop (0 : ℕ)] with m hrm hm
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by decide)
  have hj : ‖(1 / (m : ℂ) ^ 2) • J‖ = ‖J‖ / (m : ℝ) ^ 2 := by
    simp only [norm_smul, norm_div, norm_one, norm_pow, norm_natCast]
    ring
  calc
    ‖strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M)‖ ≤
        ‖strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M) -
          (1 / (m : ℂ) ^ 2) • J‖ + ‖(1 / (m : ℂ) ^ 2) • J‖ := by
      let x : Mat2 := strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M)
      let y : Mat2 := (1 / (m : ℂ) ^ 2) • J
      have hx : x = (x - y) + y := by abel
      calc
        ‖x‖ = ‖(x - y) + y‖ := congrArg norm hx
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    _ ≤ Cr / (m : ℝ) ^ 4 + ‖J‖ / (m : ℝ) ^ 2 := add_le_add hrm hj.le
    _ ≤ Cr / (m : ℝ) ^ 2 + ‖J‖ / (m : ℝ) ^ 2 :=
      add_le_add (div_le_div_of_nonneg_left hCr.le (by positivity) hpow) le_rfl
    _ = (Cr + ‖J‖) / (m : ℝ) ^ 2 := by ring




#print axioms actual_repeatedCore_quartic_remainder_norm_bound
#print axioms physicalUnmatchedCore_quartic_remainder_norm_bound
#print axioms actual_repeatedCore_quadratic_convergence_norm_bound
end OQ7.CoreConstruction

