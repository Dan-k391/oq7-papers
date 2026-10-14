import OQ7.Passivity

namespace OQ7

noncomputable section

/-- The actual phase product used in the checkpoint, without an argument branch. -/
def phaseProduct (rL rR t : ℂ) : ℂ := rL * rR * (star t) ^ 2

/-- Unit phase from the three actual nonzero scattering entries. -/
def unitPhase (rL rR t : ℂ) : ℂ :=
  phaseProduct rL rR t / ((transmissionPower t * ‖rL * rR‖ : ℝ) : ℂ)

theorem phase_denominator_pos {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    0 < transmissionPower t * ‖rL * rR‖ := by
  exact mul_pos (transmission_positive ht) (norm_pos_iff.mpr (mul_ne_zero hL hR))

/-- The normalized actual scattering phase has squared norm one. -/
theorem unitPhase_normSq {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    Complex.normSq (unitPhase rL rR t) = 1 := by
  have hden := phase_denominator_pos hL hR ht
  unfold unitPhase phaseProduct
  rw [Complex.normSq_div]
  simp only [Complex.normSq_mul, map_pow, Complex.star_def,
    Complex.normSq_conj, Complex.normSq_ofReal]
  have hsq : Complex.normSq rL * Complex.normSq rR = ‖rL * rR‖ ^ 2 := by
    rw [← Complex.normSq_mul, Complex.normSq_eq_norm_sq]
  rw [hsq]
  dsimp [transmissionPower] at hden ⊢
  have hdenne : Complex.normSq t * ‖rL * rR‖ ≠ 0 := ne_of_gt hden
  have htn : Complex.normSq t ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr ht)
  have hrn : ‖rL * rR‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr (mul_ne_zero hL hR))
  field_simp [htn, hrn]

/-- Squared displacement from minus one is the exact real-part phase penalty. -/
theorem normSq_add_one_of_unit (z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.normSq (z + 1) = 2 * (1 + z.re) := by
  rw [Complex.normSq_add]
  simp [hz]
  ring

theorem unitPhase_penalty {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    Complex.normSq (unitPhase rL rR t + 1) =
      2 * (1 + (unitPhase rL rR t).re) := by
  exact normSq_add_one_of_unit _ (unitPhase_normSq hL hR ht)

/-- Exact expansion of the actual off-diagonal absorption interference. -/
theorem interference_phaseProduct (rL rR t : ℂ) :
    Complex.normSq (interference rL rR t) =
      transmissionPower t * (Complex.normSq rL + Complex.normSq rR) +
      2 * (phaseProduct rL rR t).re := by
  have hcross : (star rL * t) * star (star t * rR) = star (phaseProduct rL rR t) := by
    simp [phaseProduct, pow_two, mul_comm, mul_left_comm, mul_assoc]
  unfold interference
  rw [Complex.normSq_add]
  simp only [← Complex.star_def, hcross]
  simp only [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
    Complex.conj_re]
  dsimp [transmissionPower]
  ring

/-- Recovering the real part of the unnormalized actual phase product. -/
theorem phaseProduct_re {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    (phaseProduct rL rR t).re = transmissionPower t * ‖rL * rR‖ *
      (unitPhase rL rR t).re := by
  have hden := phase_denominator_pos hL hR ht
  have htne : transmissionPower t ≠ 0 := ne_of_gt (transmission_positive ht)
  have hrne : ‖rL * rR‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr (mul_ne_zero hL hR))
  dsimp [unitPhase]
  rw [Complex.div_ofReal_re]
  field_simp [htne, hrne]

/-- The phase-dependent interference formula uses the actual mean reflection power. -/
theorem interference_unitPhase {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    Complex.normSq (interference rL rR t) =
      2 * transmissionPower t *
        ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t) +
      2 * transmissionPower t * ‖rL * rR‖ * (unitPhase rL rR t).re := by
  rw [interference_phaseProduct, phaseProduct_re hL hR ht]
  have he := reflection_coordinates rL rR t
  rw [he.1, he.2]
  ring

/-- Exact physical two-port determinant identity underlying the checkpoint's
phase adaptation. It avoids every choice of a principal argument. -/
theorem absorption_det_phase_penalty {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    (absorptionMatrix rL rR t).det.re =
      ScalarEnvelope.F (transmissionPower t) (meanAbsorptance rL rR t)
        |halfAsymmetry rL rR t| -
      transmissionPower t * ‖rL * rR‖ *
        Complex.normSq (unitPhase rL rR t + 1) := by
  rw [absorption_det_coordinates, Complex.ofReal_re,
    interference_unitPhase hL hR ht, unitPhase_penalty hL hR ht]
  unfold ScalarEnvelope.F
  rw [reflection_product_sqrt, norm_mul]
  have he := reflection_coordinates rL rR t
  have hsq : (‖rL‖ * ‖rR‖) ^ 2 =
      (ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 -
        (halfAsymmetry rL rR t) ^ 2 := by
    rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      he.1, he.2]
    ring
  unfold ScalarEnvelope.b at hsq ⊢
  nlinarith

/-- The phase penalty is exactly quadratic in the distance from minus one.
This is the identity used to obtain the checkpoint's fourth-order remainder. -/
theorem absorption_det_phase_norm {rL rR t : ℂ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    ScalarEnvelope.F (transmissionPower t) (meanAbsorptance rL rR t)
        |halfAsymmetry rL rR t| - (absorptionMatrix rL rR t).det.re =
      transmissionPower t * ‖rL * rR‖ * ‖unitPhase rL rR t + 1‖ ^ 2 := by
  rw [absorption_det_phase_penalty hL hR ht, Complex.normSq_eq_norm_sq]
  ring

/-- An explicit phase-distance bound gives a squared determinant remainder bound. -/
theorem phase_remainder_bound {rL rR t : ℂ} {epsilon : ℝ}
    (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0)
    (heps : ‖unitPhase rL rR t + 1‖ ≤ epsilon) :
    ScalarEnvelope.F (transmissionPower t) (meanAbsorptance rL rR t)
        |halfAsymmetry rL rR t| - (absorptionMatrix rL rR t).det.re ≤
      transmissionPower t * ‖rL * rR‖ * epsilon ^ 2 := by
  rw [absorption_det_phase_norm hL hR ht]
  apply mul_le_mul_of_nonneg_left _ (phase_denominator_pos hL hR ht).le
  exact (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) heps)).mpr heps

#print axioms phase_denominator_pos
#print axioms unitPhase_normSq
#print axioms normSq_add_one_of_unit
#print axioms unitPhase_penalty
#print axioms interference_phaseProduct
#print axioms phaseProduct_re
#print axioms interference_unitPhase
#print axioms absorption_det_phase_penalty
#print axioms absorption_det_phase_norm
#print axioms phase_remainder_bound

end
end OQ7
