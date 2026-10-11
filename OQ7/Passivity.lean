import OQ7.TwoPort
import OQ7.Envelope

namespace OQ7

open scoped ComplexOrder
noncomputable section

theorem passive_absorptances_nonneg {rL rR t : ℂ} (h : Passive rL rR t) :
    0 ≤ absorptanceLeft rL t ∧ 0 ≤ absorptanceRight rR t := by
  have hL := h.diag_nonneg (i := 0)
  have hR := h.diag_nonneg (i := 1)
  rw [absorptionMatrix_eq] at hL hR
  simpa using And.intro hL hR

theorem passive_det_nonneg {rL rR t : ℂ} (h : Passive rL rR t) :
    0 ≤ (absorptionMatrix rL rR t).det.re := by
  exact (Complex.nonneg_iff.mp h.det_nonneg).1

theorem reflection_coordinates (rL rR t : ℂ) :
    Complex.normSq rL =
      ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t) -
        halfAsymmetry rL rR t ∧
    Complex.normSq rR =
      ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t) +
        halfAsymmetry rL rR t := by
  unfold ScalarEnvelope.b transmissionPower meanAbsorptance halfAsymmetry
    absorptanceLeft absorptanceRight
  constructor <;> ring

theorem halfAsymmetry_le_b (rL rR t : ℂ) :
    |halfAsymmetry rL rR t| ≤
      ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t) := by
  have he := reflection_coordinates rL rR t
  have hl := Complex.normSq_nonneg rL
  have hr := Complex.normSq_nonneg rR
  rw [he.1] at hl
  rw [he.2] at hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem interference_reverse_triangle (rL rR t : ℂ) :
    transmissionPower t * (‖rL‖ - ‖rR‖) ^ 2 ≤
      Complex.normSq (interference rL rR t) := by
  have hn := abs_norm_sub_norm_le (star rL * t) (-(star t * rR))
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hn
  simp only [norm_neg, norm_mul, norm_star, sub_neg_eq_add, sq_abs] at hs
  rw [Complex.sq_norm] at hs
  change (‖rL‖ * ‖t‖ - ‖t‖ * ‖rR‖) ^ 2 ≤
    Complex.normSq (interference rL rR t) at hs
  calc
    transmissionPower t * (‖rL‖ - ‖rR‖) ^ 2 =
        (‖rL‖ * ‖t‖ - ‖t‖ * ‖rR‖) ^ 2 := by
      rw [transmissionPower, Complex.normSq_eq_norm_sq]
      ring
    _ ≤ _ := hs

theorem reflection_product_sqrt (rL rR t : ℂ) :
    Real.sqrt ((ScalarEnvelope.b (transmissionPower t)
      (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2) =
      ‖rL‖ * ‖rR‖ := by
  have he := reflection_coordinates rL rR t
  have hs : (ScalarEnvelope.b (transmissionPower t)
      (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2 =
      (‖rL‖ * ‖rR‖) ^ 2 := by
    rw [sq_abs]
    rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      he.1, he.2]
    ring
  rw [hs, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

theorem absorption_det_le_envelope (rL rR t : ℂ) :
    (absorptionMatrix rL rR t).det.re ≤
      ScalarEnvelope.F (transmissionPower t) (meanAbsorptance rL rR t)
        |halfAsymmetry rL rR t| := by
  have hd := absorption_det_coordinates rL rR t
  have hl := interference_reverse_triangle rL rR t
  have he := reflection_coordinates rL rR t
  have hsum : ‖rL‖ ^ 2 + ‖rR‖ ^ 2 =
      2 * ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, he.1, he.2]
    ring
  have hsq : (‖rL‖ * ‖rR‖) ^ 2 =
      (ScalarEnvelope.b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 -
        (halfAsymmetry rL rR t) ^ 2 := by
    rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      he.1, he.2]
    ring
  have hrad : 0 ≤ (ScalarEnvelope.b (transmissionPower t)
      (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2 := by
    rw [sq_abs, ← hsq]
    exact sq_nonneg _
  have hbound : transmissionPower t * (‖rL‖ - ‖rR‖) ^ 2 =
      2 * transmissionPower t * (ScalarEnvelope.b (transmissionPower t)
        (meanAbsorptance rL rR t) - ‖rL‖ * ‖rR‖) := by
    calc
      transmissionPower t * (‖rL‖ - ‖rR‖) ^ 2 =
          transmissionPower t * ((‖rL‖ ^ 2 + ‖rR‖ ^ 2) - 2 * ‖rL‖ * ‖rR‖) := by ring
      _ = _ := by rw [hsum]; ring
  rw [hbound] at hl
  rw [hd, Complex.ofReal_re, ScalarEnvelope.F_alternative hrad,
    reflection_product_sqrt, sq_abs]
  linarith

/-- The paper's invariant computed from the actual reciprocal scattering matrix. -/
def normalizedAbsorptionDet (rL rR t : ℂ) : ℝ :=
  (absorptionMatrix rL rR t).det.re / transmissionPower t

def responseAsymmetry (rL rR t : ℂ) : ℝ :=
  |absorptanceLeft rL t - absorptanceRight rR t|

theorem responseAsymmetry_eq (rL rR t : ℂ) :
    responseAsymmetry rL rR t = 2 * |halfAsymmetry rL rR t| := by
  unfold responseAsymmetry halfAsymmetry
  rw [abs_div]
  norm_num
  ring

/-- The active-branch deficit bound (33), now for the explicit passive matrix. -/
theorem active_matrix_deficit {rL rR t : ℂ} (hp : Passive rL rR t)
    (h : ScalarEnvelope.ActiveTarget (transmissionPower t) (meanAbsorptance rL rR t)) :
    ScalarEnvelope.alpha (transmissionPower t) (meanAbsorptance rL rR t) *
      normalizedAbsorptionDet rL rR t ≤
    ScalarEnvelope.D0 (transmissionPower t) (meanAbsorptance rL rR t) -
      responseAsymmetry rL rR t := by
  have hc : 0 ≤ normalizedAbsorptionDet rL rR t :=
    div_nonneg (passive_det_nonneg hp) h.transmission_pos.le
  have he : transmissionPower t * normalizedAbsorptionDet rL rR t =
      (absorptionMatrix rL rR t).det.re := by
    unfold normalizedAbsorptionDet
    field_simp [ne_of_gt h.transmission_pos]
  rw [responseAsymmetry_eq]
  exact ScalarEnvelope.scalar_deficit_of_envelope h (abs_nonneg _)
    (halfAsymmetry_le_b rL rR t) hc
    (by rw [he]; exact absorption_det_le_envelope rL rR t)

/-- Strictness at the matrix level follows when its actual absorption determinant is positive.
Positive distributed physical loss still needs its separate Maxwell/Gram proof. -/
theorem active_matrix_strict_gap {rL rR t : ℂ} (hp : Passive rL rR t)
    (h : ScalarEnvelope.ActiveTarget (transmissionPower t) (meanAbsorptance rL rR t))
    (hd : 0 < (absorptionMatrix rL rR t).det.re) :
    responseAsymmetry rL rR t <
      ScalarEnvelope.D0 (transmissionPower t) (meanAbsorptance rL rR t) := by
  have hc : 0 < normalizedAbsorptionDet rL rR t := div_pos hd h.transmission_pos
  have ha := (ScalarEnvelope.active_target_properties h).2.2.2.2.2.2.2
  have hb := active_matrix_deficit hp h
  have hprod := mul_pos ha hc
  linarith

#print axioms passive_absorptances_nonneg
#print axioms passive_det_nonneg
#print axioms reflection_coordinates
#print axioms halfAsymmetry_le_b
#print axioms interference_reverse_triangle
#print axioms reflection_product_sqrt
#print axioms absorption_det_le_envelope
#print axioms responseAsymmetry_eq
#print axioms active_matrix_deficit
#print axioms active_matrix_strict_gap

end
end OQ7
