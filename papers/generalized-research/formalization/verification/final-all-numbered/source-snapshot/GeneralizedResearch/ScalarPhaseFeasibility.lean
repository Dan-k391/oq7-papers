import GeneralizedResearch.ScalarBenchmark
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Exact prescribed-entry phase and degenerate clauses of original
Proposition 2.1, for the literal complex reciprocal two-port matrix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace GeneralizedResearch.ScalarPhaseFeasibility
open OQ7 ScalarBenchmark
open scoped Matrix ComplexOrder

def phase (rL rR t : ℂ) : ℝ := rL.arg + rR.arg - 2 * t.arg

theorem reflection_sqrt (rL rR t : ℂ) :
    Real.sqrt ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 -
      |halfAsymmetry rL rR t| ^ 2) = ‖rL‖ * ‖rR‖ :=
  OQ7.reflection_product_sqrt rL rR t

def hermitianTwo (l r : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(l : ℂ), z; star z, (r : ℂ)]

theorem hermitianTwo_re (l r : ℝ) (z : ℂ) (v : Fin 2 → ℂ) :
    (star v ⬝ᵥ (hermitianTwo l r z *ᵥ v)).re =
      l * ‖v 0‖ ^ 2 + r * ‖v 1‖ ^ 2 + 2 * (star (v 0) * z * v 1).re := by
  simp [hermitianTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.sq_norm,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem hermitianTwo_im (l r : ℝ) (z : ℂ) (v : Fin 2 → ℂ) :
    (star v ⬝ᵥ (hermitianTwo l r z *ᵥ v)).im = 0 := by
  simp [hermitianTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

/-- Two-by-two complex Hermitian PSD, with singular diagonals included. -/
theorem complex_psd_two {l r : ℝ} {z : ℂ}
    (hl : 0 ≤ l) (hr : 0 ≤ r) (hd : ‖z‖ ^ 2 ≤ l * r) :
    (hermitianTwo l r z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianTwo, Matrix.conjTranspose_apply]
  · intro v
    apply Complex.nonneg_iff.mpr
    rw [hermitianTwo_re, hermitianTwo_im]
    refine ⟨?_, rfl⟩
    have hq := (real_psd_two (c := -‖z‖) hl hr (by simpa only [neg_sq] using hd)).dotProduct_mulVec_nonneg
      (![‖v 0‖, ‖v 1‖] : Fin 2 → ℝ)
    have hq' : 0 ≤ l * ‖v 0‖ ^ 2 - 2 * ‖z‖ * ‖v 0‖ * ‖v 1‖ + r * ‖v 1‖ ^ 2 := by
      convert hq using 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    have hc := (abs_le.mp (Complex.abs_re_le_norm (star (v 0) * z * v 1))).1
    simp only [norm_mul, norm_star] at hc
    nlinarith only [hq', hc]

theorem normSq_interference (rL rR t : ℂ) :
    Complex.normSq (interference rL rR t) =
      transmissionPower t * (Complex.normSq rL + Complex.normSq rR) +
        2 * (rL * rR * (star t) ^ 2).re := by
  simp [interference, transmissionPower, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem weighted_cos_phase (rL rR t : ℂ) :
    transmissionPower t * ‖rL‖ * ‖rR‖ * Real.cos (phase rL rR t) =
      (rL * rR * (star t) ^ 2).re := by
  calc
    _ = ((‖rL‖ * Real.cos rL.arg) * (‖rR‖ * Real.cos rR.arg) -
          (‖rL‖ * Real.sin rL.arg) * (‖rR‖ * Real.sin rR.arg)) *
          ((‖t‖ * Real.cos t.arg) ^ 2 - (‖t‖ * Real.sin t.arg) ^ 2) +
        ((‖rL‖ * Real.sin rL.arg) * (‖rR‖ * Real.cos rR.arg) +
          (‖rL‖ * Real.cos rL.arg) * (‖rR‖ * Real.sin rR.arg)) *
          (2 * (‖t‖ * Real.cos t.arg) * (‖t‖ * Real.sin t.arg)) := by
      unfold phase transmissionPower
      rw [Complex.normSq_eq_norm_sq, show 2 * t.arg = t.arg + t.arg by ring]
      simp only [Real.cos_sub, Real.cos_add, Real.sin_add]
      ring
    _ = _ := by
      simp only [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg, pow_two,
        Complex.mul_re, Complex.mul_im,
        show (star t).re = t.re from rfl, show (star t).im = -t.im from rfl]
      ring

theorem interference_phase_formula (rL rR t : ℂ) :
    Complex.normSq (interference rL rR t) = 2 * transmissionPower t *
      (b (transmissionPower t) (meanAbsorptance rL rR t) +
        Real.sqrt ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 -
          |halfAsymmetry rL rR t| ^ 2) * Real.cos (phase rL rR t)) := by
  have hr := reflection_coordinates rL rR t
  change Complex.normSq rL = b _ _ - _ ∧ Complex.normSq rR = b _ _ + _ at hr
  rw [normSq_interference, ← weighted_cos_phase, reflection_sqrt]
  rw [hr.1, hr.2]
  ring

def MagnitudeConditions (rL rR t : ℂ) : Prop :=
  ValidPair (transmissionPower t) (meanAbsorptance rL rR t) ∧
    |halfAsymmetry rL rR t| ≤ meanAbsorptance rL rR t ∧
    |halfAsymmetry rL rR t| ≤ b (transmissionPower t) (meanAbsorptance rL rR t)

theorem passive_iff_magnitudes_det (rL rR t : ℂ) :
    Passive rL rR t ↔ MagnitudeConditions rL rR t ∧
      0 ≤ meanAbsorptance rL rR t ^ 2 - |halfAsymmetry rL rR t| ^ 2 -
        Complex.normSq (interference rL rR t) := by
  constructor
  · intro hp
    have hf := passive_feasible rL rR t hp
    refine ⟨⟨hf.1, hf.2.1, hf.2.2.1⟩, ?_⟩
    have hd := passive_det_nonneg hp
    rw [absorption_det_coordinates, Complex.ofReal_re] at hd
    simpa only [sq_abs] using hd
  · rintro ⟨hm, hd⟩
    have hc := absorptance_coordinates rL rR t
    have hδ := abs_le.mp hm.2.1
    have hL : 0 ≤ absorptanceLeft rL t := by rw [hc.1]; linarith
    have hR : 0 ≤ absorptanceRight rR t := by rw [hc.2]; linarith
    have hdet : ‖-interference rL rR t‖ ^ 2 ≤ absorptanceLeft rL t * absorptanceRight rR t := by
      rw [norm_neg, ← Complex.normSq_eq_norm_sq, hc.1, hc.2]
      rw [sq_abs] at hd
      nlinarith only [hd]
    have hp := complex_psd_two hL hR hdet
    change (absorptionMatrix rL rR t).PosSemidef
    rw [absorptionMatrix_eq]
    simpa only [hermitianTwo, star_neg] using hp

/-- Original Eq. (6) for prescribed nonzero actual entries. -/
theorem prescribed_entry_phase_iff (rL rR t : ℂ) (hL : rL ≠ 0) (hR : rR ≠ 0) (ht : t ≠ 0) :
    Passive rL rR t ↔ MagnitudeConditions rL rR t ∧
      Real.cos (phase rL rR t) ≤
        (meanAbsorptance rL rR t ^ 2 - |halfAsymmetry rL rR t| ^ 2 -
          2 * transmissionPower t * b (transmissionPower t) (meanAbsorptance rL rR t)) /
        (2 * transmissionPower t * Real.sqrt
          ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2)) := by
  have hden : 0 < 2 * transmissionPower t * Real.sqrt
      ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2) := by
    rw [reflection_sqrt]
    exact mul_pos (mul_pos (by norm_num) (transmission_positive ht))
      (mul_pos (norm_pos_iff.mpr hL) (norm_pos_iff.mpr hR))
  rw [passive_iff_magnitudes_det, interference_phase_formula, le_div_iff₀ hden]
  constructor <;> rintro ⟨hm, h⟩ <;> refine ⟨hm, ?_⟩ <;> nlinarith only [h]

/-- The stated degenerate clause: there is no remaining phase restriction. -/
theorem degenerate_entry_iff (rL rR t : ℂ)
    (hdeg : transmissionPower t * ‖rL * rR‖ = 0) :
    Passive rL rR t ↔ MagnitudeConditions rL rR t ∧
      0 ≤ meanAbsorptance rL rR t ^ 2 - |halfAsymmetry rL rR t| ^ 2 -
        2 * transmissionPower t * b (transmissionPower t) (meanAbsorptance rL rR t) := by
  have hz : transmissionPower t * Real.sqrt
      ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2) = 0 := by
    rw [reflection_sqrt]
    simpa only [norm_mul, mul_assoc] using hdeg
  have he : Complex.normSq (interference rL rR t) =
      2 * transmissionPower t * b (transmissionPower t) (meanAbsorptance rL rR t) := by
    calc
      _ = 2 * transmissionPower t * b (transmissionPower t) (meanAbsorptance rL rR t) +
          2 * (transmissionPower t * Real.sqrt
            ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2)) *
              Real.cos (phase rL rR t) := by rw [interference_phase_formula]; ring
      _ = _ := by rw [hz]; ring
  rw [passive_iff_magnitudes_det, he]


abbrev PhaseCriterion (rL rR t : ℂ) : Prop :=
  Real.cos (phase rL rR t) ≤
    (meanAbsorptance rL rR t ^ 2 - |halfAsymmetry rL rR t| ^ 2 -
      2 * transmissionPower t * b (transmissionPower t) (meanAbsorptance rL rR t)) /
    (2 * transmissionPower t * Real.sqrt
      ((b (transmissionPower t) (meanAbsorptance rL rR t)) ^ 2 - |halfAsymmetry rL rR t| ^ 2))

abbrev DegenerateCriterion (rL rR t : ℂ) : Prop :=
  0 ≤ meanAbsorptance rL rR t ^ 2 - |halfAsymmetry rL rR t| ^ 2 -
    2 * transmissionPower t * b (transmissionPower t) (meanAbsorptance rL rR t)

theorem every_pair_feasible {T a : ℝ} (h : ValidPair T a) : Realized T a 0 :=
  (feasibility_iff T a 0).mpr (zero_feasible h)

/-- All clauses of the original numbered Proposition 2.1: scalar existence,
all feasible pairs, exact nonzero-entry phases, and the degenerate criterion. -/
theorem proposition21 :
    (∀ T a δ : ℝ, Realized T a δ ↔ Feasible T a δ) ∧
    (∀ T a : ℝ, ValidPair T a → Realized T a 0) ∧
    (∀ rL rR t : ℂ, rL ≠ 0 → rR ≠ 0 → t ≠ 0 →
      (Passive rL rR t ↔ MagnitudeConditions rL rR t ∧ PhaseCriterion rL rR t)) ∧
    (∀ rL rR t : ℂ, transmissionPower t * ‖rL * rR‖ = 0 →
      (Passive rL rR t ↔ MagnitudeConditions rL rR t ∧ DegenerateCriterion rL rR t)) := by
  exact ⟨feasibility_iff, fun _ _ => every_pair_feasible, prescribed_entry_phase_iff, degenerate_entry_iff⟩

end GeneralizedResearch.ScalarPhaseFeasibility
