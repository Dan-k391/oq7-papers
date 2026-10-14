import PrescribedExtinction.BodySlabGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Classical

theorem horizontalSquareAperture_isOpen (R : ℝ) : IsOpen (horizontalSquareAperture R) := by
  unfold horizontalSquareAperture
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

theorem horizontalSquareAperture_volume (R : ℝ) (hR : 0 ≤ R) :
    volume (horizontalSquareAperture R) = ENNReal.ofReal (R ^ 2) := by
  have hs : horizontalSquareAperture R = Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-R / 2) (R / 2) ×ˢ Ioo (-R / 2) (R / 2)) := by
    ext z
    simp [horizontalSquareAperture, and_assoc]
  rw [hs, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
  have he : R / 2 - -R / 2 = R := by ring
  rw [he, ← ENNReal.ofReal_mul hR, ← pow_two]

def squareApertureWindow (R : ℝ) : ℂ → ℂ :=
  (horizontalSquareAperture R).indicator (fun _ => 1)

theorem squareApertureWindow_memLp (R : ℝ) : MemLp (squareApertureWindow R) 2 volume := by
  apply memLp_indicator_const _ (horizontalSquareAperture_isOpen R).measurableSet _
  right
  by_cases hR : 0 ≤ R
  · rw [horizontalSquareAperture_volume R hR]
    exact ENNReal.ofReal_ne_top
  · have hs : horizontalSquareAperture R = ∅ := by
      ext z
      simp only [horizontalSquareAperture, mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hz
      linarith [hz.1, hz.2.1]
    rw [hs, measure_empty]
    exact ENNReal.zero_ne_top

theorem horizontalSquareAperture_scaled_iff (R : ℝ) (hR : 0 < R) (z : ℂ) :
    R⁻¹ • z ∈ horizontalSquareAperture 1 ↔ z ∈ horizontalSquareAperture R := by
  have hr (t : ℝ) : R * (R⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  have hcoord (t : ℝ) : (-(1 : ℝ) / 2 < R⁻¹ * t ∧ R⁻¹ * t < 1 / 2) ↔
      (-R / 2 < t ∧ t < R / 2) := by
    constructor
    · intro ht
      have h1 := mul_lt_mul_of_pos_left ht.1 hR
      have h2 := mul_lt_mul_of_pos_left ht.2 hR
      rw [hr] at h1 h2
      constructor <;> linarith
    · intro ht
      have h1 := mul_lt_mul_of_pos_left ht.1 (inv_pos.mpr hR)
      have h2 := mul_lt_mul_of_pos_left ht.2 (inv_pos.mpr hR)
      have hi : R⁻¹ * R = 1 := inv_mul_cancel₀ hR.ne'
      have h1' : R⁻¹ * (-R / 2) = -(1 : ℝ) / 2 := by calc
        _ = -(R⁻¹ * R) / 2 := by ring
        _ = _ := by rw [hi]
      have h2' : R⁻¹ * (R / 2) = (1 : ℝ) / 2 := by calc
        _ = (R⁻¹ * R) / 2 := by ring
        _ = _ := by rw [hi]
      rw [h1'] at h1
      rw [h2'] at h2
      exact ⟨h1, h2⟩
  simp only [horizontalSquareAperture, mem_setOf_eq, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, zero_add, add_zero]
  simpa only [and_assoc] using and_congr (hcoord z.re) (hcoord z.im)

theorem squareApertureWindow_scaled (R : ℝ) (hR : 0 < R) :
    squareApertureWindow R = scaledApertureWindow (squareApertureWindow 1) R := by
  funext z
  unfold squareApertureWindow scaledApertureWindow
  change (horizontalSquareAperture R).indicator (fun _ => (1 : ℂ)) z =
    (horizontalSquareAperture 1).indicator (fun _ => (1 : ℂ)) (R⁻¹ • z)
  by_cases hz : z ∈ horizontalSquareAperture R
  · rw [indicator_of_mem hz, indicator_of_mem ((horizontalSquareAperture_scaled_iff R hR z).mpr hz)]
  · rw [indicator_of_notMem hz, indicator_of_notMem ((horizontalSquareAperture_scaled_iff R hR z).not.mpr hz)]

end OQ7Prescribed

