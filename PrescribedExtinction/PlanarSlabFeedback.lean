import PrescribedExtinction.PlanarSlabCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

def slabFeedback (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : ℂ :=
  1 - dielectricSlabReflection k A.p A.q A.width * dielectricSlabReflection k W.p W.q W.width * (Real.cos θ : ℂ) ^ 2

theorem dielectricSlabReflection_norm_lt_one (k : ℝ) (hk : 0 < k) (p q d : ℝ)
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) : ‖dielectricSlabReflection k p q d‖ < 1 := by
  have h := dielectricSlabReflection_normSq_lt_one k hk p q d hp hq hd
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (dielectricSlabReflection k p q d)]

theorem slabFeedback_ne_zero (k : ℝ) (hk : 0 < k) (A W : OQ7.HomogeneousLayer)
    (hpA : 1 ≤ A.p) (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width)
    (hpW : 1 ≤ W.p) (hqW : 0 ≤ W.q) (hdW : 0 ≤ W.width) (θ : ℝ) :
    slabFeedback k A W θ ≠ 0 := by
  have hA := dielectricSlabReflection_norm_lt_one k hk A.p A.q A.width hpA hqA hdA
  have hW := dielectricSlabReflection_norm_lt_one k hk W.p W.q W.width hpW hqW hdW
  have hc : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_add_sin_sq θ, sq_nonneg (Real.sin θ)]
  intro hz
  have he := congrArg norm (sub_eq_zero.mp hz)
  simp only [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at he
  have hprod : ‖dielectricSlabReflection k A.p A.q A.width‖ * ‖dielectricSlabReflection k W.p W.q W.width‖ < 1 := by
    calc
      _ ≤ ‖dielectricSlabReflection k A.p A.q A.width‖ * 1 := mul_le_mul_of_nonneg_left hW.le (norm_nonneg _)
      _ < 1 := by simpa using hA
  have hbound := mul_le_mul_of_nonneg_left hc (mul_nonneg
    (norm_nonneg (dielectricSlabReflection k A.p A.q A.width)) (norm_nonneg (dielectricSlabReflection k W.p W.q W.width)))
  linarith

def slabPlusPlateAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : ℂ :=
  apertureOscillation k A.width / slabFeedback k A W θ

def slabPlusAbsorberAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) * dielectricSlabReflection k W.p W.q W.width * slabPlusPlateAmplitude k A W θ

def slabMinusRightAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) : ℂ :=
  apertureOscillation (-k) (A.width + W.width)

def slabMinusAbsorberAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) * (dielectricSlabTransmission k W.p W.q W.width - apertureOscillation k W.width) *
    slabMinusRightAmplitude k A W / slabFeedback k A W θ

def slabMinusPlateLeftAmplitude (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) * dielectricSlabReflection k A.p A.q A.width * slabMinusAbsorberAmplitude k A W θ

theorem slabPlusAmplitudes_feedback (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ)
    (hD : slabFeedback k A W θ ≠ 0) :
    slabPlusPlateAmplitude k A W θ = apertureOscillation k A.width +
      (Real.cos θ : ℂ) * dielectricSlabReflection k A.p A.q A.width * slabPlusAbsorberAmplitude k A W θ := by
  unfold slabPlusAbsorberAmplitude slabPlusPlateAmplitude
  field_simp [hD]
  unfold slabFeedback
  ring

theorem slabMinusAmplitudes_feedback (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ)
    (hD : slabFeedback k A W θ ≠ 0) :
    slabMinusAbsorberAmplitude k A W θ = (Real.cos θ : ℂ) *
      ((dielectricSlabTransmission k W.p W.q W.width - apertureOscillation k W.width) * slabMinusRightAmplitude k A W +
        dielectricSlabReflection k W.p W.q W.width * slabMinusPlateLeftAmplitude k A W θ) := by
  unfold slabMinusPlateLeftAmplitude slabMinusAbsorberAmplitude
  field_simp [hD]
  unfold slabFeedback
  ring

end OQ7Prescribed
