import PrescribedExtinction.ApertureOscillation
import OQ7.Fields

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarWaveMomentPlus_hasDerivAt (k t : ℝ) (E H q : ℝ → ℂ)
    (hE : HasDerivAt E (Complex.I * (k : ℂ) * H t) t)
    (hH : HasDerivAt H (Complex.I * (k : ℂ) * (E t + q t)) t) :
    HasDerivAt (fun z => apertureOscillation (-k) z * (H z + E z))
      (Complex.I * (k : ℂ) * (apertureOscillation (-k) t * q t)) t := by
  convert (apertureOscillation_hasDerivAt (-k) t).mul (hH.add hE) using 1
  simp only [Complex.ofReal_neg, Pi.add_apply]
  ring

theorem planarWaveMomentMinus_hasDerivAt (k t : ℝ) (E H q : ℝ → ℂ)
    (hE : HasDerivAt E (Complex.I * (k : ℂ) * H t) t)
    (hH : HasDerivAt H (Complex.I * (k : ℂ) * (E t + q t)) t) :
    HasDerivAt (fun z => apertureOscillation k z * (H z - E z))
      (Complex.I * (k : ℂ) * (apertureOscillation k t * q t)) t := by
  convert (apertureOscillation_hasDerivAt k t).mul (hH.sub hE) using 1
  simp only [Pi.sub_apply]
  ring

theorem planarWaveMoments_boundary (k a b : ℝ) (hab : a ≤ b) (E H q : ℝ → ℂ)
    (hEc : ContinuousOn E (Icc a b)) (hHc : ContinuousOn H (Icc a b))
    (hqc : ContinuousOn q (Icc a b))
    (hE : ∀ t ∈ Ioo a b, HasDerivAt E (Complex.I * (k : ℂ) * H t) t)
    (hH : ∀ t ∈ Ioo a b, HasDerivAt H (Complex.I * (k : ℂ) * (E t + q t)) t) :
    (Complex.I * (k : ℂ)) * (∫ t in a..b, apertureOscillation (-k) t * q t) =
      apertureOscillation (-k) b * (H b + E b) - apertureOscillation (-k) a * (H a + E a) ∧
    (Complex.I * (k : ℂ)) * (∫ t in a..b, apertureOscillation k t * q t) =
      apertureOscillation k b * (H b - E b) - apertureOscillation k a * (H a - E a) := by
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    · exact (apertureOscillation_continuous (-k)).continuousOn.mul (hHc.add hEc)
    · intro t ht
      exact planarWaveMomentPlus_hasDerivAt k t E H q (hE t ht) (hH t ht)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact continuousOn_const.mul ((apertureOscillation_continuous (-k)).continuousOn.mul hqc)
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    · exact (apertureOscillation_continuous k).continuousOn.mul (hHc.sub hEc)
    · intro t ht
      exact planarWaveMomentMinus_hasDerivAt k t E H q (hE t ht) (hH t ht)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact continuousOn_const.mul ((apertureOscillation_continuous k).continuousOn.mul hqc)

theorem homogeneousField_planarWaveMoments (k a b : ℝ) (hab : a ≤ b) (n E₀ H₀ : ℂ)
    (hn : n ≠ 0) :
    (Complex.I * (k : ℂ)) *
      (∫ t in a..b, apertureOscillation (-k) t * ((n ^ 2 - 1) * OQ7.electricField k n E₀ H₀ t)) =
        apertureOscillation (-k) b * (OQ7.magneticField k n E₀ H₀ b + OQ7.electricField k n E₀ H₀ b) -
        apertureOscillation (-k) a * (OQ7.magneticField k n E₀ H₀ a + OQ7.electricField k n E₀ H₀ a) ∧
    (Complex.I * (k : ℂ)) *
      (∫ t in a..b, apertureOscillation k t * ((n ^ 2 - 1) * OQ7.electricField k n E₀ H₀ t)) =
        apertureOscillation k b * (OQ7.magneticField k n E₀ H₀ b - OQ7.electricField k n E₀ H₀ b) -
        apertureOscillation k a * (OQ7.magneticField k n E₀ H₀ a - OQ7.electricField k n E₀ H₀ a) := by
  have hEc : Continuous (OQ7.electricField k n E₀ H₀) :=
    continuous_iff_continuousAt.mpr fun t => (OQ7.electricField_hasDerivAt k hn E₀ H₀ t).continuousAt
  have hHc : Continuous (OQ7.magneticField k n E₀ H₀) :=
    continuous_iff_continuousAt.mpr fun t => (OQ7.magneticField_hasDerivAt k hn E₀ H₀ t).continuousAt
  apply planarWaveMoments_boundary k a b hab _ _ _ hEc.continuousOn hHc.continuousOn
    (continuous_const.mul hEc).continuousOn
  · intro t _
    exact OQ7.electricField_hasDerivAt k hn E₀ H₀ t
  · intro t _
    convert OQ7.magneticField_hasDerivAt k hn E₀ H₀ t using 1
    simp only [Pi.mul_apply]
    ring

end OQ7Prescribed
