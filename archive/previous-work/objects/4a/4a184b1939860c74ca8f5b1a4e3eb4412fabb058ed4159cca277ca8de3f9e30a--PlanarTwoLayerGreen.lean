import work.PlanarLayerField

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped Classical

def planarTwoLayerCurrent (h L : ℝ) (qA qW : ℝ → ℂ) : ℝ → ℂ :=
  fun t => (Ioc 0 h).indicator qA t + (Ioc h L).indicator qW t

theorem planarGreen_integral_indicator (k a b z : ℝ) (hab : a ≤ b) (q : ℝ → ℂ) :
    (∫ t : ℝ, planarScalarGreen k (z - t) * (Ioc a b).indicator q t) =
      ∫ t in a..b, planarScalarGreen k (z - t) * q t := by
  have he : (fun t => planarScalarGreen k (z - t) * (Ioc a b).indicator q t) =
      (Ioc a b).indicator (fun t => planarScalarGreen k (z - t) * q t) := by
    funext t
    by_cases ht : t ∈ Ioc a b <;> simp [ht]
  rw [he, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]

theorem planarGreen_indicator_integrable (k a b z : ℝ) (q : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b)) :
    Integrable (fun t => planarScalarGreen k (z - t) * (Ioc a b).indicator q t) volume := by
  have hg : Continuous (planarScalarGreen k) :=
    continuous_const.mul ((apertureOscillation_continuous k).comp continuous_abs)
  have hc : ContinuousOn (fun t => planarScalarGreen k (z - t) * q t) (Icc a b) :=
    (hg.comp (continuous_const.sub continuous_id)).continuousOn.mul hq
  have hi : IntegrableOn (fun t => planarScalarGreen k (z - t) * q t) (Ioc a b) volume :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  convert hi.integrable_indicator measurableSet_Ioc using 1
  funext t
  by_cases ht : t ∈ Ioc a b <;> simp [ht]

theorem planarTwoLayerGreen_integral (k h L z : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (qA qW : ℝ → ℂ) (hA : ContinuousOn qA (Icc 0 h)) (hW : ContinuousOn qW (Icc h L)) :
    (∫ t : ℝ, planarScalarGreen k (z - t) * planarTwoLayerCurrent h L qA qW t) =
      (∫ t in (0 : ℝ)..h, planarScalarGreen k (z - t) * qA t) +
        ∫ t in h..L, planarScalarGreen k (z - t) * qW t := by
  unfold planarTwoLayerCurrent
  simp_rw [mul_add]
  rw [integral_add (planarGreen_indicator_integrable k 0 h z qA hA)
      (planarGreen_indicator_integrable k h L z qW hW),
    planarGreen_integral_indicator k 0 h z hh qA, planarGreen_integral_indicator k h L z hL qW]

theorem planarTwoLayerGreen_interior_representation (k h L z : ℝ) (hk : k ≠ 0)
    (hh : 0 ≤ h) (hL : h ≤ L) (hz : z ∈ Icc 0 L)
    (A : PlanarLayerField k 0 h) (W : PlanarLayerField k h L)
    (hE : A.electric h = W.electric h) (hH : A.magnetic h = W.magnetic h) :
    (k : ℂ) ^ 2 * (∫ t : ℝ, planarScalarGreen k (z - t) *
        planarTwoLayerCurrent h L A.current W.current t) =
      (if z ≤ h then A.electric z else W.electric z) -
        (1 / 2 : ℂ) * apertureOscillation k z * (A.magnetic 0 + A.electric 0) +
        (1 / 2 : ℂ) * apertureOscillation k (L - z) * (W.magnetic L - W.electric L) := by
  rw [planarTwoLayerGreen_integral k h L z hh hL A.current W.current
    A.current_continuous W.current_continuous, mul_add]
  by_cases hzh : z ≤ h
  · rw [if_pos hzh,
      planarGreen_interval_interior_representation k 0 h z hk hz.1 hzh A.electric A.magnetic A.current
        A.electric_continuous A.magnetic_continuous A.current_continuous A.electric_derivative A.magnetic_derivative,
      planarGreen_interval_exterior_left_representation k h L z hk hL hzh W.electric W.magnetic W.current
        W.electric_continuous W.magnetic_continuous W.current_continuous W.electric_derivative W.magnetic_derivative,
      ← hE, ← hH, sub_zero]
    ring
  · have hhz : h ≤ z := (lt_of_not_ge hzh).le
    rw [if_neg hzh,
      planarGreen_interval_exterior_right_representation k 0 h z hk hh hhz A.electric A.magnetic A.current
        A.electric_continuous A.magnetic_continuous A.current_continuous A.electric_derivative A.magnetic_derivative,
      planarGreen_interval_interior_representation k h L z hk hhz hz.2 W.electric W.magnetic W.current
        W.electric_continuous W.magnetic_continuous W.current_continuous W.electric_derivative W.magnetic_derivative,
      hE, hH, sub_zero]
    ring

end OQ7Prescribed
