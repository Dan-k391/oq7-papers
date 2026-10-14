import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import OQ7.TwoPort

noncomputable section
namespace OQ7
open MeasureTheory Set

theorem cosine_cap_majorant {q Q c v : ℝ} (hq : 0 ≤ q) (hcap : q ≤ Q) :
    q * v ≤ c * q + Q * max (v - c) 0 := by
  by_cases h : c ≤ v
  · rw [max_eq_left (sub_nonneg.mpr h)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcap) (sub_nonneg.mpr h)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr (le_of_not_ge h))]

theorem positive_cosine_integral {lam : ℝ} (hlam : 0 ≤ lam) (hlamπ : lam ≤ Real.pi) :
    (∫ θ in -Real.pi..Real.pi, max (Real.cos θ - Real.cos lam) 0) =
      2 * (Real.sin lam - lam * Real.cos lam) := by
  let f : ℝ → ℝ := fun θ => max (Real.cos θ - Real.cos lam) 0
  have hf : Continuous f := (Real.continuous_cos.sub continuous_const).max continuous_const
  have houtLeft : (∫ θ in -Real.pi..-lam, f θ) = 0 := by
    calc
      _ = ∫ θ in -Real.pi..-lam, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le (by linarith : -Real.pi ≤ -lam)] at hθ
        have hc : Real.cos θ ≤ Real.cos lam := by
          rw [← Real.cos_neg θ]
          exact Real.cos_le_cos_of_nonneg_of_le_pi hlam
            (by linarith [hθ.1]) (by linarith [hθ.2])
        exact max_eq_right (sub_nonpos.mpr hc)
      _ = 0 := by simp
  have houtRight : (∫ θ in lam..Real.pi, f θ) = 0 := by
    calc
      _ = ∫ θ in lam..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le hlamπ] at hθ
        have hc := Real.cos_le_cos_of_nonneg_of_le_pi hlam hθ.2 hθ.1
        exact max_eq_right (sub_nonpos.mpr hc)
      _ = 0 := by simp
  have hmiddle : (∫ θ in -lam..lam, f θ) =
      2 * (Real.sin lam - lam * Real.cos lam) := by
    calc
      _ = ∫ θ in -lam..lam, Real.cos θ - Real.cos lam := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le (by linarith : -lam ≤ lam)] at hθ
        have hθabs : |θ| ≤ lam := abs_le.mpr hθ
        have hc : Real.cos lam ≤ Real.cos θ := by
          rw [← Real.cos_abs θ]
          exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hlamπ hθabs
        exact max_eq_left (sub_nonneg.mpr hc)
      _ = 2 * (Real.sin lam - lam * Real.cos lam) := by
        rw [intervalIntegral.integral_sub (Real.continuous_cos.intervalIntegrable (-lam) lam)
          (continuous_const.intervalIntegrable (-lam) lam), integral_cos,
          intervalIntegral.integral_const]
        simp only [Real.sin_neg, smul_eq_mul]
        ring
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-Real.pi) (-lam))
    (hf.intervalIntegrable (μ := volume) (-lam) lam)
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-Real.pi) lam)
    (hf.intervalIntegrable (μ := volume) lam Real.pi)
  change (∫ θ in -Real.pi..Real.pi, f θ) = _
  rw [← hsplit₂, ← hsplit₁, houtLeft, houtRight, hmiddle]
  ring

theorem positive_cosine_physical_period {K lam : ℝ} (hK : 0 < K)
    (hlam : 0 ≤ lam) (hlamπ : lam ≤ Real.pi) (a φ : ℝ) :
    (∫ z in a..a + Real.pi / K, max (Real.cos (2 * K * z - φ) - Real.cos lam) 0) =
      (Real.sin lam - lam * Real.cos lam) / K := by
  let f : ℝ → ℝ := fun θ => max (Real.cos θ - Real.cos lam) 0
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro θ
    simp [f, Real.cos_add_two_pi]
  have hshift := hp.intervalIntegral_add_eq (2 * K * a - φ) (-Real.pi)
  have hend : 2 * K * (a + Real.pi / K) - φ =
      (2 * K * a - φ) + 2 * Real.pi := by field_simp; ring
  change (∫ z in a..a + Real.pi / K, f (2 * K * z - φ)) = _
  rw [intervalIntegral.integral_comp_mul_sub f (mul_ne_zero two_ne_zero hK.ne') φ,
    hend, hshift]
  have hπ : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hπ]
  change (2 * K)⁻¹ * (∫ θ in -Real.pi..Real.pi, max (Real.cos θ - Real.cos lam) 0) = _
  rw [positive_cosine_integral hlam hlamπ]
  field_simp

theorem capped_cosine_moment {q : ℝ → ℝ} {a b K Q : ℝ}
    (hab : a ≤ b) (hK : 0 < K) (hQ : 0 < Q)
    (hlength : b - a ≤ Real.pi / K)
    (hq : IntervalIntegrable q volume a b)
    (hcap : ∀ z ∈ Icc a b, 0 ≤ q z ∧ q z ≤ Q) (φ : ℝ) :
    (∫ z in a..b, q z * Real.cos (2 * K * z - φ)) ≤
      Q / K * Real.sin (K * (∫ z in a..b, q z) / Q) := by
  let m : ℝ := ∫ z in a..b, q z
  let lam : ℝ := K * m / Q
  have hm : 0 ≤ m := intervalIntegral.integral_nonneg hab (fun z hz => (hcap z hz).1)
  have hmcap : m ≤ Q * (b - a) := by
    have h := intervalIntegral.integral_mono_on hab hq
      (continuous_const.intervalIntegrable a b) (fun z hz => (hcap z hz).2)
    simpa [m, smul_eq_mul, mul_comm] using h
  have hlam : 0 ≤ lam := div_nonneg (mul_nonneg hK.le hm) hQ.le
  have hlamπ : lam ≤ Real.pi := by
    apply (div_le_iff₀ hQ).mpr
    have hmperiod : m ≤ Q * (Real.pi / K) :=
      hmcap.trans (mul_le_mul_of_nonneg_left hlength hQ.le)
    have hmul := mul_le_mul_of_nonneg_left hmperiod hK.le
    have hcancel : K * (Q * (Real.pi / K)) = Real.pi * Q := by field_simp
    rwa [hcancel] at hmul
  let r : ℝ → ℝ := fun z => max (Real.cos (2 * K * z - φ) - Real.cos lam) 0
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hc : Continuous (fun z : ℝ => Real.cos (2 * K * z - φ)) := by fun_prop
  have hmajor := intervalIntegral.integral_mono_on hab (hq.mul_continuousOn hc.continuousOn)
    ((hq.const_mul (Real.cos lam)).add ((hr.intervalIntegrable a b).const_mul Q))
    (fun z hz => cosine_cap_majorant (hcap z hz).1 (hcap z hz).2)
  rw [intervalIntegral.integral_add (hq.const_mul (Real.cos lam))
    ((hr.intervalIntegrable a b).const_mul Q), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmajor
  have hperiodBound : (∫ z in a..b, r z) ≤
      (Real.sin lam - lam * Real.cos lam) / K := by
    calc
      _ ≤ ∫ z in a..a + Real.pi / K, r z :=
        intervalIntegral.integral_mono_interval le_rfl hab (by linarith)
          (Filter.Eventually.of_forall (fun z => le_max_right _ _))
          (hr.intervalIntegrable a (a + Real.pi / K))
      _ = _ := positive_cosine_physical_period hK hlam hlamπ a φ
  have hmul := mul_le_mul_of_nonneg_left hperiodBound hQ.le
  have hcancel : Real.cos lam * m + Q * ((Real.sin lam - lam * Real.cos lam) / K) =
      Q / K * Real.sin lam := by
    dsimp [lam]
    field_simp
    ring
  change (∫ z in a..b, q z * Real.cos (2 * K * z - φ)) ≤ Q / K * Real.sin lam
  rw [← hcancel]
  change (∫ z in a..b, q z * Real.cos (2 * K * z - φ)) ≤
    Real.cos lam * m + Q * (∫ z in a..b, r z) at hmajor
  linarith

theorem capped_fourier_moment {q : ℝ → ℝ} {a b K Q : ℝ}
    (hab : a ≤ b) (hK : 0 < K) (hQ : 0 < Q)
    (hlength : b - a ≤ Real.pi / K)
    (hq : IntervalIntegrable q volume a b)
    (hcap : ∀ z ∈ Icc a b, 0 ≤ q z ∧ q z ≤ Q) :
    ‖∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)‖ ≤
      Q / K * Real.sin (K * (∫ z in a..b, q z) / Q) := by
  let M : ℂ := ∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)
  let φ := M.arg
  have hqc : IntervalIntegrable (fun z => (q z : ℂ)) volume a b := ⟨hq.1.ofReal, hq.2.ofReal⟩
  have he : Continuous (fun z : ℝ => Complex.exp ((2 * K * z : ℝ) * Complex.I)) := by fun_prop
  have hMc := hqc.mul_continuousOn he.continuousOn
  have hre : (∫ z in a..b, q z * Real.cos (2 * K * z)) = M.re := by
    have h := intervalIntegral.intervalIntegral_re hMc
    simpa only [M, RCLike.re_eq_complex_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      zero_mul, sub_zero] using h
  have him : (∫ z in a..b, q z * Real.sin (2 * K * z)) = M.im := by
    have h := intervalIntegral.intervalIntegral_im hMc
    simpa only [M, RCLike.im_eq_complex_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero] using h
  have hc : Continuous (fun z : ℝ => Real.cos (2 * K * z)) := by fun_prop
  have hs : Continuous (fun z : ℝ => Real.sin (2 * K * z)) := by fun_prop
  have hφ : (∫ z in a..b, q z * Real.cos (2 * K * z - φ)) = ‖M‖ := by
    calc
      _ = ∫ z in a..b,
          Real.cos φ * (q z * Real.cos (2 * K * z)) +
          Real.sin φ * (q z * Real.sin (2 * K * z)) := by
        apply intervalIntegral.integral_congr
        intro z _
        dsimp only
        rw [Real.cos_sub]
        ring
      _ = Real.cos φ * M.re + Real.sin φ * M.im := by
        rw [intervalIntegral.integral_add
          ((hq.mul_continuousOn hc.continuousOn).const_mul (Real.cos φ))
          ((hq.mul_continuousOn hs.continuousOn).const_mul (Real.sin φ)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hre, him]
      _ = ‖M‖ := by
        rw [← Complex.norm_mul_cos_arg M, ← Complex.norm_mul_sin_arg M]
        change Real.cos M.arg * (‖M‖ * Real.cos M.arg) +
          Real.sin M.arg * (‖M‖ * Real.sin M.arg) = ‖M‖
        calc
          _ = ‖M‖ * (Real.sin M.arg ^ 2 + Real.cos M.arg ^ 2) := by ring
          _ = ‖M‖ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hb := capped_cosine_moment hab hK hQ hlength hq hcap φ
  rw [hφ] at hb
  exact hb

#print axioms cosine_cap_majorant
#print axioms positive_cosine_integral
#print axioms positive_cosine_physical_period
#print axioms capped_cosine_moment
#print axioms capped_fourier_moment
end OQ7

