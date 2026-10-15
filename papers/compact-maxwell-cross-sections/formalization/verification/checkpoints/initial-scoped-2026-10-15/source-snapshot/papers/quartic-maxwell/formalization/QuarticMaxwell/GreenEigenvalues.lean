import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! The sharp oscillatory cancellation in the actual radial/tangential
dynamic-minus-static dyadic eigenvalues. A Schur test and the sharp volume
rearrangement inequality are still needed for the continuum operator norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set

def greenB (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (u : ℂ)) * (Complex.I * (u : ℂ) - 1) + 1

theorem greenB_hasDerivAt (u : ℝ) :
    HasDerivAt greenB (-(u : ℂ) * Complex.exp (Complex.I * (u : ℂ))) u := by
  have hi := (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul Complex.I
  have he := hi.cexp
  have hb := (he.mul (hi.sub_const 1)).add_const 1
  have hformula : Complex.exp (Complex.I * (u : ℂ)) * Complex.I *
      (Complex.I * (u : ℂ) - 1) + Complex.exp (Complex.I * (u : ℂ)) * Complex.I =
      -(u : ℂ) * Complex.exp (Complex.I * (u : ℂ)) := by
    linear_combination (u : ℂ) * Complex.exp (Complex.I * (u : ℂ)) * Complex.I_sq
  convert hb using 1
  all_goals
    first
    | rfl
    | simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using hformula.symm

theorem greenB_integral (u : ℝ) :
    greenB u = ∫ s in (0 : ℝ)..u, -(s : ℂ) * Complex.exp (Complex.I * (s : ℂ)) := by
  have hc : Continuous (fun s : ℝ => -(s : ℂ) * Complex.exp (Complex.I * (s : ℂ))) := by
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => greenB_hasDerivAt s) (hc.intervalIntegrable 0 u)
  simpa [greenB] using h.symm

/-- The sharp `u²/2` cancellation is proved from the derivative integral;
there is no exponentially growing Taylor envelope. -/
theorem greenB_norm_le {u : ℝ} (hu : 0 ≤ u) : ‖greenB u‖ ≤ u ^ 2 / 2 := by
  rw [greenB_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (a := 0) (b := u)
    (f := fun s : ℝ => -(s : ℂ) * Complex.exp (Complex.I * (s : ℂ)))
    (g := fun s : ℝ => s) hu
    (ae_of_all _ (fun s hs => by
      simp [norm_mul, Complex.norm_exp, abs_of_nonneg hs.1.le]))
    (continuous_id.intervalIntegrable 0 u)
  simpa using h

def radialRemainderEigenvalue (k r : ℝ) : ℂ :=
  (-2 * greenB (k * r)) / (((4 * Real.pi * r ^ 3 : ℝ) : ℂ))

def tangentialRemainderEigenvalue (k r : ℝ) : ℂ :=
  (((k * r) ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((k * r : ℝ) : ℂ)) /
    (((4 * Real.pi * r ^ 3 : ℝ) : ℂ)) +
    greenB (k * r) / (((4 * Real.pi * r ^ 3 : ℝ) : ℂ))

theorem radial_eigenvalue_norm_le {k r : ℝ} (hk : 0 ≤ k) (hr : 0 < r) :
    ‖radialRemainderEigenvalue k r‖ ≤ 3 * k ^ 2 / (8 * Real.pi * r) := by
  have hb := greenB_norm_le (mul_nonneg hk hr.le)
  have hp : 0 < 4 * Real.pi * r ^ 3 := by positivity
  have hnormden : ‖(((4 * Real.pi * r ^ 3 : ℝ) : ℂ))‖ = 4 * Real.pi * r ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  unfold radialRemainderEigenvalue
  rw [norm_div, norm_mul, norm_neg, Complex.norm_two, hnormden]
  calc
    _ ≤ 2 * ((k * r) ^ 2 / 2) / (4 * Real.pi * r ^ 3) := by gcongr
    _ = k ^ 2 / (4 * Real.pi * r) := by field_simp <;> ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hpos : 0 ≤ k ^ 2 * Real.pi * r := by positivity
      nlinarith

theorem tangential_eigenvalue_norm_le {k r : ℝ} (hk : 0 ≤ k) (hr : 0 < r) :
    ‖tangentialRemainderEigenvalue k r‖ ≤ 3 * k ^ 2 / (8 * Real.pi * r) := by
  have hb := greenB_norm_le (mul_nonneg hk hr.le)
  have hp : 0 < 4 * Real.pi * r ^ 3 := by positivity
  have hnormden : ‖(((4 * Real.pi * r ^ 3 : ℝ) : ℂ))‖ = 4 * Real.pi * r ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have hnormnum : ‖(((k * r) ^ 2 : ℝ) : ℂ)‖ = (k * r) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hexp : ‖Complex.exp (Complex.I * ((k * r : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  unfold tangentialRemainderEigenvalue
  calc
    _ ≤ ‖(((k * r) ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((k * r : ℝ) : ℂ)) /
        (((4 * Real.pi * r ^ 3 : ℝ) : ℂ))‖ +
        ‖greenB (k * r) / (((4 * Real.pi * r ^ 3 : ℝ) : ℂ))‖ := norm_add_le _ _
    _ = (k * r) ^ 2 / (4 * Real.pi * r ^ 3) +
        ‖greenB (k * r)‖ / (4 * Real.pi * r ^ 3) := by
      rw [norm_div, norm_div, norm_mul, hnormnum, hexp, hnormden, mul_one]
    _ ≤ (k * r) ^ 2 / (4 * Real.pi * r ^ 3) +
        ((k * r) ^ 2 / 2) / (4 * Real.pi * r ^ 3) := by gcongr
    _ = _ := by field_simp <;> ring

end QuarticMaxwell
