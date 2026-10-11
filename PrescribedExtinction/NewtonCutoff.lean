import PrescribedExtinction.NewtonPrincipalValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Radial cutoffs for integration by parts outside a fixed Newtonian puncture.
The radii and the test functions are the actual ones in the Green framework. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Filter Set Metric
open scoped Topology

def transitionDerivative : ℝ → ℝ := deriv Real.smoothTransition

theorem transitionDerivative_continuous : Continuous transitionDerivative :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one

theorem transitionDerivative_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    transitionDerivative s = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Eventually.of_forall
  intro y
  simpa only [Real.smoothTransition.zero_of_nonpos hs] using Real.smoothTransition.nonneg y

theorem transitionDerivative_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    transitionDerivative s = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Eventually.of_forall
  intro y
  simpa only [Real.smoothTransition.one_of_one_le hs] using Real.smoothTransition.le_one y

theorem transitionDerivative_integral :
    (∫ s in (0 : ℝ)..1, transitionDerivative s) = 1 := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  simpa only [transitionDerivative, Real.smoothTransition.one,
    Real.smoothTransition.zero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hd s |>.hasDerivAt)
      (transitionDerivative_continuous.intervalIntegrable 0 1)

def exteriorCutoff (r t : ℝ) (x : Position) : ℝ :=
  Real.smoothTransition ((‖x‖ - r) / t)

theorem exteriorCutoff_zero {r t : ℝ} (ht : 0 < t) (x : Position) (hx : ‖x‖ ≤ r) :
    exteriorCutoff r t x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) ht.le)

theorem exteriorCutoff_one {r t : ℝ} (ht : 0 < t) (x : Position) (hx : r + t ≤ ‖x‖) :
    exteriorCutoff r t x = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ ht).mpr (by linarith))

theorem exteriorCutoff_nonneg (r t : ℝ) (x : Position) : 0 ≤ exteriorCutoff r t x :=
  Real.smoothTransition.nonneg _

theorem exteriorCutoff_le_one (r t : ℝ) (x : Position) : exteriorCutoff r t x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem exteriorCutoff_contDiff (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    ContDiff ℝ 1 (exteriorCutoff r t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simpa using hr)] with y hy
    exact exteriorCutoff_zero ht y hy.le
  · exact (Real.smoothTransition.contDiffAt (n := 1)).comp x
      (((contDiffAt_norm ℝ hx).sub contDiffAt_const).div_const t)

def exteriorCutoffPartial (r t : ℝ) (i : Fin 3) (x : Position) : ℝ :=
  transitionDerivative ((‖x‖ - r) / t) * (x i / ‖x‖) / t

theorem exteriorCutoff_hasLineDerivAt (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (i : Fin 3) (x : Position) :
    HasLineDerivAt ℝ (exteriorCutoff r t) (exteriorCutoffPartial r t i x) x (basisR i) := by
  by_cases hx : x = 0
  · subst x
    have he : exteriorCutoff r t =ᶠ[𝓝 (0 : Position)] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simpa using hr)] with y hy
      exact exteriorCutoff_zero ht y hy.le
    simpa [exteriorCutoffPartial, basisR] using
      (hasFDerivAt_const (E := Position) (0 : ℝ) (0 : Position)).hasLineDerivAt (basisR i) |>.congr_of_eventuallyEq he
  · have hd := (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    have hn : HasFDerivAt (fun y : Position => (‖y‖ - r) / t)
        (t⁻¹ • (‖x‖⁻¹ • innerSL ℝ x)) x := by
      simpa only [div_eq_mul_inv, mul_comm] using
        ((radialNorm_hasFDerivAt x hx).sub_const r).const_mul t⁻¹
    have h := ((hd ((‖x‖ - r) / t)).hasDerivAt.hasFDerivAt.comp x hn).hasLineDerivAt (basisR i)
    convert h using 1
    · funext y
      simp [exteriorCutoff, div_eq_mul_inv]
    · simp [exteriorCutoffPartial, transitionDerivative, real_inner_basis,
        div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

end OQ7Prescribed
