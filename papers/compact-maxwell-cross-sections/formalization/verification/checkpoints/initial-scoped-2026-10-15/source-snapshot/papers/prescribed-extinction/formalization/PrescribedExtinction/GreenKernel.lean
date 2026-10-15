import PrescribedExtinction.Maxwell
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp

/-! The actual outgoing scalar kernel, as a locally integrable function and as
a distribution on three-dimensional Euclidean space. The value at the origin
is immaterial for the induced distribution. No fundamental-solution identity,
contact coefficient, radiation identity, or bounded inverse is assumed. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Distributions

/-- `exp(i k |x|)/(4π|x|)`, with the Lean convention `1/0 = 0` at the origin. -/
def outgoingGreen (k : ℝ) (x : Position) : ℂ :=
  Complex.exp (Complex.I * ((k * ‖x‖ : ℝ) : ℂ)) /
    ((4 * Real.pi * ‖x‖ : ℝ) : ℂ)

theorem outgoingGreen_norm (k : ℝ) (x : Position) :
    ‖outgoingGreen k x‖ = (4 * Real.pi * ‖x‖)⁻¹ := by
  simp [outgoingGreen, Complex.norm_exp, abs_of_pos Real.pi_pos]

theorem outgoingGreen_measurable (k : ℝ) : Measurable (outgoingGreen k) := by
  unfold outgoingGreen
  fun_prop

theorem outgoingGreen_locallyIntegrable (k : ℝ) :
    LocallyIntegrable (outgoingGreen k) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi)⁻¹) (α := 1)
    (by norm_num [Position, finrank_euclideanSpace_fin])
    (by norm_num [Position, finrank_euclideanSpace_fin]) ?_
    (outgoingGreen_measurable k).aestronglyMeasurable
  exact ae_of_all _ fun x => by
      rw [outgoingGreen_norm]
      simp [Real.rpow_neg_one, mul_inv_rev, mul_comm]

theorem outgoingGreen_sq_norm_locallyIntegrable (k : ℝ) :
    LocallyIntegrable (fun x : Position => ‖outgoingGreen k x‖ ^ 2) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := ((4 * Real.pi)⁻¹) ^ 2) (α := 2)
    (by norm_num [Position, finrank_euclideanSpace_fin])
    (by norm_num [Position, finrank_euclideanSpace_fin]) ?_ ?_
  · exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _), outgoingGreen_norm]
      simp [mul_inv_rev, mul_pow, mul_comm]
  · exact (outgoingGreen_measurable k).norm.pow_const 2 |>.aestronglyMeasurable

theorem outgoingGreen_memLp_on_compact (k : ℝ) (K : Set Position) (hK : IsCompact K) :
    MemLp (outgoingGreen k) 2 (volume.restrict K) := by
  rw [memLp_two_iff_integrable_sq_norm
    ((outgoingGreen_measurable k).aestronglyMeasurable.restrict)]
  exact (outgoingGreen_sq_norm_locallyIntegrable k).integrableOn_isCompact hK

abbrev ScalarTest := TestFunction (⊤ : TopologicalSpace.Opens Position) ℝ ⊤
abbrev ScalarDistribution := Distribution (⊤ : TopologicalSpace.Opens Position) ℂ ⊤

/-- A genuine continuous distribution, using Mathlib's test-function topology. -/
def outgoingGreenDistribution (k : ℝ) : ScalarDistribution :=
  Distribution.ofFun ⊤ (outgoingGreen k) volume ⊤

theorem outgoingGreenDistribution_apply (k : ℝ) (φ : ScalarTest) :
    outgoingGreenDistribution k φ = ∫ x : Position, φ x • outgoingGreen k x := by
  apply Distribution.ofFun_apply
  exact (outgoingGreen_locallyIntegrable k).locallyIntegrableOn _

def distributionPartial (i : Fin 3) : ScalarDistribution →L[ℝ] ScalarDistribution :=
  Distribution.lineDerivCLM (k := ⊤) (n := ⊤) (basisR i)

def testPartial (i : Fin 3) : ScalarTest →L[ℝ] ScalarTest :=
  TestFunction.lineDerivCLM ℝ (n := ⊤) (k := ⊤) (basisR i)

/-- Full distributional Hessian: derivatives act on test functions, including
singular contributions at the origin. No pointwise differentiation is used. -/
def greenHessian (k : ℝ) (i j : Fin 3) : ScalarDistribution :=
  distributionPartial i (distributionPartial j (outgoingGreenDistribution k))

/-- Full dyadic kernel `(k² I + ∇∇·) g_k`, before convolution and restriction. -/
def dyadicGreenDistribution (k : ℝ) (i j : Fin 3) : ScalarDistribution :=
  (if i = j then (k ^ 2) • outgoingGreenDistribution k else 0) + greenHessian k i j

theorem greenHessian_apply (k : ℝ) (i j : Fin 3) (φ : ScalarTest) :
    greenHessian k i j φ = outgoingGreenDistribution k
      (testPartial j (testPartial i φ)) := by
  simp [greenHessian, distributionPartial, testPartial, Distribution.lineDerivCLM_apply]

theorem dyadicGreenDistribution_apply (k : ℝ) (i j : Fin 3) (φ : ScalarTest) :
    dyadicGreenDistribution k i j φ =
      (if i = j then (k ^ 2) • (∫ x : Position, φ x • outgoingGreen k x) else 0) +
        ∫ x : Position, (testPartial j (testPartial i φ)) x • outgoingGreen k x := by
  classical
  by_cases hij : i = j <;>
    simp [dyadicGreenDistribution, greenHessian_apply, outgoingGreenDistribution_apply, hij]

end OQ7Prescribed
