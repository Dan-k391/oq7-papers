import PrescribedExtinction.GreenGradient
import PrescribedExtinction.PolePointIBP

/-! The first outgoing Green derivative across the actual inverse-distance
pole. Its distributional derivative has no additional contact term. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem outgoingGreen_contDiffAt (k : ℝ) (x : Position) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (outgoingGreen k) x := by
  rw [show outgoingGreen k = fun y : Position => outgoingRadial k ‖y‖ from
    funext (outgoingGreen_eq_radial k)]
  exact (outgoingRadial_contDiffAt k ‖x‖ (norm_ne_zero_iff.mpr hx)).comp x
    (contDiffAt_norm ℝ hx)

theorem outgoingGreen_first_test_ibp (k : ℝ) (j : Fin 3) (φ : ScalarTest) :
    (∫ x : Position, (testPartial j φ) x • outgoingGreen k x) =
      -(∫ x : Position, φ x • outgoingGradient k j x) := by
  apply pole_point_complex_test_ibp (outgoingGreen k) (outgoingGradient k j) j
    (outgoingGreen_contDiffAt k) (outgoingGradient_hasLineDerivAt k j)
    (outgoingGreen_locallyIntegrable k) (outgoingGradient_locallyIntegrable k j)
  refine ⟨1, by norm_num, (4 * Real.pi)⁻¹, by positivity, fun x _ => ?_⟩
  rw [outgoingGreen_norm]
  simp only [mul_inv_rev, div_eq_mul_inv, mul_comm]
  exact le_rfl

/-- Exact first distributional derivative of the physical outgoing kernel.
The shrinking puncture argument proves the absence of a first-order Dirac
term rather than discarding the origin. -/
theorem outgoingGreen_first_distribution (k : ℝ) (j : Fin 3) :
    distributionPartial j (outgoingGreenDistribution k) =
      Distribution.ofFun ⊤ (outgoingGradient k j) volume ⊤ := by
  ext φ
  simp only [distributionPartial, Distribution.lineDerivCLM_apply]
  rw [Distribution.ofFun_apply ((outgoingGradient_locallyIntegrable k j).locallyIntegrableOn ⊤)]
  rw [outgoingGreenDistribution_apply]
  change -(∫ x : Position, (testPartial j φ) x • outgoingGreen k x) = _
  rw [outgoingGreen_first_test_ibp, neg_neg]

end OQ7Prescribed
