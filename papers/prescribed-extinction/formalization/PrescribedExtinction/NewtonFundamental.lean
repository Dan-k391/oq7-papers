import PrescribedExtinction.NewtonContact

/-! The physical Newton kernel has distributional Laplacian `-δ₀`.
The proof uses the verified Hessian contact identity and cancellation of
the actual compensated principal-value integrands. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem newtonHessianKernel_trace (x : Position) :
    (∑ i : Fin 3, newtonHessianKernel i i x) = 0 := by
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hn ⊢
  simp only [newtonHessianKernel, ite_true, mul_one]
  rw [← add_div, ← add_div]
  have hnum : (3 * x 0 * x 0 - ‖x‖ ^ 2) +
      (3 * x 1 * x 1 - ‖x‖ ^ 2) + (3 * x 2 * x 2 - ‖x‖ ^ 2) = 0 := by
    nlinarith [hn]
  rw [hnum, zero_div]

theorem newtonCompensated_trace (φ : ScalarTest) (x : Position) :
    (∑ i : Fin 3, newtonCompensated φ i i x) = 0 := by
  simp only [newtonCompensated, ← Finset.sum_mul, newtonHessianKernel_trace, zero_mul]

theorem newtonPVValue_trace (φ : ScalarTest) :
    (∑ i : Fin 3, newtonPVValue φ i i) = 0 := by
  unfold newtonPVValue
  rw [← integral_finsetSum Finset.univ (fun i _ => newtonCompensated_integrable φ i i)]
  simp only [newtonCompensated_trace, integral_zero]

/-- The Laplacian of the original smooth compactly supported real test function,
bundled in the original `ScalarTest` space. -/
def testLaplacian : ScalarTest →L[ℝ] ScalarTest :=
  ∑ i : Fin 3, (testPartial i).comp (testPartial i)

theorem testLaplacian_apply (φ : ScalarTest) :
    testLaplacian φ = ∑ i : Fin 3, testPartial i (testPartial i φ) := by
  simp [testLaplacian]

theorem newton_laplacian_test_integral (φ : ScalarTest) :
    (∫ x : Position, newtonReal x * (testLaplacian φ) x) = -φ 0 := by
  have he : (fun x : Position => newtonReal x * (testLaplacian φ) x) =
      (fun x => ∑ i : Fin 3, newtonReal x * (testPartial i (testPartial i φ)) x) := by
    funext x
    simp [testLaplacian_apply, Fin.sum_univ_three, mul_add]
  rw [he, integral_finsetSum Finset.univ
    (fun i _ => newtonReal_test_integrable (testPartial i (testPartial i φ)))]
  simp only [newton_contact_identity_real, ite_true]
  rw [Finset.sum_sub_distrib, newtonPVValue_trace]
  simp

theorem newton_hessian_trace_distribution :
    (∑ i : Fin 3, greenHessian 0 i i) = -newtonDirac := by
  ext φ
  simp only [Fin.sum_univ_three, add_apply, neg_apply,
    newton_hessian_contact_apply, newtonDirac_apply, ite_true]
  have h := newtonPVValue_trace φ
  simp only [Fin.sum_univ_three] at h
  push_cast
  rw [show newtonPVValue φ 0 0 = -newtonPVValue φ 1 1 - newtonPVValue φ 2 2 by linarith [h]]
  push_cast
  ring

end OQ7Prescribed
