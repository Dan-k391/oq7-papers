import PrescribedExtinction.NewtonTempered
import PrescribedExtinction.NewtonFundamental

/-! The physical Newton distribution and its verified contact identity agree
with their actual tempered-distribution realizations on the original compact
smooth test functions. This bridge assumes no Fourier identity. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

/-- Complexification of an original real compact smooth test function,
with its genuine Schwartz decay obtained from compact support. -/
def scalarTestSchwartz (φ : ScalarTest) : SchwartzMap Position ℂ :=
  (show HasCompactSupport (Complex.ofRealCLM ∘ (φ : Position → ℝ)) from
    φ.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp φ.contDiff)

theorem scalarTestSchwartz_apply (φ : ScalarTest) (x : Position) :
    scalarTestSchwartz φ x = (φ x : ℂ) := rfl

theorem scalarTestSchwartz_partial (φ : ScalarTest) (i : Fin 3) :
    LineDeriv.lineDerivOp (basisR i) (scalarTestSchwartz φ) =
      scalarTestSchwartz (testPartial i φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply, scalarTestSchwartz_apply]
  change lineDeriv ℝ (Complex.ofRealCLM ∘ (φ : Position → ℝ)) x (basisR i) =
    ((testPartial i φ) x : ℂ)
  have hf := (φ.contDiff.differentiable (by simp)).differentiableAt (x := x)
  have h := ((Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x hf.hasFDerivAt).hasLineDerivAt
    (basisR i)
  have he : (testPartial i φ) x = fderiv ℝ (φ : Position → ℝ) x (basisR i) := by
    rw [testPartial, TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact hf.lineDeriv_eq_fderiv
  rw [he]
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply] using h.lineDeriv

theorem newtonTempered_scalarTest (φ : ScalarTest) :
    newtonTempered (scalarTestSchwartz φ) = outgoingGreenDistribution 0 φ := by
  rw [newtonTempered_apply, outgoingGreenDistribution_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change scalarTestSchwartz φ x * outgoingGreen 0 x = φ x • outgoingGreen 0 x
    rw [scalarTestSchwartz_apply, Complex.real_smul]

/-- The actual tempered Hessian of the physical Newton kernel. -/
def newtonTemperedHessian (i j : Fin 3) : TemperedDistribution Position ℂ :=
  LineDeriv.lineDerivOp (basisR i)
    (LineDeriv.lineDerivOp (basisR j) newtonTempered)

theorem newtonTemperedHessian_apply (φ : SchwartzMap Position ℂ) (i j : Fin 3) :
    newtonTemperedHessian i j φ = newtonTempered
      (LineDeriv.lineDerivOp (basisR j) (LineDeriv.lineDerivOp (basisR i) φ)) := by
  simp only [newtonTemperedHessian, TemperedDistribution.lineDerivOp_apply_apply,
    LineDeriv.lineDerivOp_neg, neg_neg]

theorem newtonTemperedHessian_scalarTest (φ : ScalarTest) (i j : Fin 3) :
    newtonTemperedHessian i j (scalarTestSchwartz φ) = greenHessian 0 i j φ := by
  rw [newtonTemperedHessian_apply, scalarTestSchwartz_partial,
    scalarTestSchwartz_partial, newtonTempered_scalarTest, greenHessian_apply]

theorem newtonTemperedHessian_contact_apply (φ : ScalarTest) (i j : Fin 3) :
    newtonTemperedHessian i j (scalarTestSchwartz φ) =
      ((newtonPVValue φ i j - ((if i = j then 1 else 0) / 3) * φ 0 : ℝ) : ℂ) := by
  rw [newtonTemperedHessian_scalarTest, newton_hessian_contact_apply]

end OQ7Prescribed
