import OQ7.Transfer
import OQ7.PhysicalCoatings
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OQ7

open scoped Matrix Topology ContDiff Matrix.Norms.Elementwise

/-- Two real logarithmic coating parameters acting on all eight real entries of the core. -/
def logCoatedTransfer (F : Mat2) (ℓ : ℝ × ℝ) : Mat2 :=
  !![(Real.exp (ℓ.1 + ℓ.2) : ℂ) * F 0 0,
      (Real.exp (ℓ.2 - ℓ.1) : ℂ) * F 0 1;
      (Real.exp (ℓ.1 - ℓ.2) : ℂ) * F 1 0,
      (Real.exp (-ℓ.1 - ℓ.2) : ℂ) * F 1 1]

/-- The checkpoint's smooth extension of the transmitted power to general complex matrices. -/
def matchingTransmissionPower (F : Mat2) : ℝ :=
  Complex.normSq (transferTransmissionLeft (waveTransfer F))

/-- The reciprocal two-transmission average, agreeing with physical mean absorption
on unimodular matrices while remaining a real rational function off that locus. -/
def matchingMeanAbsorptance (F : Mat2) : ℝ :=
  1 - (Complex.normSq (transferReflectionLeft (waveTransfer F)) +
    Complex.normSq (transferReflectionRight (waveTransfer F)) +
    Complex.normSq (transferTransmissionLeft (waveTransfer F)) +
    Complex.normSq (transferTransmissionRight (waveTransfer F))) / 2

def matchingResponse (F : Mat2) : ℝ × ℝ :=
  (matchingTransmissionPower F, matchingMeanAbsorptance F)

def matchingLogResponse (u : Mat2 × (ℝ × ℝ)) : ℝ × ℝ :=
  matchingResponse (logCoatedTransfer u.1 u.2)

@[fun_prop] theorem matching_complex_re_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.re := Complex.reCLM.contDiff

@[fun_prop] theorem matching_complex_im_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.im := Complex.imCLM.contDiff

@[fun_prop] theorem matching_complex_ofReal_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
@[fun_prop] theorem matching_complex_normSq_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.normSq := by
  change ContDiff ℝ n (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact
    ((matching_complex_re_contDiff n).mul (matching_complex_re_contDiff n)).add
      ((matching_complex_im_contDiff n).mul (matching_complex_im_contDiff n))

@[fun_prop] theorem matching_complex_normSq_contDiffAt (n : WithTop ℕ∞) (z : ℂ) :
    ContDiffAt ℝ n Complex.normSq z := (matching_complex_normSq_contDiff n).contDiffAt
theorem logCoatedTransfer_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun u : Mat2 × (ℝ × ℝ) => logCoatedTransfer u.1 u.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [logCoatedTransfer] <;> fun_prop

theorem logCoatedTransfer_det (F : Mat2) (ℓ : ℝ × ℝ) :
    (logCoatedTransfer F ℓ).det = F.det := by
  have h1 : Real.exp (ℓ.1 + ℓ.2) * Real.exp (-ℓ.1 - ℓ.2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h2 : Real.exp (ℓ.2 - ℓ.1) * Real.exp (ℓ.1 - ℓ.2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [logCoatedTransfer, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = ((Real.exp (ℓ.1 + ℓ.2) * Real.exp (-ℓ.1 - ℓ.2) : ℝ) : ℂ) *
        (F 0 0 * F 1 1) -
      ((Real.exp (ℓ.2 - ℓ.1) * Real.exp (ℓ.1 - ℓ.2) : ℝ) : ℂ) *
        (F 0 1 * F 1 0) := by push_cast; ring
    _ = _ := by rw [h1, h2]; simp

theorem matchingTransmissionPower_physical {F : Mat2} (hF : F.det = 1) :
    matchingTransmissionPower F =
      transmissionPower (transferTransmissionRight (waveTransfer F)) := by
  rw [matchingTransmissionPower, transfer_transmission_reciprocity _
    (by rw [waveTransfer_det, hF])]
  rfl

theorem matchingMeanAbsorptance_physical {F : Mat2} (hF : F.det = 1) :
    matchingMeanAbsorptance F =
      meanAbsorptance (transferReflectionLeft (waveTransfer F))
        (transferReflectionRight (waveTransfer F))
        (transferTransmissionRight (waveTransfer F)) := by
  rw [matchingMeanAbsorptance, transfer_transmission_reciprocity _
    (by rw [waveTransfer_det, hF])]
  unfold meanAbsorptance absorptanceLeft absorptanceRight
  ring

theorem waveTransfer_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n waveTransfer := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [waveTransfer, waveBasis, waveBasisInv, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    fun_prop

theorem matchingResponse_contDiffAt (n : WithTop ℕ∞) (F : Mat2)
    (hd : waveTransfer F 1 1 ≠ 0) : ContDiffAt ℝ n matchingResponse F := by
  have hw : ContDiffAt ℝ n waveTransfer F := (waveTransfer_contDiff n).contDiffAt
  have he (i j : Fin 2) : ContDiffAt ℝ n (fun X : Mat2 => waveTransfer X i j) F :=
    (contDiff_apply_apply ℝ ℂ i j).contDiffAt.comp F hw
  have hdet := ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))
  have hdivide {f : Mat2 → ℂ} (hf : ContDiffAt ℝ n f F) :
      ContDiffAt ℝ n (fun X => f X / waveTransfer X 1 1) F := by
    simpa only [div_eq_mul_inv] using! hf.mul ((he 1 1).inv hd)
  have htL := hdivide hdet
  have htR := hdivide (contDiffAt_const (c := (1 : ℂ)))
  have hrL := hdivide (he 1 0).neg
  have hrR := hdivide (he 0 1)
  have hn (f : Mat2 → ℂ) (hf : ContDiffAt ℝ n f F) :
      ContDiffAt ℝ n (fun X => Complex.normSq (f X)) F :=
    (matching_complex_normSq_contDiff n).contDiffAt.comp F hf
  unfold matchingResponse matchingTransmissionPower matchingMeanAbsorptance
  unfold transferReflectionLeft transferReflectionRight transferTransmissionLeft
    transferTransmissionRight
  simp only [Matrix.det_fin_two]
  exact (hn _ htL).prodMk
    (contDiffAt_const.sub (((hn _ hrL).add (hn _ hrR)).add (hn _ htL) |>.add (hn _ htR)
      |>.div_const 2))
theorem matchingLogResponse_contDiffAt (n : WithTop ℕ∞) (u : Mat2 × (ℝ × ℝ))
    (hd : waveTransfer (logCoatedTransfer u.1 u.2) 1 1 ≠ 0) :
    ContDiffAt ℝ n matchingLogResponse u :=
  (matchingResponse_contDiffAt n _ hd).comp u (logCoatedTransfer_contDiff n).contDiffAt

#print axioms matching_complex_re_contDiff
#print axioms matching_complex_im_contDiff
#print axioms matching_complex_ofReal_contDiff
#print axioms matching_complex_normSq_contDiff
#print axioms matching_complex_normSq_contDiffAt
#print axioms logCoatedTransfer_contDiff
#print axioms logCoatedTransfer_det
#print axioms matchingTransmissionPower_physical
#print axioms matchingMeanAbsorptance_physical
#print axioms waveTransfer_contDiff
#print axioms matchingResponse_contDiffAt
#print axioms matchingLogResponse_contDiffAt

end OQ7








