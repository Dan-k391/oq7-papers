import OQ7.MatchingSheet
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7

open scoped Topology Matrix.Norms.Elementwise

/-- A real two-dimensional Jacobian written as a continuous linear map. -/
def realJacobian2 (a b c d : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (c • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem realJacobian2_apply (a b c d : ℝ) (u : ℝ × ℝ) :
    realJacobian2 a b c d u = (a * u.1 + b * u.2, c * u.1 + d * u.2) := by
  simp [realJacobian2]

theorem realJacobian2_isInvertible {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) :
    (realJacobian2 a b c d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := realJacobian2 (d / (a * d - b * c)) (-b / (a * d - b * c))
      (-c / (a * d - b * c)) (a / (a * d - b * c)))
  · apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;>
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        realJacobian2_apply] <;> ring_nf at hdet ⊢ <;> field_simp [hdet] <;> ring
  · apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;>
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        realJacobian2_apply] <;> ring_nf at hdet ⊢ <;> field_simp [hdet] <;> ring

def sheetVHResponse (z : ℝ × ℝ) : ℝ × ℝ :=
  (4 / (z.1 + z.2) ^ 2, 2 * z.2 * z.1 / (z.1 + z.2) ^ 2)

def sheetVHJacobian (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  realJacobian2 (-8 / (z.1 + z.2) ^ 3) (-8 / (z.1 + z.2) ^ 3)
    (2 * z.2 * (z.2 - z.1) / (z.1 + z.2) ^ 3)
    (2 * z.1 * (z.1 - z.2) / (z.1 + z.2) ^ 3)

theorem inverseSquare_hasDerivAt {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-2 / s ^ 3) s := by
  convert ((hasDerivAt_id s).pow 2).inv (pow_ne_zero 2 hs) using 1
  · ext x
    simp
  · dsimp
    field_simp [hs] <;> ring

theorem sheetVHResponse_hasFDerivAt (z : ℝ × ℝ) (hD : z.1 + z.2 ≠ 0) :
    HasFDerivAt sheetVHResponse (sheetVHJacobian z) z := by
  have hv : HasFDerivAt (fun u : ℝ × ℝ => u.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    hasFDerivAt_fst
  have hh : HasFDerivAt (fun u : ℝ × ℝ => u.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    hasFDerivAt_snd
  have hs := hv.add hh
  have hi := (inverseSquare_hasDerivAt hD).comp_hasFDerivAt z hs
  have hT := hi.const_mul 4
  have ha := ((hh.mul hv).const_mul 2).mul hi
  convert hT.prodMk ha using 1
  · ext u <;> simp [sheetVHResponse, div_eq_mul_inv, mul_assoc]
  · apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;>
      simp [sheetVHJacobian, realJacobian2_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] <;>
      field_simp [hD] <;> ring

theorem sheetVHJacobian_det (z : ℝ × ℝ) (hD : z.1 + z.2 ≠ 0) :
    (-8 / (z.1 + z.2) ^ 3) * (2 * z.1 * (z.1 - z.2) / (z.1 + z.2) ^ 3) -
      (-8 / (z.1 + z.2) ^ 3) * (2 * z.2 * (z.2 - z.1) / (z.1 + z.2) ^ 3) =
      -16 * (z.1 - z.2) / (z.1 + z.2) ^ 5 := by
  field_simp [hD]
  ring

theorem sheetVHJacobian_isInvertible (z : ℝ × ℝ) (hD : z.1 + z.2 ≠ 0)
    (hdiff : z.1 - z.2 ≠ 0) : (sheetVHJacobian z).IsInvertible := by
  unfold sheetVHJacobian
  apply realJacobian2_isInvertible
  rw [sheetVHJacobian_det z hD]
  exact div_ne_zero (mul_ne_zero (by norm_num) hdiff) (pow_ne_zero _ hD)

/-- The limiting sheet coordinates induced by the two physical coating logs. -/
def sheetLogA (ℓ : ℝ × ℝ) : ℝ := Real.exp (ℓ.1 + ℓ.2)

def sheetLogH (g : ℝ) (ℓ : ℝ × ℝ) : ℝ := g * Real.exp (ℓ.1 - ℓ.2)

def sheetLogVH (g : ℝ) (ℓ : ℝ × ℝ) : ℝ × ℝ :=
  (sheetLogA ℓ + (sheetLogA ℓ)⁻¹, sheetLogH g ℓ)

def sheetLogVHJacobian (g : ℝ) (ℓ : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  realJacobian2 ((1 - ((sheetLogA ℓ)^2)⁻¹) * sheetLogA ℓ)
    ((1 - ((sheetLogA ℓ)^2)⁻¹) * sheetLogA ℓ) (sheetLogH g ℓ) (-sheetLogH g ℓ)

theorem sheetLogVH_hasFDerivAt (g : ℝ) (ℓ : ℝ × ℝ) :
    HasFDerivAt (sheetLogVH g) (sheetLogVHJacobian g ℓ) ℓ := by
  have hL : HasFDerivAt (fun u : ℝ × ℝ => u.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) ℓ := hasFDerivAt_fst
  have hR : HasFDerivAt (fun u : ℝ × ℝ => u.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) ℓ := hasFDerivAt_snd
  have hA := (hL.add hR).exp
  have hAne : Real.exp (ℓ.1 + ℓ.2) ≠ 0 := Real.exp_ne_zero _
  have hAi := ((hasDerivAt_id (Real.exp (ℓ.1 + ℓ.2))).inv hAne).comp_hasFDerivAt ℓ hA
  have hH := ((hL.sub hR).exp).const_mul g
  convert (hA.add hAi).prodMk hH using 1
  · ext u <;> simp [sheetLogVH, sheetLogA, sheetLogH]
  · apply ContinuousLinearMap.ext
    intro u
    apply Prod.ext <;>
      simp [sheetLogVHJacobian, realJacobian2_apply, sheetLogA, sheetLogH] <;> ring

theorem sheetLogVHJacobian_isInvertible {g : ℝ} (hg : 0 < g) (ℓ : ℝ × ℝ)
    (hA : sheetLogA ℓ < 1) : (sheetLogVHJacobian g ℓ).IsInvertible := by
  have hApos : 0 < sheetLogA ℓ := Real.exp_pos _
  have hHpos : 0 < sheetLogH g ℓ := mul_pos hg (Real.exp_pos _)
  have hfactor : 1 - ((sheetLogA ℓ)^2)⁻¹ ≠ 0 := by
    intro hz
    field_simp [ne_of_gt hApos] at hz
    nlinarith
  unfold sheetLogVHJacobian
  apply realJacobian2_isInvertible
  have hfactorA := mul_ne_zero hfactor (ne_of_gt hApos)
  have hHne := ne_of_gt hHpos
  convert mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hfactorA) hHne using 1 <;> ring

theorem logCoatedTransfer_sheet (g : ℝ) (ℓ : ℝ × ℝ) :
    logCoatedTransfer (triangularMatchingTransfer 1 g) ℓ =
      triangularMatchingTransfer (sheetLogA ℓ) (sheetLogH g ℓ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [logCoatedTransfer, triangularMatchingTransfer, sheetLogA, sheetLogH,
      Real.exp_neg, neg_add_rev, Complex.ofReal_mul] <;> try ring
  rw [← Complex.exp_neg]
  congr 1
  ring

theorem matchingLogResponse_sheet {g : ℝ} (hg : 0 < g) (ℓ : ℝ × ℝ) :
    matchingLogResponse (triangularMatchingTransfer 1 g, ℓ) =
      sheetVHResponse (sheetLogVH g ℓ) := by
  have hA : 0 < sheetLogA ℓ := Real.exp_pos _
  have hH : 0 < sheetLogH g ℓ := mul_pos hg (Real.exp_pos _)
  unfold matchingLogResponse
  rw [logCoatedTransfer_sheet, triangularMatchingTransfer_response (ne_of_gt hA)
    (show sheetLogA ℓ + sheetLogH g ℓ + (sheetLogA ℓ)⁻¹ ≠ 0 by positivity)]
  simp [sheetVHResponse, sheetLogVH, add_comm, add_left_comm, add_assoc]

def matchingSheetLogJacobian (g : ℝ) (ℓ : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  sheetVHJacobian (sheetLogVH g ℓ) ∘L sheetLogVHJacobian g ℓ

theorem matchingLogResponse_sheet_hasFDerivAt {g : ℝ} (hg : 0 < g) (ℓ : ℝ × ℝ) :
    HasFDerivAt (fun u => matchingLogResponse (triangularMatchingTransfer 1 g, u))
      (matchingSheetLogJacobian g ℓ) ℓ := by
  have hA : 0 < sheetLogA ℓ := Real.exp_pos _
  have hH : 0 < sheetLogH g ℓ := mul_pos hg (Real.exp_pos _)
  have hD : (sheetLogVH g ℓ).1 + (sheetLogVH g ℓ).2 ≠ 0 := by
    dsimp [sheetLogVH]
    positivity
  have hd := (sheetVHResponse_hasFDerivAt (sheetLogVH g ℓ) hD).comp ℓ
    (sheetLogVH_hasFDerivAt g ℓ)
  have he : (fun u => matchingLogResponse (triangularMatchingTransfer 1 g, u)) =
      sheetVHResponse ∘ sheetLogVH g := funext (matchingLogResponse_sheet hg)
  rw [he]
  simpa only [matchingSheetLogJacobian] using! hd

theorem matchingSheetLogJacobian_isInvertible {g : ℝ} (hg : 0 < g) (ℓ : ℝ × ℝ)
    (hA : sheetLogA ℓ < 1) (hdiff : (sheetLogVH g ℓ).1 - (sheetLogVH g ℓ).2 ≠ 0) :
    (matchingSheetLogJacobian g ℓ).IsInvertible := by
  have hApos : 0 < sheetLogA ℓ := Real.exp_pos _
  have hHpos : 0 < sheetLogH g ℓ := mul_pos hg (Real.exp_pos _)
  have hD : (sheetLogVH g ℓ).1 + (sheetLogVH g ℓ).2 ≠ 0 := by
    dsimp [sheetLogVH]
    positivity
  exact (sheetVHJacobian_isInvertible _ hD hdiff).comp
    (sheetLogVHJacobian_isInvertible hg ℓ hA)

#print axioms realJacobian2_apply
#print axioms realJacobian2_isInvertible
#print axioms inverseSquare_hasDerivAt
#print axioms sheetVHResponse_hasFDerivAt
#print axioms sheetVHJacobian_det
#print axioms sheetVHJacobian_isInvertible
#print axioms sheetLogVH_hasFDerivAt
#print axioms sheetLogVHJacobian_isInvertible
#print axioms logCoatedTransfer_sheet
#print axioms matchingLogResponse_sheet
#print axioms matchingLogResponse_sheet_hasFDerivAt
#print axioms matchingSheetLogJacobian_isInvertible

end OQ7
