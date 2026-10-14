import OQ7.CoreFactorization
import OQ7.PhysicalExponential
import OQ7.ScalarSign

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7.CoreConstruction
open scoped Matrix Matrix.Norms.Operator

def dimensionlessCell (P Q t : ℝ) : Mat2 :=
  NormedSpace.exp ((-t / 2) • realGenerator P) *
    NormedSpace.exp (t • (realGenerator P + lossGenerator Q)) *
      NormedSpace.exp ((-t / 2) • realGenerator P)

def coreSliceParameter (k Q M : ℝ) (m : ℕ) : ℝ := k * coreSliceWidth Q M m

theorem maxwellGenerator_realP {P : ℝ} (hP : 0 ≤ P) (k : ℝ) :
    maxwellGenerator k (Real.sqrt P : ℂ) = k • realGenerator P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [maxwellGenerator, realGenerator, Complex.real_smul,
      ← Complex.ofReal_pow, Real.sq_sqrt hP]
  all_goals ring

theorem maxwellGenerator_lossyP (k P Q width : ℝ) :
    maxwellGenerator k (refractiveIndex (lossyPLayer P Q width)) =
      k • (realGenerator P + lossGenerator Q) := by
  unfold maxwellGenerator
  rw [refractiveIndex_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realGenerator, lossGenerator, matrixUnit21, Complex.real_smul,
      relativePermittivity, lossyPLayer]
  all_goals (ring_nf <;> simp [Complex.I_sq] <;> ring)

/-- The exponential D is derived from the actual stripped physical cell transfer. -/
theorem strippedCellTransfer_eq_dimensionless {P : ℝ} (hP : 1 ≤ P)
    (k Q M : ℝ) (m : ℕ) :
    strippedCellTransfer k P Q M m = dimensionlessCell P Q (coreSliceParameter k Q M m) := by
  have hP0 : 0 ≤ P := by linarith
  have hn : (Real.sqrt P : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by linarith : 0 < P)).ne'
  have hl : -(coreSliceWidth Q M m) / 2 * k = -(k * coreSliceWidth Q M m) / 2 := by ring
  have hm : coreSliceWidth Q M m * k = k * coreSliceWidth Q M m := by ring
  unfold strippedCellTransfer
  rw [homogeneousTransfer_eq_exp k hn,
    layerTransfer_eq_exp k (layer := lossyPLayer P Q (coreSliceWidth Q M m)) hP,
    maxwellGenerator_realP hP0, maxwellGenerator_lossyP]
  simp only [smul_smul, lossyPLayer, hl, hm, dimensionlessCell, coreSliceParameter]

theorem coreSliceParameter_eq (k Q M : ℝ) (m : ℕ) :
    coreSliceParameter k Q M m = (k * M) / Q / (m : ℝ) := by
  simp only [coreSliceParameter, coreSliceWidth, div_eq_mul_inv]
  ring

/-- The repeated exponential core equals the full actual physical core, up to its scalar sign. -/
theorem physicalUnmatchedCore_transfer_eq_signed_dimensionless {k P : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (Q M : ℝ) (m : ℕ) :
    stackTransfer k (physicalUnmatchedCore k P Q M m) =
      ((-1 : ℂ) ^ (m + 1)) • dimensionlessCell P Q (coreSliceParameter k Q M m) ^ m := by
  rw [physicalUnmatchedCore_transferFactorization hk (by linarith : 0 < P),
    strippedCellTransfer_eq_dimensionless hP]

theorem physicalUnmatchedCore_fluxDefect_eq_dimensionless {k P : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (Q M : ℝ) (m : ℕ) :
    fluxDefect (stackTransfer k (physicalUnmatchedCore k P Q M m)) =
      fluxDefect (dimensionlessCell P Q (coreSliceParameter k Q M m) ^ m) := by
  rw [physicalUnmatchedCore_transfer_eq_signed_dimensionless hk hP,
    signPow_fluxDefect]

#print axioms maxwellGenerator_realP
#print axioms maxwellGenerator_lossyP
#print axioms strippedCellTransfer_eq_dimensionless
#print axioms coreSliceParameter_eq
#print axioms physicalUnmatchedCore_transfer_eq_signed_dimensionless
#print axioms physicalUnmatchedCore_fluxDefect_eq_dimensionless
end OQ7.CoreConstruction
