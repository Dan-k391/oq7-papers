import OQ7.PhysicalCore

noncomputable section
namespace OQ7.CoreConstruction
open scoped Matrix

theorem homogeneousTransfer_mul (k : ℝ) {n : ℂ} (hn : n ≠ 0) (x y : ℝ) :
    homogeneousTransfer k n x * homogeneousTransfer k n y = homogeneousTransfer k n (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homogeneousTransfer, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (field_simp; ring_nf; simp [Complex.I_sq, Complex.cos_add, Complex.sin_add] <;> ring)

theorem coreQuarterTransfer_realFormula (k P : ℝ) :
    coreQuarterTransfer k P =
      homogeneousTransfer k (Real.sqrt P : ℂ) (coreCellLength k P / 2) := by
  rw [coreQuarterTransfer, layerTransfer, refractiveIndex_quarterWave k (Real.sqrt_nonneg P)]
  congr 1
  dsimp [quarterWaveLayer, coreCellLength]
  field_simp

theorem coreQuarterTransfer_sq {k P : ℝ} (hk : 0 < k) (hP : 0 < P) :
    coreQuarterTransfer k P ^ 2 = -(1 : Mat2) := by
  have hn := Real.sqrt_pos.mpr hP
  have hnc : (Real.sqrt P : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [coreQuarterTransfer, layerTransfer_quarterWave hk hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp; ring_nf; simp [Complex.I_sq]

/-- Equation (35) is an exact factorization of the actual three-layer physical cell. -/
theorem physicalCoreCell_transferFactorization {k P Q M : ℝ} (hP : 0 < P) (m : ℕ) :
    stackTransfer k (physicalCoreCell k P Q M m) =
      coreQuarterTransfer k P * strippedCellTransfer k P Q M m * coreQuarterTransfer k P := by
  have hn : (Real.sqrt P : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hP).ne'
  let W := homogeneousTransfer k (Real.sqrt P : ℂ) (-(coreSliceWidth Q M m) / 2)
  let S := homogeneousTransfer k (Real.sqrt P : ℂ)
    ((coreCellLength k P - coreSliceWidth Q M m) / 2)
  have hleft : coreQuarterTransfer k P * W = S := by
    rw [coreQuarterTransfer_realFormula]
    dsimp [W, S]
    rw [homogeneousTransfer_mul k hn]
    congr 1
    ring
  have hright : W * coreQuarterTransfer k P = S := by
    rw [coreQuarterTransfer_realFormula]
    dsimp [W, S]
    rw [homogeneousTransfer_mul k hn]
    congr 1
    ring
  calc
    _ = S * layerTransfer k (lossyPLayer P Q (coreSliceWidth Q M m)) * S := by
      simp only [physicalCoreCell, stackTransfer, one_mul, realPLayer_transfer hP.le]
      simp only [S, mul_assoc]
    _ = (coreQuarterTransfer k P * W) *
        layerTransfer k (lossyPLayer P Q (coreSliceWidth Q M m)) * (W * coreQuarterTransfer k P) := by
      rw [hleft, hright]
    _ = _ := by dsimp [strippedCellTransfer, W]; simp only [mul_assoc]

theorem symmetricConjugation_pow (R D : Mat2) (hR : R ^ 2 = -(1 : Mat2)) (m : ℕ) :
    R * (R * D * R) ^ m * R = ((-1 : ℂ) ^ (m + 1)) • D ^ m := by
  have hRR : R * R = -(1 : Mat2) := by simpa only [pow_two] using hR
  induction m with
  | zero => simpa using hRR
  | succ m ih =>
      calc
        _ = (R * (R * D * R) ^ m * R) * D * (R * R) := by
          rw [pow_succ]
          simp only [mul_assoc]
        _ = -((R * (R * D * R) ^ m * R) * D) := by rw [hRR]; simp
        _ = -((((-1 : ℂ) ^ (m + 1)) • D ^ m) * D) := by rw [ih]
        _ = _ := by simp [pow_succ, neg_smul]

/-- Both real-P end quarter waves strip the repeated physical cells, up to a scalar sign. -/
theorem physicalUnmatchedCore_transferFactorization {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (m : ℕ) :
    stackTransfer k (physicalUnmatchedCore k P Q M m) =
      ((-1 : ℂ) ^ (m + 1)) • strippedCellTransfer k P Q M m ^ m := by
  simp only [physicalUnmatchedCore, stackTransfer_append, repeatPhysicalLayers_transfer,
    stackTransfer, one_mul]
  rw [physicalCoreCell_transferFactorization hP]
  simpa only [coreQuarterTransfer, mul_assoc] using
    symmetricConjugation_pow (coreQuarterTransfer k P) (strippedCellTransfer k P Q M m)
      (coreQuarterTransfer_sq hk hP) m

#print axioms homogeneousTransfer_mul
#print axioms coreQuarterTransfer_realFormula
#print axioms coreQuarterTransfer_sq
#print axioms physicalCoreCell_transferFactorization
#print axioms symmetricConjugation_pow
#print axioms physicalUnmatchedCore_transferFactorization
end OQ7.CoreConstruction
