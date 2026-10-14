import OQ7.CoreAlgebra
import OQ7.PhysicalQuarterWave
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace OQ7.CoreConstruction
open Filter
open scoped Matrix Topology

def realPLayer (P width : ℝ) : HomogeneousLayer := ⟨P, 0, width⟩
def lossyPLayer (P Q width : ℝ) : HomogeneousLayer := ⟨P, Q, width⟩
def coreCellLength (k P : ℝ) : ℝ := Real.pi / (k * Real.sqrt P)
def coreSliceWidth (Q M : ℝ) (m : ℕ) : ℝ := M / Q / (m : ℝ)

/-- The actual centered lossy slice and its two positive real-P spacers. -/
def physicalCoreCell (k P Q M : ℝ) (m : ℕ) : List HomogeneousLayer :=
  let spacer := (coreCellLength k P - coreSliceWidth Q M m) / 2
  [realPLayer P spacer, lossyPLayer P Q (coreSliceWidth Q M m), realPLayer P spacer]

/-- All m physical cells and the two physical real-P end quarter waves. -/
def physicalUnmatchedCore (k P Q M : ℝ) (m : ℕ) : List HomogeneousLayer :=
  [quarterWaveLayer k (Real.sqrt P)] ++
    repeatPhysicalLayers (physicalCoreCell k P Q M m) m ++
      [quarterWaveLayer k (Real.sqrt P)]

def coreQuarterTransfer (k P : ℝ) : Mat2 := layerTransfer k (quarterWaveLayer k (Real.sqrt P))

/-- Algebraically strip the two half-slice real-P propagations; the physical list stays positive. -/
def strippedCellTransfer (k P Q M : ℝ) (m : ℕ) : Mat2 :=
  homogeneousTransfer k (Real.sqrt P : ℂ) (-(coreSliceWidth Q M m) / 2) *
    layerTransfer k (lossyPLayer P Q (coreSliceWidth Q M m)) *
      homogeneousTransfer k (Real.sqrt P : ℂ) (-(coreSliceWidth Q M m) / 2)

theorem realPLayer_refractiveIndex {P : ℝ} (hP : 0 ≤ P) (width : ℝ) :
    refractiveIndex (realPLayer P width) = (Real.sqrt P : ℂ) := by
  unfold refractiveIndex relativePermittivity realPLayer
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast hP)]
  rfl

theorem realPLayer_transfer {P : ℝ} (hP : 0 ≤ P) (k width : ℝ) :
    layerTransfer k (realPLayer P width) = homogeneousTransfer k (Real.sqrt P : ℂ) width := by
  rw [layerTransfer, realPLayer_refractiveIndex hP]
  rfl

theorem coreCellLength_pos {k P : ℝ} (hk : 0 < k) (hP : 0 < P) :
    0 < coreCellLength k P := div_pos Real.pi_pos (mul_pos hk (Real.sqrt_pos.mpr hP))

theorem coreSliceWidth_pos {Q M : ℝ} {m : ℕ} (hQ : 0 < Q) (hM : 0 < M)
    (hm : 0 < m) : 0 < coreSliceWidth Q M m :=
  div_pos (div_pos hM hQ) (by exact_mod_cast hm)

theorem coreSliceWidth_tendsto (Q M : ℝ) :
    Tendsto (coreSliceWidth Q M) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat (M / Q)

theorem coreSliceWidth_eventually_fits {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    ∀ᶠ m : ℕ in atTop,
      0 < m ∧ 0 < coreSliceWidth Q M m ∧ coreSliceWidth Q M m < coreCellLength k P := by
  have hw := (coreSliceWidth_tendsto Q M).eventually
    (eventually_lt_nhds (coreCellLength_pos hk hP))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hw] with m hm hfit
  exact ⟨hm, coreSliceWidth_pos hQ hM hm, hfit⟩

theorem physicalCoreCell_thickness (k P Q M : ℝ) (m : ℕ) :
    totalThickness (physicalCoreCell k P Q M m) = coreCellLength k P := by
  simp [physicalCoreCell, totalThickness, realPLayer, lossyPLayer]
  ring

theorem physicalCoreCell_loss {Q : ℝ} (hQ : Q ≠ 0) (k P M : ℝ) (m : ℕ) :
    integratedLoss (physicalCoreCell k P Q M m) = M / (m : ℝ) := by
  simp [physicalCoreCell, integratedLoss, realPLayer, lossyPLayer, coreSliceWidth]
  field_simp

theorem physicalCoreCell_admissible {k P Q M : ℝ} {m : ℕ}
    (hP : 1 ≤ P) (hQ : 0 ≤ Q) (hM : 0 ≤ coreSliceWidth Q M m)
    (hfit : coreSliceWidth Q M m ≤ coreCellLength k P) :
    StackAdmissible P Q (physicalCoreCell k P Q M m) := by
  have hspacer : 0 ≤ (coreCellLength k P - coreSliceWidth Q M m) / 2 := by linarith
  have hreal : LayerAdmissible P Q
      (realPLayer P ((coreCellLength k P - coreSliceWidth Q M m) / 2)) :=
    ⟨hP, le_rfl, le_rfl, hQ, hspacer⟩
  have hloss : LayerAdmissible P Q (lossyPLayer P Q (coreSliceWidth Q M m)) :=
    ⟨hP, le_rfl, hQ, le_rfl, hM⟩
  intro layer hm
  simp [physicalCoreCell] at hm
  rcases hm with rfl | rfl | rfl
  · exact hreal
  · exact hloss
  · exact hreal

theorem physicalUnmatchedCore_loss {Q : ℝ} {m : ℕ} (hQ : Q ≠ 0) (hm : m ≠ 0)
    (k P M : ℝ) : integratedLoss (physicalUnmatchedCore k P Q M m) = M := by
  have hmc : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  simp only [physicalUnmatchedCore, integratedLoss_append, repeatPhysicalLayers_loss,
    physicalCoreCell_loss hQ]
  simp [quarterWaveLayer, integratedLoss]
  field_simp

theorem physicalUnmatchedCore_thickness (k P Q M : ℝ) (m : ℕ) :
    totalThickness (physicalUnmatchedCore k P Q M m) = ((m : ℝ) + 1) * coreCellLength k P := by
  simp only [physicalUnmatchedCore, totalThickness_append, repeatPhysicalLayers_thickness,
    physicalCoreCell_thickness]
  simp [quarterWaveLayer, totalThickness, coreCellLength]
  field_simp
  ring

theorem physicalUnmatchedCore_admissible {k P Q M : ℝ} {m : ℕ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : 0 ≤ Q) (hM : 0 ≤ coreSliceWidth Q M m)
    (hfit : coreSliceWidth Q M m ≤ coreCellLength k P) :
    StackAdmissible P Q (physicalUnmatchedCore k P Q M m) := by
  have hn : 1 ≤ Real.sqrt P := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hP
  have hend := quarterWaveLayer_admissible hk hn (Real.sq_sqrt (by linarith : 0 ≤ P)).le hQ
  have hbody := repeatPhysicalLayers_admissible (physicalCoreCell_admissible hP hQ hM hfit) m
  intro layer hm
  simp only [physicalUnmatchedCore, List.mem_append, List.mem_singleton] at hm
  rcases hm with (rfl | hbodymem) | rfl
  · exact hend
  · exact hbody layer hbodymem
  · exact hend

theorem physicalUnmatchedCore_eventually_admissible {k P Q M : ℝ}
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hM : 0 < M) :
    ∀ᶠ m : ℕ in atTop, StackAdmissible P Q (physicalUnmatchedCore k P Q M m) ∧
      integratedLoss (physicalUnmatchedCore k P Q M m) = M := by
  filter_upwards [coreSliceWidth_eventually_fits (P := P) hk (by linarith) hQ hM] with m hm
  exact ⟨physicalUnmatchedCore_admissible hk hP.le hQ.le hm.2.1.le hm.2.2.le,
    physicalUnmatchedCore_loss hQ.ne' hm.1.ne' k P M⟩

#print axioms realPLayer_refractiveIndex
#print axioms realPLayer_transfer
#print axioms coreCellLength_pos
#print axioms coreSliceWidth_pos
#print axioms coreSliceWidth_tendsto
#print axioms coreSliceWidth_eventually_fits
#print axioms physicalCoreCell_thickness
#print axioms physicalCoreCell_loss
#print axioms physicalCoreCell_admissible
#print axioms physicalUnmatchedCore_loss
#print axioms physicalUnmatchedCore_thickness
#print axioms physicalUnmatchedCore_admissible
#print axioms physicalUnmatchedCore_eventually_admissible
end OQ7.CoreConstruction
