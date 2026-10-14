import OQ7.Layers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace OQ7Prescribed
open scoped Matrix

def plateDesignIndex (j : ℕ) : ℝ := 2 * (j : ℝ) / (2 * (j : ℝ) - 1)
def plateDesignPermittivity (j : ℕ) : ℝ := (plateDesignIndex j) ^ 2
def plateDesignThickness (k : ℝ) (j : ℕ) : ℝ := (2 * (j : ℝ) - 1) * Real.pi / k

theorem plateDesignIndex_gt_one (j : ℕ) (hj : 1 ≤ j) : 1 < plateDesignIndex j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold plateDesignIndex
  apply (one_lt_div (by linarith : 0 < 2 * (j : ℝ) - 1)).mpr
  linarith

theorem plateDesignPermittivity_pos_susceptibility (j : ℕ) (hj : 1 ≤ j) :
    0 < plateDesignPermittivity j - 1 := by
  have hn := plateDesignIndex_gt_one j hj
  unfold plateDesignPermittivity
  nlinarith

theorem plateDesignThickness_pos (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j) :
    0 < plateDesignThickness k j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold plateDesignThickness
  exact div_pos (mul_pos (by linarith) Real.pi_pos) hk

theorem plateDesign_phases (k : ℝ) (hk : k ≠ 0) (j : ℕ) (hj : 1 ≤ j) :
    k * plateDesignThickness k j = (j : ℝ) * (2 * Real.pi) - Real.pi ∧
    k * plateDesignIndex j * plateDesignThickness k j = (j : ℝ) * (2 * Real.pi) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm : 2 * (j : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  unfold plateDesignThickness plateDesignIndex
  constructor <;> field_simp <;> ring

theorem exists_plateDesign_within_cap (P : ℝ) (hP : 1 < P) :
    ∃ j : ℕ, 1 ≤ j ∧ plateDesignPermittivity j ≤ P := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max 1 (3 / (P - 1)))
  have hjr : (1 : ℝ) < j := (le_max_left _ _).trans_lt hj
  have hjn : 1 ≤ j := by exact_mod_cast hjr.le
  have hm : 0 < 2 * (j : ℝ) - 1 := by linarith
  have hm1 : 1 ≤ 2 * (j : ℝ) - 1 := by linarith
  have hbig : 3 / (P - 1) < 2 * (j : ℝ) - 1 := by
    have ht := (le_max_right _ _).trans_lt hj
    linarith
  have hprod : 3 < (P - 1) * (2 * (j : ℝ) - 1) := by
    have hp := (div_lt_iff₀ (sub_pos.mpr hP)).mp hbig
    nlinarith
  let u := 1 / (2 * (j : ℝ) - 1)
  have hu : 0 < u := one_div_pos.mpr hm
  have hu1 : u ≤ 1 := (div_le_one hm).mpr hm1
  have huP : u ≤ (P - 1) / 3 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hn : plateDesignIndex j = 1 + u := by
    unfold plateDesignIndex u
    field_simp
    ring
  refine ⟨j, hjn, ?_⟩
  unfold plateDesignPermittivity
  rw [hn]
  nlinarith

theorem losslessPlateDesign_active_transfer (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j) :
    OQ7.homogeneousTransfer k (plateDesignIndex j : ℂ) (plateDesignThickness k j) = 1 := by
  have hp := (plateDesign_phases k hk.ne' j hj).2
  have hpc : (k : ℂ) * (plateDesignIndex j : ℂ) * (plateDesignThickness k j : ℂ) =
      (j : ℂ) * (2 * (Real.pi : ℂ)) := by exact_mod_cast hp
  have hs : Complex.sin ((j : ℂ) * (2 * (Real.pi : ℂ))) = 0 := by
    simpa using Complex.sin_nat_mul_two_pi_sub 0 j
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [OQ7.homogeneousTransfer, hpc, Complex.cos_nat_mul_two_pi, hs]

theorem losslessPlateDesign_vacuum_transfer (k : ℝ) (hk : 0 < k) (j : ℕ) (hj : 1 ≤ j) :
    OQ7.homogeneousTransfer k 1 (plateDesignThickness k j) = -1 := by
  have hp := (plateDesign_phases k hk.ne' j hj).1
  have hpc : (k : ℂ) * (plateDesignThickness k j : ℂ) =
      (j : ℂ) * (2 * (Real.pi : ℂ)) - (Real.pi : ℂ) := by exact_mod_cast hp
  have hs : Complex.sin ((j : ℂ) * (2 * (Real.pi : ℂ)) - (Real.pi : ℂ)) = 0 := by
    simpa using Complex.sin_nat_mul_two_pi_sub (Real.pi : ℂ) j
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [OQ7.homogeneousTransfer, hpc, Complex.cos_nat_mul_two_pi_sub_pi, hs]

end OQ7Prescribed
