import OQ7.CellRemainder
import OQ7.ProductRemainder

noncomputable section
namespace OQ7
open Filter Asymptotics
open scoped Topology

theorem norm_one_add_reciprocal_smul_le {A : Type*} [NormedRing A]
    [NormOneClass A] [NormedAlgebra ℝ A] (G : A) (m : ℕ) :
    ‖(1 : A) + (1 / (m : ℝ)) • G‖ ≤ 1 + ‖G‖ / (m : ℝ) := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hb := norm_add_le (1 : A) ((1 / (m : ℝ)) • G)
  simpa only [norm_one, norm_smul, Real.norm_eq_abs, abs_div, abs_one, abs_inv,
    abs_of_nonneg hm, one_div, inv_mul_eq_div] using hb

theorem norm_one_add_reciprocal_smul_add_le {A : Type*} [NormedRing A]
    [NormOneClass A] [NormedAlgebra ℝ A] (G w : A) {Cw : ℝ} (hCw : 0 ≤ Cw)
    {m : ℕ} (hm : 0 < m) (hw : ‖w‖ ≤ Cw / (m : ℝ) ^ 3) :
    ‖(1 : A) + (1 / (m : ℝ)) • G + w‖ ≤ 1 + (‖G‖ + Cw) / (m : ℝ) := by
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpow : (m : ℝ) ≤ (m : ℝ) ^ 3 := le_self_pow₀ hm1 (by decide)
  have hw' : ‖w‖ ≤ Cw / (m : ℝ) := hw.trans
    (div_le_div_of_nonneg_left hCw hmp hpow)
  calc
    ‖(1 : A) + (1 / (m : ℝ)) • G + w‖ ≤
        ‖(1 : A) + (1 / (m : ℝ)) • G‖ + ‖w‖ := norm_add_le _ _
    _ ≤ 1 + ‖G‖ / (m : ℝ) + Cw / (m : ℝ) :=
      add_le_add (norm_one_add_reciprocal_smul_le G m) hw'
    _ = 1 + (‖G‖ + Cw) / (m : ℝ) := by ring

theorem reciprocalCell_insertionError_quartic_bound {A : Type*} [NormedRing A]
    [NormOneClass A] [NormedAlgebra ℝ A] (G : A) (w : ℕ → A)
    {Cw : ℝ} (hCw : 0 < Cw)
    (hw : ∀ᶠ m : ℕ in atTop, ‖w m‖ ≤ Cw / (m : ℝ) ^ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ‖insertionError ((1 : A) + (1 / (m : ℝ)) • G) (w m) m‖ ≤ C / (m : ℝ) ^ 4 := by
  let Cb : ℝ := ‖G‖ + Cw
  have hCb : 0 ≤ Cb := add_nonneg (norm_nonneg G) hCw.le
  refine ⟨Cw ^ 2 * Real.exp Cb / 2, by positivity, ?_⟩
  filter_upwards [hw, eventually_gt_atTop (0 : ℕ)] with m hwm hm
  apply norm_insertionError_quartic _ _ hCb hCw.le hm _ _ hwm
  · apply (norm_one_add_reciprocal_smul_le G m).trans
    simpa only [Cb, add_comm] using add_le_add_left
      (div_le_div_of_nonneg_right (show ‖G‖ ≤ ‖G‖ + Cw from
        le_add_of_nonneg_right hCw.le) (Nat.cast_nonneg m)) 1
  · exact norm_one_add_reciprocal_smul_add_le G (w m) hCw.le hm hwm

#print axioms norm_one_add_reciprocal_smul_le
#print axioms norm_one_add_reciprocal_smul_add_le
#print axioms reciprocalCell_insertionError_quartic_bound
end OQ7
