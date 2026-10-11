import OQ7.CellNormBounds


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OQ7

theorem firstInsertion_add {A : Type*} [Ring A] (a w v : A) (n : ℕ) :
    firstInsertion a (w + v) n = firstInsertion a w n + firstInsertion a v n := by
  induction n with
  | zero => simp [firstInsertion]
  | succ n ih =>
    simp only [firstInsertion, ih]
    noncomm_ring

theorem firstInsertion_sub {A : Type*} [Ring A] (a w v : A) (n : ℕ) :
    firstInsertion a (w - v) n = firstInsertion a w n - firstInsertion a v n := by
  induction n with
  | zero => simp [firstInsertion]
  | succ n ih =>
    simp only [firstInsertion, ih]
    noncomm_ring

theorem norm_firstInsertion_quintic_reciprocal_le {A : Type*} [NormedRing A]
    [NormOneClass A] [NormedAlgebra ℝ A] (G r : A) {Cr : ℝ} (hCr : 0 ≤ Cr)
    {m : ℕ} (hm : 0 < m) (hr : ‖r‖ ≤ Cr / (m : ℝ) ^ 5) :
    ‖firstInsertion ((1 : A) + (1 / (m : ℝ)) • G) r m‖ ≤
      (Cr * Real.exp ‖G‖) / (m : ℝ) ^ 4 := by
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmr : (m : ℝ) ≠ 0 := hmp.ne'
  have hR : 1 ≤ 1 + ‖G‖ / (m : ℝ) := le_add_of_nonneg_right (by positivity)
  calc
    ‖firstInsertion ((1 : A) + (1 / (m : ℝ)) • G) r m‖ ≤
        (m : ℝ) * ‖r‖ * (1 + ‖G‖ / (m : ℝ)) ^ m :=
      norm_firstInsertion_le _ _ hR (norm_one_add_reciprocal_smul_le G m) m
    _ ≤ (m : ℝ) * (Cr / (m : ℝ) ^ 5) * Real.exp ‖G‖ := by
      gcongr
      exact one_add_div_pow_le_exp (norm_nonneg G) hm
    _ = (Cr * Real.exp ‖G‖) / (m : ℝ) ^ 4 := by field_simp

end OQ7


#print axioms OQ7.firstInsertion_add
#print axioms OQ7.firstInsertion_sub
#print axioms OQ7.norm_firstInsertion_quintic_reciprocal_le

