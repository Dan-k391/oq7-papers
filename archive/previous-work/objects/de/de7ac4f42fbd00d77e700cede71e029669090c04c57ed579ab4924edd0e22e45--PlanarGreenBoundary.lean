import work.PlanarLayerFTC
import work.PlanarGreenInterval

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem planarGreen_interval_interior_representation (k a b z : ℝ) (hk : k ≠ 0)
    (haz : a ≤ z) (hzb : z ≤ b) (E H q : ℝ → ℂ)
    (hEc : ContinuousOn E (Icc a b)) (hHc : ContinuousOn H (Icc a b))
    (hqc : ContinuousOn q (Icc a b))
    (hE : ∀ t ∈ Ioo a b, HasDerivAt E (Complex.I * (k : ℂ) * H t) t)
    (hH : ∀ t ∈ Ioo a b, HasDerivAt H (Complex.I * (k : ℂ) * (E t + q t)) t) :
    (k : ℂ) ^ 2 * (∫ t in a..b, planarScalarGreen k (z - t) * q t) =
      E z - (1 / 2 : ℂ) * apertureOscillation k (z - a) * (H a + E a) +
        (1 / 2 : ℂ) * apertureOscillation k (b - z) * (H b - E b) := by
  have hl := planarWaveMoments_boundary k a z haz E H q
    (hEc.mono (Icc_subset_Icc le_rfl hzb)) (hHc.mono (Icc_subset_Icc le_rfl hzb))
    (hqc.mono (Icc_subset_Icc le_rfl hzb))
    (fun t ht => hE t ⟨ht.1, ht.2.trans_le hzb⟩)
    (fun t ht => hH t ⟨ht.1, ht.2.trans_le hzb⟩)
  have hr := planarWaveMoments_boundary k z b hzb E H q
    (hEc.mono (Icc_subset_Icc haz le_rfl)) (hHc.mono (Icc_subset_Icc haz le_rfl))
    (hqc.mono (Icc_subset_Icc haz le_rfl))
    (fun t ht => hE t ⟨haz.trans_lt ht.1, ht.2⟩)
    (fun t ht => hH t ⟨haz.trans_lt ht.1, ht.2⟩)
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have halg (U V : ℂ) :
      (k : ℂ) ^ 2 * (Complex.I / (2 * (k : ℂ)) *
        (apertureOscillation k z * U + apertureOscillation (-k) z * V)) =
      (apertureOscillation k z * (Complex.I * (k : ℂ) * U) +
        apertureOscillation (-k) z * (Complex.I * (k : ℂ) * V)) / 2 := by
    field_simp
  rw [planarGreen_interval_split k a b z haz hzb q hqc, halg, hl.1, hr.2]
  rw [apertureOscillation_sub k z a, apertureOscillation_sub k b z]
  calc
    _ = ((apertureOscillation k z * apertureOscillation (-k) z) * (H z + E z) -
        (apertureOscillation k z * apertureOscillation (-k) a) * (H a + E a) +
        (apertureOscillation (-k) z * apertureOscillation k b) * (H b - E b) -
        (apertureOscillation (-k) z * apertureOscillation k z) * (H z - E z)) / 2 := by ring
    _ = _ := by
      rw [apertureOscillation_opposite_mul,
        mul_comm (apertureOscillation (-k) z) (apertureOscillation k z),
        apertureOscillation_opposite_mul]
      ring

theorem planarGreen_interval_exterior_right_representation (k a b z : ℝ) (hk : k ≠ 0)
    (hab : a ≤ b) (hbz : b ≤ z) (E H q : ℝ → ℂ)
    (hEc : ContinuousOn E (Icc a b)) (hHc : ContinuousOn H (Icc a b))
    (hqc : ContinuousOn q (Icc a b))
    (hE : ∀ t ∈ Ioo a b, HasDerivAt E (Complex.I * (k : ℂ) * H t) t)
    (hH : ∀ t ∈ Ioo a b, HasDerivAt H (Complex.I * (k : ℂ) * (E t + q t)) t) :
    (k : ℂ) ^ 2 * (∫ t in a..b, planarScalarGreen k (z - t) * q t) =
      (1 / 2 : ℂ) * apertureOscillation k (z - b) * (H b + E b) -
        (1 / 2 : ℂ) * apertureOscillation k (z - a) * (H a + E a) := by
  have hm := (planarWaveMoments_boundary k a b hab E H q hEc hHc hqc hE hH).1
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have halg (U : ℂ) : (k : ℂ) ^ 2 *
      (Complex.I / (2 * (k : ℂ)) * apertureOscillation k z * U) =
        (1 / 2 : ℂ) * apertureOscillation k z * (Complex.I * (k : ℂ) * U) := by
    field_simp
  rw [planarGreen_interval_left k a b z hab hbz q, halg, hm,
    apertureOscillation_sub k z b, apertureOscillation_sub k z a]
  ring

theorem planarGreen_interval_exterior_left_representation (k a b z : ℝ) (hk : k ≠ 0)
    (hab : a ≤ b) (hza : z ≤ a) (E H q : ℝ → ℂ)
    (hEc : ContinuousOn E (Icc a b)) (hHc : ContinuousOn H (Icc a b))
    (hqc : ContinuousOn q (Icc a b))
    (hE : ∀ t ∈ Ioo a b, HasDerivAt E (Complex.I * (k : ℂ) * H t) t)
    (hH : ∀ t ∈ Ioo a b, HasDerivAt H (Complex.I * (k : ℂ) * (E t + q t)) t) :
    (k : ℂ) ^ 2 * (∫ t in a..b, planarScalarGreen k (z - t) * q t) =
      (1 / 2 : ℂ) * apertureOscillation k (b - z) * (H b - E b) -
        (1 / 2 : ℂ) * apertureOscillation k (a - z) * (H a - E a) := by
  have hm := (planarWaveMoments_boundary k a b hab E H q hEc hHc hqc hE hH).2
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have halg (U : ℂ) : (k : ℂ) ^ 2 *
      (Complex.I / (2 * (k : ℂ)) * apertureOscillation (-k) z * U) =
        (1 / 2 : ℂ) * apertureOscillation (-k) z * (Complex.I * (k : ℂ) * U) := by
    field_simp
  rw [planarGreen_interval_right k a b z hab hza q, halg, hm,
    apertureOscillation_sub k b z, apertureOscillation_sub k a z]
  ring

end OQ7Prescribed
