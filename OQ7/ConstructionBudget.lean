import OQ7.ResourceAsymptotics

noncomputable section
namespace OQ7
open Filter
open scoped Topology

/-- The integer construction index for every real thickness budget, including fixed coating cost. -/
def constructionIndex (k P C L : ℝ) : ℕ :=
  ⌊Real.sqrt P / Real.pi * (k * L - C)⌋₊

theorem constructionShift_atTop {k : ℝ} (hk : 0 < k) (C : ℝ) :
    Tendsto (fun L : ℝ => k * L - C) atTop atTop := by
  simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-C)
    (Tendsto.const_mul_atTop hk tendsto_id)

theorem constructionIndex_atTop {k P : ℝ} (hk : 0 < k) (hP : 0 < P) (C : ℝ) :
    Tendsto (constructionIndex k P C) atTop atTop := by
  have hA : 0 < Real.sqrt P / Real.pi := by positivity
  exact tendsto_nat_floor_atTop.comp
    (Tendsto.const_mul_atTop hA (constructionShift_atTop hk C))

theorem constructionIndex_ratio {k P : ℝ} (hk : 0 < k) (hP : 0 < P) (C : ℝ) :
    Tendsto (fun L : ℝ => (constructionIndex k P C L : ℝ) / (k * L)) atTop
      (𝓝 (Real.sqrt P / Real.pi)) := by
  have hx := constructionShift_atTop hk C
  have hfloor := (tendsto_nat_floor_mul_div_atTop
    (show 0 ≤ Real.sqrt P / Real.pi by positivity)).comp hx
  have hC : Tendsto (fun L : ℝ => C / (k * L)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hk tendsto_id)
  have hr : Tendsto (fun L : ℝ => (k * L - C) / (k * L)) atTop (𝓝 1) := by
    have ht1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hC
    rw [sub_zero] at ht1
    apply ht1.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    field_simp
  have ht := hfloor.mul hr
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with L hshift hL
  dsimp [constructionIndex]
  field_simp

theorem constructionIndex_fits {k P C L : ℝ} (hP : 0 < P) (hshift : 0 ≤ k * L - C) :
    Real.pi * (constructionIndex k P C L : ℝ) / Real.sqrt P + C ≤ k * L := by
  have hs := Real.sqrt_pos.mpr hP
  have hf := Nat.floor_le (mul_nonneg (div_nonneg hs.le Real.pi_pos.le) hshift)
  have hb := mul_le_mul_of_nonneg_left hf (div_nonneg Real.pi_pos.le hs.le)
  dsimp [constructionIndex]
  have he : Real.pi / Real.sqrt P *
      (Real.sqrt P / Real.pi * (k * L - C)) = k * L - C := by field_simp
  rw [he] at hb
  have heleft : Real.pi / Real.sqrt P * (constructionIndex k P C L : ℝ) =
      Real.pi * (constructionIndex k P C L : ℝ) / Real.sqrt P := by ring
  simp only [constructionIndex] at heleft
  rw [heleft] at hb
  linarith

#print axioms constructionShift_atTop
#print axioms constructionIndex_atTop
#print axioms constructionIndex_ratio
#print axioms constructionIndex_fits
end OQ7
