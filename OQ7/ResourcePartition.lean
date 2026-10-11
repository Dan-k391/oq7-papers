import OQ7.PhysicalIntegrals
import OQ7.ResourceAsymptotics
import OQ7.PhysicalAbsorption

noncomputable section

namespace OQ7

open Set MeasureTheory

/-- Equal cells of the selected interval, including cells whose endpoints lie inside layers. -/
def resourceCellPoint (a L : ℝ) (n j : ℕ) : ℝ := a + (j : ℝ) * L / (n : ℝ)

def resourceCellMass (q : ℝ → ℝ) (a L : ℝ) (n : ℕ) (j : Fin n) : ℝ :=
  ∫ z in resourceCellPoint a L n j.val..resourceCellPoint a L n (j.val + 1), q z

def resourceCellU (q : ℝ → ℝ) (a L K Q : ℝ) (n : ℕ) (j : Fin n) : ℝ :=
  K * resourceCellMass q a L n j / Q

def resourceCellAbsorption (k : ℝ) (layers : List HomogeneousLayer)
    (a L : ℝ) (n : ℕ) (j : Fin n) : Mat2 :=
  stackDepositedAbsorption k layers (resourceCellPoint a L n j.val)
    (resourceCellPoint a L n (j.val + 1))

theorem resourceCellPoint_zero (a L : ℝ) (n : ℕ) : resourceCellPoint a L n 0 = a := by
  simp [resourceCellPoint]

theorem resourceCellPoint_end (a L : ℝ) {n : ℕ} (hn : 0 < n) :
    resourceCellPoint a L n n = a + L := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [resourceCellPoint, mul_div_cancel_left₀ L hn0]

theorem resourceCellPoint_step (a L : ℝ) (n j : ℕ) :
    resourceCellPoint a L n (j + 1) - resourceCellPoint a L n j = L / n := by
  simp only [resourceCellPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem resourceCellPoint_mem (a : ℝ) {L : ℝ} (hL : 0 ≤ L) {n j : ℕ}
    (hn : 0 < n) (hj : j ≤ n) : resourceCellPoint a L n j ∈ Icc a (a + L) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hp := div_nonneg (mul_nonneg (Nat.cast_nonneg j) hL) hn'.le
  have hu : (j : ℝ) * L / n ≤ L := (div_le_iff₀ hn').mpr (by nlinarith)
  unfold resourceCellPoint
  constructor <;> linarith

theorem resourceCellPoint_le_next (a : ℝ) {L : ℝ} (hL : 0 ≤ L) (n j : ℕ) :
    resourceCellPoint a L n j ≤ resourceCellPoint a L n (j + 1) := by
  have hstep := resourceCellPoint_step a L n j
  have hdiv : 0 ≤ L / (n : ℝ) := div_nonneg hL (Nat.cast_nonneg _)
  linarith

theorem resourceCell_subset (a : ℝ) {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (j : Fin n) : Icc (resourceCellPoint a L n j.val) (resourceCellPoint a L n (j.val + 1))
      ⊆ Icc a (a + L) := by
  have hleft := resourceCellPoint_mem a hL hn (Nat.le_of_lt j.isLt)
  have hright := resourceCellPoint_mem a hL hn j.isLt
  exact Icc_subset_Icc hleft.1 hright.2

theorem resourceCellMass_sum (q : ℝ → ℝ) (a L : ℝ) {n : ℕ} (hn : 0 < n)
    (hint : ∀ x y, IntervalIntegrable q volume x y) :
    (∑ j : Fin n, resourceCellMass q a L n j) = ∫ z in a..a + L, q z := by
  simp only [resourceCellMass]
  have hsum := Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ∫ z in resourceCellPoint a L n j..resourceCellPoint a L n (j + 1), q z) n
  rw [hsum]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => hint (resourceCellPoint a L n j) (resourceCellPoint a L n (j + 1)))]
  rw [resourceCellPoint_zero, resourceCellPoint_end a L hn]

theorem resourceCellMass_bounds {q : ℝ → ℝ} {a L Q : ℝ} {n : ℕ}
    (hL : 0 ≤ L) (hn : 0 < n) (hint : ∀ x y, IntervalIntegrable q volume x y)
    (hcap : ∀ z ∈ Icc a (a + L), 0 ≤ q z ∧ q z ≤ Q) (j : Fin n) :
    0 ≤ resourceCellMass q a L n j ∧ resourceCellMass q a L n j ≤ Q * (L / n) := by
  have hab := resourceCellPoint_le_next a hL n j.val
  have hsub := resourceCell_subset a hL hn j
  constructor
  · exact intervalIntegral.integral_nonneg hab (fun z hz => (hcap z (hsub hz)).1)
  · have hc : IntervalIntegrable (fun _ : ℝ => Q) volume
        (resourceCellPoint a L n j.val) (resourceCellPoint a L n (j.val + 1)) :=
      continuous_const.intervalIntegrable _ _
    have hu := intervalIntegral.integral_mono_on hab (hint _ _) hc
      (fun z hz => (hcap z (hsub hz)).2)
    rw [intervalIntegral.integral_const] at hu
    simpa only [resourceCellMass, smul_eq_mul, resourceCellPoint_step, mul_comm] using hu

theorem resourceCellWidth_of_countLower {L a : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n) (hcount : a * L ≤ n) : L / n ≤ 1 / a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_div_iff₀ hn' ha).mpr (by simpa only [mul_comm, one_mul, mul_one] using hcount)

theorem resourceCellWidth_full {k P L : ℝ} (hk : 0 < k) (hP : 0 < P) :
    L / (ResourceFloor.fullCellCount k P L : ℝ) ≤ Real.pi / (k * Real.sqrt P) := by
  have ha : 0 < k * Real.sqrt P / Real.pi := by positivity
  have hb := resourceCellWidth_of_countLower ha
    (ResourceFloor.cellCount_pos (k * Real.sqrt P / Real.pi) L)
    (ResourceFloor.cellCount_lower (k * Real.sqrt P / Real.pi) L)
  simpa only [one_div, inv_div, ResourceFloor.fullCellCount] using hb

theorem resourceCellWidth_half {k P L : ℝ} (hk : 0 < k) (hP : 0 < P) :
    L / (ResourceFloor.halfCellCount k P L : ℝ) ≤ Real.pi / (2 * k * Real.sqrt P) := by
  have ha : 0 < 2 * k * Real.sqrt P / Real.pi := by positivity
  have hb := resourceCellWidth_of_countLower ha
    (ResourceFloor.cellCount_pos (2 * k * Real.sqrt P / Real.pi) L)
    (ResourceFloor.cellCount_lower (2 * k * Real.sqrt P / Real.pi) L)
  simpa only [one_div, inv_div, ResourceFloor.halfCellCount] using hb

theorem resourceCellU_bounds {q : ℝ → ℝ} {a L K Q B : ℝ} {n : ℕ}
    (hL : 0 ≤ L) (hn : 0 < n) (hK : 0 < K) (hQ : 0 < Q)
    (hint : ∀ x y, IntervalIntegrable q volume x y)
    (hcap : ∀ z ∈ Icc a (a + L), 0 ≤ q z ∧ q z ≤ Q)
    (hwidth : K * (L / n) ≤ B) (j : Fin n) : resourceCellU q a L K Q n j ∈ Icc 0 B := by
  have hm := resourceCellMass_bounds hL hn hint hcap j
  constructor
  · exact div_nonneg (mul_nonneg hK.le hm.1) hQ.le
  · calc
      resourceCellU q a L K Q n j ≤ K * (Q * (L / n)) / Q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm.2 hK.le) hQ.le
      _ = K * (L / n) := by field_simp
      _ ≤ B := hwidth

theorem resourceCellU_sum (q : ℝ → ℝ) (a L K Q : ℝ) {n : ℕ} (hn : 0 < n)
    (hint : ∀ x y, IntervalIntegrable q volume x y) :
    (∑ j : Fin n, resourceCellU q a L K Q n j) = K * (∫ z in a..a + L, q z) / Q := by
  simp only [resourceCellU, ← Finset.sum_div, ← Finset.mul_sum]
  rw [resourceCellMass_sum q a L hn hint]

theorem resourceCellAbsorption_sum (k a : ℝ) {L P Q : ℝ} {n : ℕ}
    {layers : List HomogeneousLayer} (hL : 0 ≤ L) (hn : 0 < n)
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) :
    (∑ j : Fin n, resourceCellAbsorption k layers a L n j) =
      stackDepositedAbsorption k layers a (a + L) := by
  ext i j
  simp only [Matrix.sum_apply]
  have heq (r : Fin n) : resourceCellAbsorption k layers a L n r i j =
      (k : ℂ) * ∫ z in resourceCellPoint a L n r.val..resourceCellPoint a L n (r.val + 1),
        stackWeightedField k layers (fun x => stackInputMatrix k layers x i)
          (fun x => stackInputMatrix k layers x j) z :=
    stackDepositedAbsorption_interval_entry k layers (resourceCellPoint_le_next a hL n r.val) i j
  simp_rw [heq]
  rw [← Finset.mul_sum, stackDepositedAbsorption_interval_entry k layers (by linarith : a ≤ a + L)]
  congr 1
  have hsum := Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    ∫ z in resourceCellPoint a L n r..resourceCellPoint a L n (r + 1),
      stackWeightedField k layers (fun x => stackInputMatrix k layers x i)
        (fun x => stackInputMatrix k layers x j) z) n
  rw [hsum, intervalIntegral.sum_integral_adjacent_intervals
    (fun r hr => stackWeightedField_intervalIntegrable k _ _ hQ h _ _)]
  rw [resourceCellPoint_zero, resourceCellPoint_end a L hn]

theorem resourceCell_subset_Ioo (a : ℝ) {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (j : Fin n) : Ioo (resourceCellPoint a L n j.val) (resourceCellPoint a L n (j.val + 1))
      ⊆ Ioo a (a + L) := by
  have hleft := resourceCellPoint_mem a hL hn (Nat.le_of_lt j.isLt)
  have hright := resourceCellPoint_mem a hL hn j.isLt
  intro z hz
  exact ⟨hleft.1.trans_lt hz.1, hz.2.trans_le hright.2⟩

/-- Open-interval material caps suffice; interface endpoint values do not affect the mass. -/
theorem resourceCellMass_bounds_Ioo {q : ℝ → ℝ} {a L Q : ℝ} {n : ℕ}
    (hL : 0 ≤ L) (hn : 0 < n) (hint : ∀ x y, IntervalIntegrable q volume x y)
    (hcap : ∀ z ∈ Ioo a (a + L), 0 ≤ q z ∧ q z ≤ Q) (j : Fin n) :
    0 ≤ resourceCellMass q a L n j ∧ resourceCellMass q a L n j ≤ Q * (L / n) := by
  have hab := resourceCellPoint_le_next a hL n j.val
  have hsub := resourceCell_subset_Ioo a hL hn j
  have hc (C : ℝ) : IntervalIntegrable (fun _ : ℝ => C) volume
      (resourceCellPoint a L n j.val) (resourceCellPoint a L n (j.val + 1)) :=
    continuous_const.intervalIntegrable _ _
  constructor
  · have hb := intervalIntegral.integral_mono_on_of_le_Ioo hab (hc 0) (hint _ _)
      (fun z hz => (hcap z (hsub hz)).1)
    simpa only [intervalIntegral.integral_zero, resourceCellMass] using hb
  · have hu := intervalIntegral.integral_mono_on_of_le_Ioo hab (hint _ _) (hc Q)
      (fun z hz => (hcap z (hsub hz)).2)
    rw [intervalIntegral.integral_const] at hu
    simpa only [resourceCellMass, smul_eq_mul, resourceCellPoint_step, mul_comm] using hu

theorem resourceCellU_bounds_Ioo {q : ℝ → ℝ} {a L K Q B : ℝ} {n : ℕ}
    (hL : 0 ≤ L) (hn : 0 < n) (hK : 0 < K) (hQ : 0 < Q)
    (hint : ∀ x y, IntervalIntegrable q volume x y)
    (hcap : ∀ z ∈ Ioo a (a + L), 0 ≤ q z ∧ q z ≤ Q)
    (hwidth : K * (L / n) ≤ B) (j : Fin n) : resourceCellU q a L K Q n j ∈ Icc 0 B := by
  have hm := resourceCellMass_bounds_Ioo hL hn hint hcap j
  constructor
  · exact div_nonneg (mul_nonneg hK.le hm.1) hQ.le
  · calc
      resourceCellU q a L K Q n j ≤ K * (Q * (L / n)) / Q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm.2 hK.le) hQ.le
      _ = K * (L / n) := by field_simp
      _ ≤ B := hwidth

theorem resourceMass_le_cap_Ioo {q : ℝ → ℝ} {a L Q : ℝ} (hL : 0 ≤ L)
    (hint : ∀ x y, IntervalIntegrable q volume x y)
    (hcap : ∀ z ∈ Ioo a (a + L), 0 ≤ q z ∧ q z ≤ Q) :
    (∫ z in a..a + L, q z) ≤ Q * L := by
  have hb := (resourceCellMass_bounds_Ioo hL (by decide : 0 < 1) hint hcap (0 : Fin 1)).2
  simpa [resourceCellMass, resourceCellPoint] using hb

#print axioms resourceCellPoint_zero
#print axioms resourceCellPoint_end
#print axioms resourceCellPoint_step
#print axioms resourceCellPoint_mem
#print axioms resourceCellPoint_le_next
#print axioms resourceCell_subset
#print axioms resourceCellMass_sum
#print axioms resourceCellMass_bounds
#print axioms resourceCellWidth_of_countLower
#print axioms resourceCellWidth_full
#print axioms resourceCellWidth_half
#print axioms resourceCellU_bounds
#print axioms resourceCellU_sum
#print axioms resourceCellAbsorption_sum
#print axioms resourceCell_subset_Ioo
#print axioms resourceCellMass_bounds_Ioo
#print axioms resourceCellU_bounds_Ioo
#print axioms resourceMass_le_cap_Ioo

end OQ7
