import OQ7.ResourcePartition
import OQ7.DeterminantMinkowski
import OQ7.ResourceCells
import OQ7.ResourceCellsOpen
import OQ7.Target
import OQ7.Passivity
import OQ7.PhysicalClass

noncomputable section

namespace OQ7

open Set MeasureTheory
open scoped Matrix ComplexOrder

/-- The paper's invariant, evaluated on the actual finite-layer scattering response. -/
def stackResourceInvariant (k : ℝ) (layers : List HomogeneousLayer) : ℝ :=
  normalizedAbsorptionDet (stackReflectionLeft k layers) (stackReflectionRight k layers)
    (stackTransmission k layers)

theorem stackResourceInvariant_eq_fluxDefect {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    stackResourceInvariant k layers = (fluxDefect (stackTransfer k layers)).det.re := by
  have hc := congrArg Complex.re (stack_absorption_det_ratio hk h)
  simpa only [stackResourceInvariant, normalizedAbsorptionDet, stackReflectionLeft,
    stackReflectionRight, stackTransmission, transmissionPower, Complex.div_ofReal_re] using hc

theorem stackResourceInvariant_nonneg {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    0 ≤ stackResourceInvariant k layers := by
  rw [stackResourceInvariant_eq_fluxDefect hk h]
  exact (Complex.nonneg_iff.mp (stackTransfer_fluxDefect_posSemidef hk.le h).det_nonneg).1

theorem posSemidef_sqrt_det_aggregate_normalized {ι : Type*} (s : Finset ι)
    (A : ι → Mat2) (total : Mat2) {T : ℝ} (hT : 0 ≤ T)
    (hA : ∀ i ∈ s, (A i).PosSemidef)
    (hrest : (total - ∑ i ∈ s, A i).PosSemidef) :
    (∑ i ∈ s, Real.sqrt ((A i).det.re / T)) ≤ Real.sqrt (total.det.re / T) := by
  simp_rw [Real.sqrt_div' _ hT]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (posSemidef_sqrt_det_aggregate s A total hA hrest)
    (Real.sqrt_nonneg T)

theorem physical_selected_sqrt_aggregate {k Pglobal Qglobal a L : ℝ} {n : ℕ}
    (hk : 0 < k) (ha : 0 ≤ a) (hL : 0 ≤ L) (hn : 0 < n)
    {layers : List HomogeneousLayer} (hQglobal : 0 ≤ Qglobal)
    (h : StackAdmissible Pglobal Qglobal layers) :
    (∑ j : Fin n, Real.sqrt ((resourceCellAbsorption k layers a L n j).det.re /
      stackTransmissionPower k layers)) ≤ Real.sqrt (stackResourceInvariant k layers) := by
  let A := absorptionMatrix (stackReflectionLeft k layers) (stackReflectionRight k layers)
    (stackTransmission k layers)
  have hAcell (j : Fin n) (_ : j ∈ Finset.univ) :
      (resourceCellAbsorption k layers a L n j).PosSemidef :=
    stackDepositedAbsorption_posSemidef hk.le hQglobal h _ _
  have hrest : (A - ∑ j : Fin n, resourceCellAbsorption k layers a L n j).PosSemidef := by
    rw [resourceCellAbsorption_sum k a hL hn hQglobal h]
    exact stackAbsorption_sub_deposited_posSemidef hk hQglobal h ha (by linarith)
      (le_max_right (totalThickness layers) (a + L))
      (le_max_left (totalThickness layers) (a + L))
  have hT : 0 ≤ stackTransmissionPower k layers := Complex.normSq_nonneg _
  exact posSemidef_sqrt_det_aggregate_normalized Finset.univ
    (resourceCellAbsorption k layers a L n) A hT hAcell hrest

theorem beta_eq_squared_scalar (k P Q M : ℝ) (n : ℕ) :
    ResourceFloor.beta k P Q M n =
      ((Q / P) * (n : ℝ) * ResourceScalar.g (ResourceFloor.U k P Q M / n)) ^ 2 := by
  rw [mul_pow, mul_pow, ResourceScalar.g_sq, div_pow]
  unfold ResourceFloor.beta
  ring

/-- The physical finite-cell aggregation step; the cell estimates are discharged by Lemma 4.3. -/
theorem physical_resource_floor_of_cellBounds {k P Q M a L Pglobal Qglobal : ℝ} {n : ℕ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (ha : 0 ≤ a) (hL : 0 ≤ L) (hn : 0 < n)
    {layers : List HomogeneousLayer} (hQglobal : 0 ≤ Qglobal)
    (h : StackAdmissible Pglobal Qglobal layers)
    (hcell : ∀ j : Fin n, Q / P * ResourceScalar.g
      (resourceCellU (stackLossProfile layers) a L (k * Real.sqrt P) Q n j) ≤
        Real.sqrt ((resourceCellAbsorption k layers a L n j).det.re / stackTransmissionPower k layers))
    (hscalar : (n : ℝ) * ResourceScalar.g (ResourceFloor.U k P Q M / n) ≤
      ∑ j : Fin n, ResourceScalar.g
        (resourceCellU (stackLossProfile layers) a L (k * Real.sqrt P) Q n j)) :
    ResourceFloor.beta k P Q M n ≤ stackResourceInvariant k layers := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcell j)
  rw [← Finset.mul_sum] at hsum
  have hag := physical_selected_sqrt_aggregate hk ha hL hn hQglobal h
  have hscalar' := mul_le_mul_of_nonneg_left hscalar (div_nonneg hQ.le hP.le)
  have hb : Q / P * (n : ℝ) * ResourceScalar.g (ResourceFloor.U k P Q M / n) ≤
      Real.sqrt (stackResourceInvariant k layers) := by
    simpa only [mul_assoc] using hscalar'.trans (hsum.trans hag)
  have hleft : 0 ≤ Q / P * (n : ℝ) * ResourceScalar.g (ResourceFloor.U k P Q M / n) :=
    mul_nonneg (mul_nonneg (div_nonneg hQ.le hP.le) (Nat.cast_nonneg n))
      (ResourceScalar.g_nonneg _)
  have hsquare := (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mpr hb
  rw [Real.sq_sqrt (stackResourceInvariant_nonneg hk h)] at hsquare
  rw [beta_eq_squared_scalar]
  exact hsquare

/-- Every partition cell uses the actual Maxwell comparison and physical Gram identity. -/
theorem physical_resource_cell_bounds_Ioo {k P Q a L Pglobal Qglobal : ℝ} {n : ℕ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hL : 0 ≤ L) (hn : 0 < n)
    {layers : List HomogeneousLayer} (hQglobal : 0 ≤ Qglobal)
    (h : StackAdmissible Pglobal Qglobal layers)
    (hp : ∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P)
    (hq : ∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hwidth : L / (n : ℝ) ≤ Real.pi / (k * Real.sqrt P)) :
    ∀ j : Fin n, Q / P * ResourceScalar.g
      (resourceCellU (stackLossProfile layers) a L (k * Real.sqrt P) Q n j) ≤
        Real.sqrt ((resourceCellAbsorption k layers a L n j).det.re /
          stackTransmissionPower k layers) := by
  intro j
  have hsub := resourceCell_subset_Ioo a hL hn j
  exact cell_sqrt_det_lower_Ioo hk hP hQ hQglobal h
    (fun z hz => hp z (hsub hz)) (fun z hz => hq z (hsub hz))
    (resourceCellPoint_le_next a hL n j.val)
    (by simpa only [resourceCellPoint_step] using hwidth)

/-- The unconditional half-cell lower bound for the original physical selected interval. -/
theorem physical_resource_half_lower_Ioo {k P Q M a L Pglobal Qglobal : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (ha : 0 ≤ a) (hL : 0 < L)
    {layers : List HomogeneousLayer} (hQglobal : 0 ≤ Qglobal)
    (h : StackAdmissible Pglobal Qglobal layers)
    (hp : ∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P)
    (hq : ∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hmass : (∫ z in a..a + L, stackLossProfile layers z) = M) :
    ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) ≤
      stackResourceInvariant k layers := by
  let n := ResourceFloor.halfCellCount k P L
  have hn : 0 < n := ResourceFloor.cellCount_pos _ _
  have hK : 0 < k * Real.sqrt P := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hw := resourceCellWidth_half (L := L) hk hP
  have hwidth : k * Real.sqrt P * (L / (n : ℝ)) ≤ Real.pi / 2 := by
    have hb := (le_div_iff₀ (show 0 < 2 * k * Real.sqrt P by positivity)).mp hw
    dsimp [n]
    nlinarith
  have hwidthfull : L / (n : ℝ) ≤ Real.pi / (k * Real.sqrt P) := by
    apply (le_div_iff₀ hK).mpr
    nlinarith [Real.pi_pos]
  have hi := fun x y => stackLossProfile_intervalIntegrable x y hQglobal h
  have hu := resourceCellU_bounds_Ioo hL.le hn hK hQ hi hq hwidth
  have hs := resourceCellU_sum (stackLossProfile layers) a L (k * Real.sqrt P) Q hn hi
  rw [hmass] at hs
  have hscalar := ResourceScalar.sum_g_half hn
    (resourceCellU (stackLossProfile layers) a L (k * Real.sqrt P) Q n) hu
  rw [hs] at hscalar
  exact physical_resource_floor_of_cellBounds hk hP hQ ha hL.le hn hQglobal h
    (physical_resource_cell_bounds_Ioo hk hP hQ hL.le hn hQglobal h hp hq hwidthfull) hscalar

/-- The full-cell estimate, using the checkpoint's two valid scalar aggregation cases. -/
theorem physical_resource_full_lower_Ioo {k P Q M a L Pglobal Qglobal : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (ha : 0 ≤ a) (hL : 0 < L)
    {layers : List HomogeneousLayer} (hQglobal : 0 ≤ Qglobal)
    (h : StackAdmissible Pglobal Qglobal layers)
    (hp : ∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P)
    (hq : ∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hmass : (∫ z in a..a + L, stackLossProfile layers z) = M)
    (hcase : ResourceFloor.U k P Q M ≤ Real.pi / 2 ∨
      ResourceFloor.U k P Q M / (ResourceFloor.fullCellCount k P L : ℝ) ≤ 1 / 3) :
    ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) ≤
      stackResourceInvariant k layers := by
  let n := ResourceFloor.fullCellCount k P L
  have hn : 0 < n := ResourceFloor.cellCount_pos _ _
  have hK : 0 < k * Real.sqrt P := mul_pos hk (Real.sqrt_pos.mpr hP)
  have hw := resourceCellWidth_full (L := L) hk hP
  have hwidth : k * Real.sqrt P * (L / (n : ℝ)) ≤ Real.pi := by
    have hb := (le_div_iff₀ hK).mp hw
    simpa only [mul_comm] using hb
  have hi := fun x y => stackLossProfile_intervalIntegrable x y hQglobal h
  have hu := resourceCellU_bounds_Ioo hL.le hn hK hQ hi hq hwidth
  have hs := resourceCellU_sum (stackLossProfile layers) a L (k * Real.sqrt P) Q hn hi
  rw [hmass] at hs
  change (∑ j : Fin n, resourceCellU (stackLossProfile layers) a L (k * Real.sqrt P) Q n j) =
    ResourceFloor.U k P Q M at hs
  have hscalar := ResourceScalar.sum_g_full_cases hn
    (resourceCellU (stackLossProfile layers) a L (k * Real.sqrt P) Q n) hu
    (by rw [hs]; exact ResourceFloor.U_pos hk hP hQ hM)
    (by rw [hs]; exact hcase)
  rw [hs] at hscalar
  exact physical_resource_floor_of_cellBounds hk hP hQ ha hL.le hn hQglobal h
    (physical_resource_cell_bounds_Ioo hk hP hQ hL.le hn hQglobal h hp hq hw) hscalar

theorem physical_resource_half_lower_finitePhysical_Ioo {k P Q M a L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (ha : 0 ≤ a) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : FinitePhysicalStack layers)
    (hp : ∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P)
    (hq : ∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hmass : (∫ z in a..a + L, stackLossProfile layers z) = M) :
    ResourceFloor.beta k P Q M (ResourceFloor.halfCellCount k P L) ≤
      stackResourceInvariant k layers := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  exact physical_resource_half_lower_Ioo hk hP hQ ha hL hQglobal hadm hp hq hmass

theorem physical_resource_full_lower_finitePhysical_Ioo {k P Q M a L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (ha : 0 ≤ a) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : FinitePhysicalStack layers)
    (hp : ∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P)
    (hq : ∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hmass : (∫ z in a..a + L, stackLossProfile layers z) = M)
    (hcase : ResourceFloor.U k P Q M ≤ Real.pi / 2 ∨
      ResourceFloor.U k P Q M / (ResourceFloor.fullCellCount k P L : ℝ) ≤ 1 / 3) :
    ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) ≤
      stackResourceInvariant k layers := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  exact physical_resource_full_lower_Ioo hk hP hQ hM ha hL hQglobal hadm hp hq hmass hcase

/-- The explicit positive finite-budget estimate in Theorem 4.5. -/
theorem physical_resource_explicit_lower_finitePhysical_Ioo {k P Q M a L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (ha : 0 ≤ a) (hL : 0 < L)
    {layers : List HomogeneousLayer} (h : FinitePhysicalStack layers)
    (hp : ∀ z ∈ Ioo a (a + L), stackRealProfile layers z ≤ P)
    (hq : ∀ z ∈ Ioo a (a + L), 0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q)
    (hmass : (∫ z in a..a + L, stackLossProfile layers z) = M) :
    4 * k ^ 4 * M ^ 4 / (3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2) ≤
      stackResourceInvariant k layers := by
  obtain ⟨Pglobal, Qglobal, _, hQglobal, hadm⟩ := finitePhysicalStack_exists_caps h
  have hbudget : M ≤ Q * L := by
    rw [← hmass]
    exact resourceMass_le_cap_Ioo hL.le
      (fun x y => stackLossProfile_intervalIntegrable x y hQglobal hadm) hq
  exact (ResourceFloor.half_floor_explicit hk hP hQ hM hL hbudget).trans
    (physical_resource_half_lower_Ioo hk hP hQ ha hL hQglobal hadm hp hq hmass)

#print axioms physical_resource_cell_bounds_Ioo
#print axioms physical_resource_half_lower_Ioo
#print axioms physical_resource_full_lower_Ioo
#print axioms physical_resource_half_lower_finitePhysical_Ioo
#print axioms physical_resource_full_lower_finitePhysical_Ioo
#print axioms physical_resource_explicit_lower_finitePhysical_Ioo
#print axioms stackResourceInvariant_eq_fluxDefect
#print axioms stackResourceInvariant_nonneg
#print axioms posSemidef_sqrt_det_aggregate_normalized
#print axioms physical_selected_sqrt_aggregate
#print axioms beta_eq_squared_scalar
#print axioms physical_resource_floor_of_cellBounds

end OQ7
