import OQ7.PhysicalIntegrals
import OQ7.PhysicalGram
import OQ7.GramProperties
import OQ7.PhysicalPassivity

noncomputable section

namespace OQ7

open MeasureTheory Set
open scoped Matrix ComplexOrder

/-- Absorption deposited on a spatial interval by the actual two scattering solutions.
The full-stack equality with the scattering absorption matrix is proved below. -/
def stackDepositedAbsorption (k : ℝ) (layers : List HomogeneousLayer) (a b : ℝ) : Mat2 :=
  (k : ℂ) • weightedGram (volume.restrict (Ioc a b)) (stackLossProfile layers)
    (fun z port => stackScatteringElectric k layers port z)

theorem stackScatteringWeighted_integrable (k a b : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (i j : Fin 2) :
    Integrable (fun z => (stackLossProfile layers z : ℂ) *
      star (stackScatteringElectric k layers i z) * stackScatteringElectric k layers j z)
      (volume.restrict (Ioc a b)) := by
  have hsub : Ioc a b ⊆ uIcc a b := fun z hz =>
    ⟨(min_le_left a b).trans hz.1.le, hz.2.trans (le_max_right a b)⟩
  exact (stackWeightedField_integrableOn k a b hQ h
    (fun r => stackInputMatrix k layers r i) (fun r => stackInputMatrix k layers r j)).mono_set hsub

theorem stackDepositedAbsorption_posSemidef {k P Q : ℝ} (hk : 0 ≤ k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (a b : ℝ) : (stackDepositedAbsorption k layers a b).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · apply weightedGram_posSemidef
    · exact stackScatteringWeighted_integrable k a b hQ h
    · exact ae_of_all _ (fun z => (stackLossProfile_bounds hQ h z).1)
  · exact RCLike.nonneg_iff.mpr ⟨hk, by simp⟩

/-- Maxwell integration identifies the actual physical scattering absorption with its Gram integral. -/
theorem stackAbsorption_eq_deposited {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) :
    absorptionMatrix (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferReflectionRight (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) =
        stackDepositedAbsorption k layers 0 (totalThickness layers) := by
  have hboundary := transfer_absorption_fluxDefect (stackTransfer k layers)
    (stackTransfer_denominator_ne_zero hk h) (stackTransfer_det k h)
  ext i j
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  have hentry := congrArg (fun A : Mat2 => A i j) hboundary
  change 2 * _ = ((stackInputMatrix k layers).conjTranspose *
    fluxDefect (stackTransfer k layers) * stackInputMatrix k layers) i j at hentry
  rw [stackFluxDefect_gram_entry k hQ h] at hentry
  rw [intervalIntegral.integral_of_le (totalThickness_nonneg h)] at hentry
  change 2 * _ = 2 * ((k : ℂ) * weightedGram
    (volume.restrict (Ioc 0 (totalThickness layers))) (stackLossProfile layers)
      (fun z port => stackScatteringElectric k layers port z) i j)
  simpa [stackWeightedField, weightedGram, stackScatteringElectric_as_field, mul_assoc]
    using hentry

/-- The manuscript's physical Gram determinant identity, with the complete stack's transmission. -/
theorem stackPhysicalGramDeterminant {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (a b : ℝ) :
    (stackDepositedAbsorption k layers a b).det /
      (Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) : ℂ) =
        ((4 * k ^ 4 * ∫ p in {p : ℝ × ℝ | p.1 < p.2},
          stackFundamentalPairKernel k layers p
            ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) : ℝ) : ℂ) := by
  have hint := stackScatteringWeighted_integrable k a b hQ h
  have hGram := weightedGram_det_triangleIntegral (volume.restrict (Ioc a b))
    (stackLossProfile layers) (fun z port => stackScatteringElectric k layers port z) hint
  have hkernel := funext (stackScatteringGramPairKernel hk.ne' layers)
  rw [hkernel, integral_const_mul] at hGram
  have ht : Complex.normSq
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) ≠ 0 := by
    intro ht
    exact stack_transmission_ne_zero hk h (Complex.normSq_eq_zero.mp ht)
  have htC : (Complex.normSq
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) : ℂ) ≠ 0 := by
    exact_mod_cast ht
  rw [stackDepositedAbsorption, Matrix.det_smul, hGram]
  simp only [Fintype.card_fin]
  push_cast
  field_simp

theorem stackDepositedAbsorption_interval_entry (k : ℝ) (layers : List HomogeneousLayer)
    {a b : ℝ} (hab : a ≤ b) (i j : Fin 2) :
    stackDepositedAbsorption k layers a b i j = (k : ℂ) *
      ∫ z in a..b, stackWeightedField k layers
        (fun r => stackInputMatrix k layers r i) (fun r => stackInputMatrix k layers r j) z := by
  rw [intervalIntegral.integral_of_le hab]
  rfl

theorem stackDepositedAbsorption_add_adjacent (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    stackDepositedAbsorption k layers a c = stackDepositedAbsorption k layers a b +
      stackDepositedAbsorption k layers b c := by
  ext i j
  rw [Matrix.add_apply, stackDepositedAbsorption_interval_entry k layers (hab.trans hbc),
    stackDepositedAbsorption_interval_entry k layers hab,
    stackDepositedAbsorption_interval_entry k layers hbc,
    ← intervalIntegral.integral_add_adjacent_intervals
      (stackWeightedField_intervalIntegrable k a b hQ h _ _)
      (stackWeightedField_intervalIntegrable k b c hQ h _ _)]
  ring

theorem stackAbsorption_eq_deposited_budget {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    {L : ℝ} (hL : totalThickness layers ≤ L) :
    absorptionMatrix (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferReflectionRight (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) =
        stackDepositedAbsorption k layers 0 L := by
  rw [stackAbsorption_eq_deposited hk hQ h]
  ext i j
  rw [stackDepositedAbsorption_interval_entry k layers (totalThickness_nonneg h),
    stackDepositedAbsorption_interval_entry k layers ((totalThickness_nonneg h).trans hL),
    stackWeightedField_integral_budget k hQ h _ _ hL]

/-- Absorption outside a selected interval is positive semidefinite in the original scattering basis. -/
theorem stackAbsorption_sub_deposited_posSemidef {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    {a b L : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbL : b ≤ L)
    (hL : totalThickness layers ≤ L) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferReflectionRight (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) -
        stackDepositedAbsorption k layers a b).PosSemidef := by
  rw [stackAbsorption_eq_deposited_budget hk hQ h hL,
    stackDepositedAbsorption_add_adjacent k hQ h ha (hab.trans hbL),
    stackDepositedAbsorption_add_adjacent k hQ h hab hbL]
  convert (stackDepositedAbsorption_posSemidef hk.le hQ h 0 a).add
    (stackDepositedAbsorption_posSemidef hk.le hQ h b L) using 1
  abel

theorem stackFundamentalPairKernel_nonneg {k P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (p : ℝ × ℝ) : 0 ≤ stackFundamentalPairKernel k layers p := by
  exact mul_nonneg (mul_nonneg (stackLossProfile_bounds hQ h p.1).1
    (stackLossProfile_bounds hQ h p.2).1) (Complex.normSq_nonneg _)

theorem stackFundamentalPairKernel_integrable {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (a b : ℝ) :
    Integrable (stackFundamentalPairKernel k layers)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
  have ht : Complex.normSq
      (transferTransmissionRight (waveTransfer (stackTransfer k layers))) ≠ 0 := by
    intro ht
    exact stack_transmission_ne_zero hk h (Complex.normSq_eq_zero.mp ht)
  let C := 4 * k ^ 2 * Complex.normSq
    (transferTransmissionRight (waveTransfer (stackTransfer k layers)))
  have hC : C ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hk.ne')) ht
  have hGram := gramPairKernel_integrable (volume.restrict (Ioc a b))
    (stackLossProfile layers) (fun z port => stackScatteringElectric k layers port z)
      (stackScatteringWeighted_integrable k a b hQ h)
  apply (hGram.const_mul C⁻¹).congr
  exact Filter.Eventually.of_forall fun p => by
    change C⁻¹ * gramPairKernel (stackLossProfile layers)
      (fun z port => stackScatteringElectric k layers port z) p = _
    rw [stackScatteringGramPairKernel hk.ne' layers]
    change C⁻¹ * (C * stackFundamentalPairKernel k layers p) = _
    rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]

theorem stackAbsorption_physicalGramDeterminant {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferReflectionRight (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers)))).det /
      (Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) : ℂ) =
        ((4 * k ^ 4 * ∫ p in {p : ℝ × ℝ | p.1 < p.2},
          stackFundamentalPairKernel k layers p
            ∂(volume.restrict (Ioc 0 (totalThickness layers))).prod
              (volume.restrict (Ioc 0 (totalThickness layers))) : ℝ) : ℂ) := by
  rw [stackAbsorption_eq_deposited hk hQ h]
  exact stackPhysicalGramDeterminant hk hQ h 0 (totalThickness layers)

theorem stackAbsorption_physicalGramDeterminant_budget {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    {L : ℝ} (hL : totalThickness layers ≤ L) :
    (absorptionMatrix (transferReflectionLeft (waveTransfer (stackTransfer k layers)))
      (transferReflectionRight (waveTransfer (stackTransfer k layers)))
      (transferTransmissionRight (waveTransfer (stackTransfer k layers)))).det /
      (Complex.normSq (transferTransmissionRight (waveTransfer (stackTransfer k layers))) : ℂ) =
        ((4 * k ^ 4 * ∫ p in {p : ℝ × ℝ | p.1 < p.2},
          stackFundamentalPairKernel k layers p
            ∂(volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioc 0 L)) : ℝ) : ℂ) := by
  rw [stackAbsorption_eq_deposited_budget hk hQ h hL]
  exact stackPhysicalGramDeterminant hk hQ h 0 L

/-- Real determinant form of the exact physical identity, suited to material-resource bounds. -/
theorem stackFluxDefect_physicalGramDeterminant_budget {k P Q : ℝ} (hk : 0 < k)
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    {L : ℝ} (hL : totalThickness layers ≤ L) :
    (fluxDefect (stackTransfer k layers)).det.re =
      4 * k ^ 4 * ∫ p in {p : ℝ × ℝ | p.1 < p.2},
        stackFundamentalPairKernel k layers p
          ∂(volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioc 0 L)) := by
  have hd := stackAbsorption_physicalGramDeterminant_budget hk hQ h hL
  rw [stack_absorption_det_ratio hk h] at hd
  exact congrArg Complex.re hd

#print axioms stackScatteringWeighted_integrable
#print axioms stackDepositedAbsorption_posSemidef
#print axioms stackAbsorption_eq_deposited
#print axioms stackPhysicalGramDeterminant
#print axioms stackDepositedAbsorption_interval_entry
#print axioms stackDepositedAbsorption_add_adjacent
#print axioms stackAbsorption_eq_deposited_budget
#print axioms stackAbsorption_sub_deposited_posSemidef
#print axioms stackFundamentalPairKernel_nonneg
#print axioms stackFundamentalPairKernel_integrable
#print axioms stackAbsorption_physicalGramDeterminant
#print axioms stackAbsorption_physicalGramDeterminant_budget
#print axioms stackFluxDefect_physicalGramDeterminant_budget

end OQ7
