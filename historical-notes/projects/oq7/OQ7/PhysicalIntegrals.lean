import OQ7.PhysicalGlobal
import OQ7.Gram

noncomputable section

namespace OQ7

open Set MeasureTheory
open scoped Matrix

/-- The actual Maxwell electric-field product, weighted by imaginary permittivity. -/
def stackWeightedField (k : ℝ) (layers : List HomogeneousLayer)
    (v w : Fin 2 → ℂ) (z : ℝ) : ℂ :=
  (stackLossProfile layers z : ℂ) * star (stackElectricField k layers v z) *
    stackElectricField k layers w z

theorem stackWeightedField_integrableOn (k a b : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (v w : Fin 2 → ℂ) : IntegrableOn (stackWeightedField k layers v w) (uIcc a b) := by
  have hprod := ((stackElectricField_continuous k h v).star.mul
    (stackElectricField_continuous k h w)).integrableOn_uIcc (a := a) (b := b) (μ := volume)
  have hq : Measurable (fun z => (stackLossProfile layers z : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (stackLossProfile_measurable layers)
  have hbound : ∀ᵐ z ∂volume.restrict (uIcc a b), ‖(stackLossProfile layers z : ℂ)‖ ≤ Q :=
    ae_of_all _ (fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (stackLossProfile_bounds hQ h z).1]
      exact (stackLossProfile_bounds hQ h z).2)
  apply (hprod.bdd_mul hq.aestronglyMeasurable hbound).congr
  exact ae_of_all _ (fun z => by
    change (stackLossProfile layers z : ℂ) *
      (star (stackElectricField k layers v z) * stackElectricField k layers w z) = _
    simp only [stackWeightedField, mul_assoc])

theorem stackWeightedField_intervalIntegrable (k a b : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (v w : Fin 2 → ℂ) : IntervalIntegrable (stackWeightedField k layers v w) volume a b :=
  (stackWeightedField_integrableOn k a b hQ h v w).intervalIntegrable

theorem stackLossProfile_zero_after {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) {z : ℝ} (hz : totalThickness layers ≤ z) :
    stackLossProfile layers z = 0 := by
  induction layers generalizing z with
  | nil => rfl
  | cons layer layers ih =>
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    change layer.width + totalThickness layers ≤ z at hz
    have hzw : layer.width ≤ z := le_trans (le_add_of_nonneg_right (totalThickness_nonneg ht)) hz
    simp only [stackLossProfile, if_neg (not_lt.mpr hzw)]
    exact ih ht (by linarith)

theorem stackLossProfile_integral_budget {P Q : ℝ} {layers : List HomogeneousLayer}
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) {L : ℝ}
    (hL : totalThickness layers ≤ L) :
    ∫ z in 0..L, stackLossProfile layers z = integratedLoss layers := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (stackLossProfile_intervalIntegrable 0 (totalThickness layers) hQ h)
    (stackLossProfile_intervalIntegrable (totalThickness layers) L hQ h)]
  have hzero : (∫ z in totalThickness layers..L, stackLossProfile layers z) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hL
      (g := fun _ => 0) (fun z hz => stackLossProfile_zero_after h (le_of_lt hz.1))]
    simp
  rw [hzero, add_zero, stackLossProfile_integral hQ h]

theorem stackWeightedField_integral_budget (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers)
    (v w : Fin 2 → ℂ) {L : ℝ} (hL : totalThickness layers ≤ L) :
    (∫ z in 0..L, stackWeightedField k layers v w z) =
      ∫ z in 0..totalThickness layers, stackWeightedField k layers v w z := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (stackWeightedField_intervalIntegrable k 0 (totalThickness layers) hQ h v w)
    (stackWeightedField_intervalIntegrable k (totalThickness layers) L hQ h v w)]
  have hzero : (∫ z in totalThickness layers..L, stackWeightedField k layers v w z) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hL
      (g := fun _ => 0) (fun z hz => by
        simp [stackWeightedField, stackLossProfile_zero_after h (le_of_lt hz.1)])]
    simp
  rw [hzero, add_zero]

theorem layerTransfer_fieldState (k : ℝ) (layer : HomogeneousLayer) (v : Fin 2 → ℂ) :
    layerTransfer k layer *ᵥ v =
      ![layerElectricField k layer (v 0) (v 1) layer.width,
        layerMagneticField k layer (v 0) (v 1) layer.width] := by
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  simpa only [hv] using layerField_transfer_boundary k layer (v 0) (v 1)

theorem stackMixedFlux_integral (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) (v w : Fin 2 → ℂ) :
    mixedFlux (v 0) (v 1) (w 0) (w 1) -
      mixedFlux ((stackTransfer k layers *ᵥ v) 0) ((stackTransfer k layers *ᵥ v) 1)
        ((stackTransfer k layers *ᵥ w) 0) ((stackTransfer k layers *ᵥ w) 1) =
      (2 * (k : ℂ)) * ∫ z in 0..totalThickness layers, stackWeightedField k layers v w z := by
  induction layers generalizing v w with
  | nil => simp [stackTransfer, totalThickness]
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    let v' := layerTransfer k layer *ᵥ v
    let w' := layerTransfer k layer *ᵥ w
    have hEv : v' 0 = layerElectricField k layer (v 0) (v 1) layer.width :=
      congrArg (fun u => u 0) (layerTransfer_fieldState k layer v)
    have hHv : v' 1 = layerMagneticField k layer (v 0) (v 1) layer.width :=
      congrArg (fun u => u 1) (layerTransfer_fieldState k layer v)
    have hEw : w' 0 = layerElectricField k layer (w 0) (w 1) layer.width :=
      congrArg (fun u => u 0) (layerTransfer_fieldState k layer w)
    have hHw : w' 1 = layerMagneticField k layer (w 0) (w 1) layer.width :=
      congrArg (fun u => u 1) (layerTransfer_fieldState k layer w)
    have hhead := layerMixedFlux_integral k hl.1 (v 0) (v 1) (w 0) (w 1)
    rw [← hEv, ← hHv, ← hEw, ← hHw] at hhead
    have htail := ih ht v' w'
    have hleft : (∫ z in 0..layer.width, stackWeightedField k (layer :: layers) v w z) =
        (layer.q : ℂ) * ∫ z in 0..layer.width,
          star (layerElectricField k layer (v 0) (v 1) z) *
            layerElectricField k layer (w 0) (w 1) z := by
      rw [intervalIntegral.integral_congr_Ioo_of_le hl.2.2.2.2
        (g := fun z => (layer.q : ℂ) * (star (layerElectricField k layer (v 0) (v 1) z) *
          layerElectricField k layer (w 0) (w 1) z)) (fun z hz => by
            simp [stackWeightedField, stackLossProfile, hz.2,
              stackElectricField_cons, le_of_lt hz.2, mul_assoc])]
      rw [intervalIntegral.integral_const_mul]
    have hright : (∫ z in layer.width..layer.width + totalThickness layers,
        stackWeightedField k (layer :: layers) v w z) =
        ∫ z in 0..totalThickness layers, stackWeightedField k layers v' w' z := by
      rw [intervalIntegral.integral_congr_Ioo_of_le
        (le_add_of_nonneg_right (totalThickness_nonneg ht))
        (g := fun z => stackWeightedField k layers v' w' (z - layer.width))
        (fun z hz => by
          simp [stackWeightedField, stackLossProfile, not_lt.mpr (le_of_lt hz.1),
            stackElectricField_cons, not_le.mpr hz.1, v', w'])]
      rw [intervalIntegral.integral_comp_sub_right]
      simp
    change _ = (2 * (k : ℂ)) * ∫ z in 0..layer.width + totalThickness layers,
      stackWeightedField k (layer :: layers) v w z
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (stackWeightedField_intervalIntegrable k 0 layer.width hQ h v w)
      (stackWeightedField_intervalIntegrable k layer.width
        (layer.width + totalThickness layers) hQ h v w), hleft, hright]
    rw [stackTransfer, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change _ - mixedFlux ((stackTransfer k layers *ᵥ v') 0) ((stackTransfer k layers *ᵥ v') 1)
      ((stackTransfer k layers *ᵥ w') 0) ((stackTransfer k layers *ᵥ w') 1) = _
    linear_combination hhead + htail

theorem stackFluxDefect_gram_entry (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) (B : Mat2) (i j : Fin 2) :
    (B.conjTranspose * fluxDefect (stackTransfer k layers) * B) i j =
      (2 * (k : ℂ)) * ∫ z in 0..totalThickness layers,
        stackWeightedField k layers (fun r => B r i) (fun r => B r j) z := by
  rw [fluxDefect_congruence_entry]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
    stackMixedFlux_integral k hQ h (fun r => B r i) (fun r => B r j)

#print axioms stackWeightedField_integrableOn
#print axioms stackWeightedField_intervalIntegrable
#print axioms stackLossProfile_zero_after
#print axioms stackLossProfile_integral_budget
#print axioms stackWeightedField_integral_budget
#print axioms layerTransfer_fieldState
#print axioms stackMixedFlux_integral
#print axioms stackFluxDefect_gram_entry

end OQ7
