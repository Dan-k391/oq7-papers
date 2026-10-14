import OQ7.Fields
import OQ7.Transfer
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

namespace OQ7

open scoped Topology Matrix
open Set Filter
open MeasureTheory

/-- Actual state propagation from the left boundary to a spatial point.
The empty tail continues into the exterior vacuum. -/
def partialTransfer (k : ℝ) : List HomogeneousLayer → ℝ → Mat2
  | [], z => homogeneousTransfer k 1 z
  | layer :: layers, z => if z ≤ layer.width then
      homogeneousTransfer k (refractiveIndex layer) z
    else partialTransfer k layers (z - layer.width) * layerTransfer k layer

/-- Imaginary permittivity along the actual finite stack, with exterior vacuum. -/
def stackLossProfile : List HomogeneousLayer → ℝ → ℝ
  | [], _ => 0
  | layer :: layers, z => if z < layer.width then layer.q
      else stackLossProfile layers (z - layer.width)

/-- Real permittivity along the actual finite stack, with exterior vacuum. -/
def stackRealProfile : List HomogeneousLayer → ℝ → ℝ
  | [], _ => 1
  | layer :: layers, z => if z < layer.width then layer.p
      else stackRealProfile layers (z - layer.width)

def interfacePositions : List HomogeneousLayer → List ℝ
  | [] => []
  | layer :: layers => layer.width :: (interfacePositions layers).map (layer.width + ·)

def partialState (k : ℝ) (layers : List HomogeneousLayer) (v : Fin 2 → ℂ) (z : ℝ) :=
  partialTransfer k layers z *ᵥ v

def stackElectricField (k : ℝ) (layers : List HomogeneousLayer) (v : Fin 2 → ℂ) (z : ℝ) : ℂ :=
  partialState k layers v z 0

def stackMagneticField (k : ℝ) (layers : List HomogeneousLayer) (v : Fin 2 → ℂ) (z : ℝ) : ℂ :=
  partialState k layers v z 1

theorem homogeneousTransfer_zero (k : ℝ) (n : ℂ) :
    homogeneousTransfer k n 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [homogeneousTransfer]

theorem partialTransfer_zero (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) : partialTransfer k layers 0 = 1 := by
  cases layers with
  | nil => exact homogeneousTransfer_zero k 1
  | cons layer layers =>
    have hw := (h layer (by simp)).2.2.2.2
    simp [partialTransfer, hw, homogeneousTransfer_zero]

theorem partialTransfer_total (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) :
    partialTransfer k layers (totalThickness layers) = stackTransfer k layers := by
  induction layers with
  | nil => simp [partialTransfer, totalThickness, stackTransfer, homogeneousTransfer_zero]
  | cons layer layers ih =>
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    have htn := totalThickness_nonneg ht
    change partialTransfer k (layer :: layers) (layer.width + totalThickness layers) = _
    by_cases hz : totalThickness layers = 0
    · have hb : partialTransfer k layers (totalThickness layers) = 1 := by
        rw [hz]; exact partialTransfer_zero k ht
      have hs : stackTransfer k layers = 1 := (ih ht).symm.trans hb
      simp [partialTransfer, stackTransfer, hz, hs, layerTransfer]
    · have hg : layer.width < layer.width + totalThickness layers :=
        lt_add_of_pos_right layer.width (lt_of_le_of_ne htn (Ne.symm hz))
      simp only [partialTransfer, not_le.mpr hg, ↓reduceIte, add_sub_cancel_left,
        stackTransfer]
      rw [ih ht]

theorem partialTransfer_det (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (z : ℝ) : (partialTransfer k layers z).det = 1 := by
  induction layers generalizing z with
  | nil => exact homogeneousTransfer_det k one_ne_zero z
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    simp only [partialTransfer]
    split_ifs
    · exact homogeneousTransfer_det k (refractiveIndex_ne_zero hl.1) z
    · rw [Matrix.det_mul, ih ht, layerTransfer_det k hl, one_mul]

theorem stackLossProfile_bounds {P Q : ℝ} {layers : List HomogeneousLayer}
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) (z : ℝ) :
    0 ≤ stackLossProfile layers z ∧ stackLossProfile layers z ≤ Q := by
  induction layers generalizing z with
  | nil => simpa [stackLossProfile] using hQ
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    simp only [stackLossProfile]
    split_ifs
    · exact ⟨hl.2.2.1, hl.2.2.2.1⟩
    · exact ih ht _

theorem stackRealProfile_bounds {P Q : ℝ} {layers : List HomogeneousLayer}
    (hP : 1 ≤ P) (h : StackAdmissible P Q layers) (z : ℝ) :
    1 ≤ stackRealProfile layers z ∧ stackRealProfile layers z ≤ P := by
  induction layers generalizing z with
  | nil => simpa [stackRealProfile] using hP
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    simp only [stackRealProfile]
    split_ifs
    · exact ⟨hl.1, hl.2.1⟩
    · exact ih ht _

theorem homogeneousTransfer_continuous (k : ℝ) (n : ℂ) :
    Continuous (homogeneousTransfer k n) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;>
    simp only [homogeneousTransfer, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals fun_prop

theorem partialTransfer_continuous (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) : Continuous (partialTransfer k layers) := by
  induction layers with
  | nil => exact homogeneousTransfer_continuous k 1
  | cons layer layers ih =>
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    apply Continuous.if
    · intro z hz
      have hz' : z = layer.width := by
        change z ∈ frontier (Iic layer.width) at hz
        simpa only [frontier_Iic, mem_singleton_iff] using hz
      subst z
      simp [partialTransfer_zero k ht, layerTransfer]
    · exact homogeneousTransfer_continuous k (refractiveIndex layer)
    · apply continuous_pi; intro i
      apply continuous_pi; intro j
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      have hc : Continuous (fun z : ℝ => partialTransfer k layers (z - layer.width)) :=
        (ih ht).comp (continuous_id.sub continuous_const)
      exact (((continuous_apply 0).comp ((continuous_apply i).comp hc)).mul continuous_const).add
        (((continuous_apply 1).comp ((continuous_apply i).comp hc)).mul continuous_const)

theorem partialState_continuous (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (v : Fin 2 → ℂ) :
    Continuous (partialState k layers v) := by
  apply continuous_pi; intro i
  simp only [partialState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hc := partialTransfer_continuous k h
  exact (((continuous_apply 0).comp ((continuous_apply i).comp hc)).mul continuous_const).add
    (((continuous_apply 1).comp ((continuous_apply i).comp hc)).mul continuous_const)

theorem partialState_zero (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (v : Fin 2 → ℂ) : partialState k layers v 0 = v := by
  simp [partialState, partialTransfer_zero k h]

theorem partialState_cons (k : ℝ) (layer : HomogeneousLayer)
    (layers : List HomogeneousLayer) (v : Fin 2 → ℂ) (z : ℝ) :
    partialState k (layer :: layers) v z = if z ≤ layer.width then
      ![layerElectricField k layer (v 0) (v 1) z,
        layerMagneticField k layer (v 0) (v 1) z]
    else partialState k layers (layerTransfer k layer *ᵥ v) (z - layer.width) := by
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
  simp only [partialState, partialTransfer]
  split_ifs
  · simpa only [hv, layerElectricField, layerMagneticField] using
      homogeneousField_transfer k (refractiveIndex layer) (v 0) (v 1) z
  · exact (Matrix.mulVec_mulVec _ _ _).symm

theorem stackElectricField_cons (k : ℝ) (layer : HomogeneousLayer)
    (layers : List HomogeneousLayer) (v : Fin 2 → ℂ) (z : ℝ) :
    stackElectricField k (layer :: layers) v z = if z ≤ layer.width then
      layerElectricField k layer (v 0) (v 1) z
    else stackElectricField k layers (layerTransfer k layer *ᵥ v) (z - layer.width) := by
  unfold stackElectricField
  rw [partialState_cons]
  split_ifs <;> rfl

theorem stackMagneticField_cons (k : ℝ) (layer : HomogeneousLayer)
    (layers : List HomogeneousLayer) (v : Fin 2 → ℂ) (z : ℝ) :
    stackMagneticField k (layer :: layers) v z = if z ≤ layer.width then
      layerMagneticField k layer (v 0) (v 1) z
    else stackMagneticField k layers (layerTransfer k layer *ᵥ v) (z - layer.width) := by
  unfold stackMagneticField
  rw [partialState_cons]
  split_ifs <;> rfl

/-- Matching both values and derivatives glues the ordinary derivative at an interface. -/
theorem hasDerivAt_if_le {f g df dg : ℝ → ℂ} (a : ℝ)
    (hf : ∀ z, HasDerivAt f (df z) z) (hg : ∀ z, HasDerivAt g (dg z) z)
    (hfg : f a = g a) (hdfg : df a = dg a) (z : ℝ) :
    HasDerivAt (fun x => if x ≤ a then f x else g x)
      (if z ≤ a then df z else dg z) z := by
  rcases lt_trichotomy z a with hz | hz | hz
  · simp only [le_of_lt hz, ↓reduceIte]
    apply (hf z).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hz] with x hx
    exact if_pos (le_of_lt hx)
  · subst z
    simp only [le_refl, ↓reduceIte]
    have hleft := (hf a).hasDerivWithinAt (s := Iic a)
    have hright := (hg a).hasDerivWithinAt (s := Ici a)
    rw [← hdfg] at hright
    have hleft' : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) (df a) (Iic a) a :=
      hleft.congr (fun x hx => if_pos hx) (if_pos le_rfl)
    have hright' : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) (df a) (Ici a) a := by
      apply hright.congr
      · intro x hx
        by_cases hxa : x ≤ a
        · have hxa' : x = a := le_antisymm hxa hx
          subst x
          simp [hfg]
        · exact if_neg hxa
      · simp [hfg]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft'.union hright'
  · simp only [not_le.mpr hz, ↓reduceIte]
    apply (hg z).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hz] with x hx
    exact if_neg (not_le.mpr hx)

theorem stackElectricField_maxwell (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (v : Fin 2 → ℂ) (z : ℝ) :
    HasDerivAt (stackElectricField k layers v)
      (Complex.I * (k : ℂ) * stackMagneticField k layers v z) z := by
  induction layers generalizing v z with
  | nil =>
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    have hstate (x : ℝ) := homogeneousField_transfer k 1 (v 0) (v 1) x
    rw [hv] at hstate
    have he : stackElectricField k [] v = electricField k 1 (v 0) (v 1) := by
      funext x
      exact congrArg (fun u => u 0) (hstate x)
    have hh : stackMagneticField k [] v z = magneticField k 1 (v 0) (v 1) z :=
      congrArg (fun u => u 1) (hstate z)
    rw [he, hh]
    exact electricField_hasDerivAt k one_ne_zero _ _ _
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    let w := layerTransfer k layer *ᵥ v
    have hnext : partialState k layers w 0 = w := partialState_zero k ht w
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    have hb := layerField_transfer_boundary k layer (v 0) (v 1)
    rw [hv] at hb
    have heq : layerElectricField k layer (v 0) (v 1) layer.width =
        stackElectricField k layers w (layer.width - layer.width) := by
      simp only [sub_self, stackElectricField]
      rw [hnext]
      exact (congrArg (fun u => u 0) hb).symm
    have hdeq : Complex.I * (k : ℂ) * layerMagneticField k layer (v 0) (v 1) layer.width =
        Complex.I * (k : ℂ) * stackMagneticField k layers w (layer.width - layer.width) := by
      simp only [sub_self, stackMagneticField]
      rw [hnext]
      have hhb : w 1 = layerMagneticField k layer (v 0) (v 1) layer.width :=
        congrArg (fun u => u 1) hb
      rw [hhb]
    have hdnext (x : ℝ) : HasDerivAt (fun y => stackElectricField k layers w (y - layer.width))
        (Complex.I * (k : ℂ) * stackMagneticField k layers w (x - layer.width)) x := by
      convert (ih ht w (x - layer.width)).scomp x ((hasDerivAt_id x).sub_const layer.width) using 1 <;>
        simp [Function.comp_def]
    have hd := hasDerivAt_if_le layer.width
      (layerElectricField_maxwell k hl.1 (v 0) (v 1)) hdnext heq hdeq z
    have he : stackElectricField k (layer :: layers) v =
        (fun x => if x ≤ layer.width then layerElectricField k layer (v 0) (v 1) x
          else stackElectricField k layers w (x - layer.width)) := by
      funext x; exact stackElectricField_cons k layer layers v x
    rw [he, stackMagneticField_cons]
    split_ifs at hd ⊢ <;> exact hd

theorem stackElectricField_continuous (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (v : Fin 2 → ℂ) :
    Continuous (stackElectricField k layers v) :=
  (continuous_apply 0).comp (partialState_continuous k h v)

theorem stackMagneticField_continuous (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) (v : Fin 2 → ℂ) :
    Continuous (stackMagneticField k layers v) :=
  (continuous_apply 1).comp (partialState_continuous k h v)

theorem stackMagneticField_maxwell_offInterfaces (k : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers)
    (v : Fin 2 → ℂ) (z : ℝ) (hz : z ∉ interfacePositions layers) :
    HasDerivAt (stackMagneticField k layers v)
      (Complex.I * (k : ℂ) * ((stackRealProfile layers z : ℂ) +
        Complex.I * (stackLossProfile layers z : ℂ)) * stackElectricField k layers v z) z := by
  induction layers generalizing v z with
  | nil =>
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    have hstate (x : ℝ) := homogeneousField_transfer k 1 (v 0) (v 1) x
    rw [hv] at hstate
    have he : stackElectricField k [] v z = electricField k 1 (v 0) (v 1) z :=
      congrArg (fun u => u 0) (hstate z)
    have hh : stackMagneticField k [] v = magneticField k 1 (v 0) (v 1) := by
      funext x
      exact congrArg (fun u => u 1) (hstate x)
    simp only [he, hh, stackRealProfile, stackLossProfile, Complex.ofReal_one,
      Complex.ofReal_zero, mul_zero, add_zero, mul_one]
    simpa using magneticField_hasDerivAt k one_ne_zero (v 0) (v 1) z
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    have hzw : z ≠ layer.width := by
      intro heq
      apply hz
      simp [interfacePositions, heq]
    rcases lt_or_gt_of_ne hzw with hleft | hright
    · have hd := layerMagneticField_maxwell k hl.1 (v 0) (v 1) z
      have hde : HasDerivAt (stackMagneticField k (layer :: layers) v)
          (Complex.I * (k : ℂ) * relativePermittivity layer *
            layerElectricField k layer (v 0) (v 1) z) z := by
        apply hd.congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hleft] with x hx
        rw [stackMagneticField_cons, if_pos (le_of_lt hx)]
      simpa only [stackElectricField_cons, if_pos (le_of_lt hleft),
        stackRealProfile, stackLossProfile, if_pos hleft, relativePermittivity] using hde
    · let w := layerTransfer k layer *ᵥ v
      have htail : z - layer.width ∉ interfacePositions layers := by
        intro hmem
        apply hz
        simp only [interfacePositions, List.mem_cons]
        right
        exact List.mem_map.mpr ⟨z - layer.width, hmem, by ring⟩
      have hd := (ih ht w (z - layer.width) htail).scomp z
        ((hasDerivAt_id z).sub_const layer.width)
      have hd' : HasDerivAt (fun x => stackMagneticField k layers w (x - layer.width))
          (Complex.I * (k : ℂ) * ((stackRealProfile layers (z - layer.width) : ℂ) +
            Complex.I * (stackLossProfile layers (z - layer.width) : ℂ)) *
            stackElectricField k layers w (z - layer.width)) z := by
        convert hd using 1 <;> simp [Function.comp_def]
      have hde := hd'.congr_of_eventuallyEq (f₁ := stackMagneticField k (layer :: layers) v) (by
        filter_upwards [Ioi_mem_nhds hright] with x hx
        rw [stackMagneticField_cons, if_neg (not_le.mpr hx)])
      simpa only [stackElectricField_cons, if_neg (not_le.mpr hright),
        stackRealProfile, stackLossProfile, if_neg (not_lt.mpr (le_of_lt hright))] using hde

theorem stackLossProfile_measurable (layers : List HomogeneousLayer) :
    Measurable (stackLossProfile layers) := by
  induction layers with
  | nil => exact measurable_const
  | cons layer layers ih =>
    exact Measurable.ite measurableSet_Iio measurable_const
      (ih.comp (measurable_id.sub_const layer.width))

theorem stackRealProfile_measurable (layers : List HomogeneousLayer) :
    Measurable (stackRealProfile layers) := by
  induction layers with
  | nil => exact measurable_const
  | cons layer layers ih =>
    exact Measurable.ite measurableSet_Iio measurable_const
      (ih.comp (measurable_id.sub_const layer.width))

theorem stackLossProfile_integrableOn (a b : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) :
    IntegrableOn (stackLossProfile layers) (uIcc a b) := by
  have hc : IntegrableOn (fun _ : ℝ => Q) (uIcc a b) :=
    continuous_const.integrableOn_uIcc
  apply hc.mono' (stackLossProfile_measurable layers).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (stackLossProfile_bounds hQ h x).1]
    exact (stackLossProfile_bounds hQ h x).2)

theorem stackLossProfile_intervalIntegrable (a b : ℝ) {P Q : ℝ}
    {layers : List HomogeneousLayer} (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) :
    IntervalIntegrable (stackLossProfile layers) volume a b :=
  (stackLossProfile_integrableOn a b hQ h).intervalIntegrable

theorem stackLossProfile_integral {P Q : ℝ} {layers : List HomogeneousLayer}
    (hQ : 0 ≤ Q) (h : StackAdmissible P Q layers) :
    ∫ z in 0..totalThickness layers, stackLossProfile layers z = integratedLoss layers := by
  induction layers with
  | nil => simp [totalThickness, integratedLoss]
  | cons layer layers ih =>
    have hl := h layer (by simp)
    have ht : StackAdmissible P Q layers := fun other hm => h other (by simp [hm])
    change (∫ z in 0..layer.width + totalThickness layers,
      stackLossProfile (layer :: layers) z) = layer.q * layer.width + integratedLoss layers
    have hint₁ := stackLossProfile_intervalIntegrable 0 layer.width hQ h
    have hint₂ := stackLossProfile_intervalIntegrable layer.width
      (layer.width + totalThickness layers) hQ h
    rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
    have hleft : (∫ z in 0..layer.width, stackLossProfile (layer :: layers) z) =
        layer.q * layer.width := by
      rw [intervalIntegral.integral_congr_Ioo_of_le hl.2.2.2.2
        (g := fun _ => layer.q) (fun z hz => by simp [stackLossProfile, hz.2])]
      simp [mul_comm]
    have hright : (∫ z in layer.width..layer.width + totalThickness layers,
        stackLossProfile (layer :: layers) z) =
        ∫ z in 0..totalThickness layers, stackLossProfile layers z := by
      rw [intervalIntegral.integral_congr_Ioo_of_le
        (le_add_of_nonneg_right (totalThickness_nonneg ht))
        (g := fun z => stackLossProfile layers (z - layer.width))
        (fun z hz => by simp [stackLossProfile, not_lt.mpr (le_of_lt hz.1)])]
      rw [intervalIntegral.integral_comp_sub_right]
      simp
    rw [hleft, hright, ih ht]

#print axioms homogeneousTransfer_zero
#print axioms partialTransfer_zero
#print axioms partialTransfer_total
#print axioms partialTransfer_det
#print axioms stackLossProfile_bounds
#print axioms stackRealProfile_bounds
#print axioms homogeneousTransfer_continuous
#print axioms partialTransfer_continuous
#print axioms partialState_continuous
#print axioms partialState_zero
#print axioms partialState_cons
#print axioms stackElectricField_cons
#print axioms stackMagneticField_cons
#print axioms hasDerivAt_if_le
#print axioms stackElectricField_maxwell
#print axioms stackElectricField_continuous
#print axioms stackMagneticField_continuous
#print axioms stackMagneticField_maxwell_offInterfaces
#print axioms stackLossProfile_measurable
#print axioms stackRealProfile_measurable
#print axioms stackLossProfile_integrableOn
#print axioms stackLossProfile_intervalIntegrable
#print axioms stackLossProfile_integral

end OQ7
