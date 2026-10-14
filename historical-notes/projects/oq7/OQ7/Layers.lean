import OQ7.TwoPort
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Sqrt

namespace OQ7

/-- An actual homogeneous dielectric layer: real and imaginary permittivity, and width. -/
structure HomogeneousLayer where
  p : ℝ
  q : ℝ
  width : ℝ

/-- The paper's material caps and nonnegative geometric layer width. -/
def LayerAdmissible (P Q : ℝ) (layer : HomogeneousLayer) : Prop :=
  1 ≤ layer.p ∧ layer.p ≤ P ∧ 0 ≤ layer.q ∧ layer.q ≤ Q ∧ 0 ≤ layer.width

/-- A finite multilayer with the same material caps on every layer. -/
def StackAdmissible (P Q : ℝ) (layers : List HomogeneousLayer) : Prop :=
  ∀ layer ∈ layers, LayerAdmissible P Q layer

def totalThickness (layers : List HomogeneousLayer) : ℝ :=
  (layers.map HomogeneousLayer.width).sum

/-- This is integrated imaginary permittivity, rather than absorbed power. -/
def integratedLoss (layers : List HomogeneousLayer) : ℝ :=
  (layers.map (fun layer => layer.q * layer.width)).sum

def relativePermittivity (layer : HomogeneousLayer) : ℂ :=
  (layer.p : ℂ) + Complex.I * (layer.q : ℂ)

noncomputable def refractiveIndex (layer : HomogeneousLayer) : ℂ :=
  Complex.sqrt (relativePermittivity layer)

theorem refractiveIndex_sq (layer : HomogeneousLayer) :
    refractiveIndex layer ^ 2 = relativePermittivity layer := by
  simp [refractiveIndex, Complex.sqrt]

theorem relativePermittivity_ne_zero {layer : HomogeneousLayer} (hp : 1 ≤ layer.p) :
    relativePermittivity layer ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [relativePermittivity] at hre
  linarith

theorem refractiveIndex_ne_zero {layer : HomogeneousLayer} (hp : 1 ≤ layer.p) :
    refractiveIndex layer ≠ 0 := by
  intro h
  have hs := refractiveIndex_sq layer
  rw [h] at hs
  exact relativePermittivity_ne_zero hp (by simpa using hs.symm)

/-- Exact homogeneous-layer formula in state coordinates `(E, E'/(i k))`.
The eventual Maxwell verification must connect this formula to the differential equation. -/
noncomputable def homogeneousTransfer (k : ℝ) (n : ℂ) (width : ℝ) : Mat2 :=
  let θ := (k : ℂ) * n * (width : ℂ)
  !![Complex.cos θ, Complex.I * Complex.sin θ / n;
     Complex.I * n * Complex.sin θ, Complex.cos θ]

noncomputable def layerTransfer (k : ℝ) (layer : HomogeneousLayer) : Mat2 :=
  homogeneousTransfer k (refractiveIndex layer) layer.width

theorem homogeneousTransfer_det (k : ℝ) {n : ℂ} (hn : n ≠ 0) (width : ℝ) :
    (homogeneousTransfer k n width).det = 1 := by
  let θ := (k : ℂ) * n * (width : ℂ)
  have hcross : (Complex.I * Complex.sin θ / n) *
      (Complex.I * n * Complex.sin θ) = -(Complex.sin θ) ^ 2 := by
    field_simp
    ring_nf
    simp [Complex.I_sq]
  change (!![Complex.cos θ, Complex.I * Complex.sin θ / n;
    Complex.I * n * Complex.sin θ, Complex.cos θ] : Mat2).det = 1
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hcross]
  simpa [sq, sub_neg_eq_add, add_comm] using Complex.sin_sq_add_cos_sq θ

theorem layerTransfer_det (k : ℝ) {P Q : ℝ} {layer : HomogeneousLayer}
    (h : LayerAdmissible P Q layer) : (layerTransfer k layer).det = 1 := by
  exact homogeneousTransfer_det k (refractiveIndex_ne_zero h.1) layer.width

/-- Layers are listed from left to right, so their state transfers multiply in reverse order. -/
noncomputable def stackTransfer (k : ℝ) : List HomogeneousLayer → Mat2
  | [] => 1
  | layer :: layers => stackTransfer k layers * layerTransfer k layer

theorem stackTransfer_det (k : ℝ) {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) : (stackTransfer k layers).det = 1 := by
  induction layers with
  | nil => simp [stackTransfer]
  | cons layer layers ih =>
      rw [stackTransfer, Matrix.det_mul, ih]
      · simp [layerTransfer_det k (h layer (by simp))]
      · intro other hm
        exact h other (by simp [hm])

theorem totalThickness_nonneg {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) : 0 ≤ totalThickness layers := by
  induction layers with
  | nil => simp [totalThickness]
  | cons layer layers ih =>
      simp only [totalThickness, List.map_cons, List.sum_cons]
      apply add_nonneg (h layer (by simp)).2.2.2.2
      apply ih
      intro other hm
      exact h other (by simp [hm])

theorem integratedLoss_nonneg {P Q : ℝ} {layers : List HomogeneousLayer}
    (h : StackAdmissible P Q layers) : 0 ≤ integratedLoss layers := by
  induction layers with
  | nil => simp [integratedLoss]
  | cons layer layers ih =>
      simp only [integratedLoss, List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact mul_nonneg (h layer (by simp)).2.2.1 (h layer (by simp)).2.2.2.2
      · apply ih
        intro other hm
        exact h other (by simp [hm])

theorem integratedLoss_le_cap_mul_thickness {P Q : ℝ}
    {layers : List HomogeneousLayer} (h : StackAdmissible P Q layers) :
    integratedLoss layers ≤ Q * totalThickness layers := by
  induction layers with
  | nil => simp [integratedLoss, totalThickness]
  | cons layer layers ih =>
      have hl := h layer (by simp)
      have ht : StackAdmissible P Q layers := by
        intro other hm
        exact h other (by simp [hm])
      have hw := mul_le_mul_of_nonneg_right hl.2.2.2.1 hl.2.2.2.2
      have hi := ih ht
      simp only [integratedLoss, totalThickness, List.map_cons, List.sum_cons] at *
      nlinarith

#print axioms refractiveIndex_sq
#print axioms relativePermittivity_ne_zero
#print axioms refractiveIndex_ne_zero
#print axioms homogeneousTransfer_det
#print axioms layerTransfer_det
#print axioms stackTransfer_det
#print axioms totalThickness_nonneg
#print axioms integratedLoss_nonneg
#print axioms integratedLoss_le_cap_mul_thickness

end OQ7
