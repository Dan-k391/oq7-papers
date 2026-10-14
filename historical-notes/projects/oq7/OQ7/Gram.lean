import OQ7.Fields
import OQ7.Transfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace OQ7

open scoped Matrix
open MeasureTheory

/-- The polarized physical flux, whose diagonal is twice directed flux. -/
def mixedFlux (E₁ H₁ E₂ H₂ : ℂ) : ℂ := star E₁ * H₂ + star H₁ * E₂

theorem mixedFlux_derivative_algebra (k p q : ℝ) (E₁ H₁ E₂ H₂ : ℂ) :
    (star (Complex.I * (k : ℂ) * H₁) * H₂ +
      star E₁ * (Complex.I * (k : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ)) * E₂)) +
    (star (Complex.I * (k : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ)) * E₁) * E₂ +
      star H₁ * (Complex.I * (k : ℂ) * H₂)) =
        (-2 * (k : ℂ) * (q : ℂ)) * (star E₁ * E₂) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Maxwell's polarized flux law at any point where the actual field derivatives exist. -/
theorem maxwellMixedFlux_hasDerivAt (k p q : ℝ) (E₁ H₁ E₂ H₂ : ℝ → ℂ) (z : ℝ)
    (hE₁ : HasDerivAt E₁ (Complex.I * (k : ℂ) * H₁ z) z)
    (hH₁ : HasDerivAt H₁
      (Complex.I * (k : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ)) * E₁ z) z)
    (hE₂ : HasDerivAt E₂ (Complex.I * (k : ℂ) * H₂ z) z)
    (hH₂ : HasDerivAt H₂
      (Complex.I * (k : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ)) * E₂ z) z) :
    HasDerivAt (fun x => mixedFlux (E₁ x) (H₁ x) (E₂ x) (H₂ x))
      ((-2 * (k : ℂ) * (q : ℂ)) * (star (E₁ z) * E₂ z)) z := by
  convert (hE₁.star.mul hH₂).add (hH₁.star.mul hE₂) using 1
  · rfl
  · exact (mixedFlux_derivative_algebra k p q _ _ _ _).symm

theorem layerMixedFlux_hasDerivAt (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (E₁ H₁ E₂ H₂ : ℂ) (z : ℝ) :
    HasDerivAt (fun x => mixedFlux (layerElectricField k layer E₁ H₁ x)
      (layerMagneticField k layer E₁ H₁ x) (layerElectricField k layer E₂ H₂ x)
      (layerMagneticField k layer E₂ H₂ x))
      ((-2 * (k : ℂ) * (layer.q : ℂ)) *
        (star (layerElectricField k layer E₁ H₁ z) *
          layerElectricField k layer E₂ H₂ z)) z := by
  have hE₁ := layerElectricField_maxwell k hp E₁ H₁ z
  have hH₁ := layerMagneticField_maxwell k hp E₁ H₁ z
  have hE₂ := layerElectricField_maxwell k hp E₂ H₂ z
  have hH₂ := layerMagneticField_maxwell k hp E₂ H₂ z
  convert (hE₁.star.mul hH₂).add (hH₁.star.mul hE₂) using 1
  · rfl
  · exact (mixedFlux_derivative_algebra k layer.p layer.q _ _ _ _).symm

theorem layerMixedFlux_integral (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (E₁ H₁ E₂ H₂ : ℂ) :
    mixedFlux E₁ H₁ E₂ H₂ -
      mixedFlux (layerElectricField k layer E₁ H₁ layer.width)
        (layerMagneticField k layer E₁ H₁ layer.width)
        (layerElectricField k layer E₂ H₂ layer.width)
        (layerMagneticField k layer E₂ H₂ layer.width) =
      (2 * (k : ℂ) * (layer.q : ℂ)) *
        ∫ z in 0..layer.width, star (layerElectricField k layer E₁ H₁ z) *
          layerElectricField k layer E₂ H₂ z := by
  have hE₁ : Continuous (layerElectricField k layer E₁ H₁) :=
    continuous_iff_continuousAt.mpr fun z =>
      (layerElectricField_maxwell k hp E₁ H₁ z).continuousAt
  have hE₂ : Continuous (layerElectricField k layer E₂ H₂) :=
    continuous_iff_continuousAt.mpr fun z =>
      (layerElectricField_maxwell k hp E₂ H₂ z).continuousAt
  have hint := (((hE₁.star).mul hE₂).const_mul
    (-2 * (k : ℂ) * (layer.q : ℂ))).intervalIntegrable (μ := volume) 0 layer.width
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => layerMixedFlux_hasDerivAt k hp E₁ H₁ E₂ H₂ z) hint
  rw [intervalIntegral.integral_const_mul] at h
  have hzero₁ := homogeneousField_initial k (refractiveIndex layer) E₁ H₁
  have hzero₂ := homogeneousField_initial k (refractiveIndex layer) E₂ H₂
  change _ = _ - mixedFlux
    (electricField k (refractiveIndex layer) E₁ H₁ 0)
    (magneticField k (refractiveIndex layer) E₁ H₁ 0)
    (electricField k (refractiveIndex layer) E₂ H₂ 0)
    (magneticField k (refractiveIndex layer) E₂ H₂ 0) at h
  rw [hzero₁.1, hzero₁.2, hzero₂.1, hzero₂.2] at h
  linear_combination h

/-- The adjugate written explicitly in the physical two-dimensional coordinates. -/
def adjugate2 (F : Mat2) : Mat2 := !![F 1 1, -F 0 1; -F 1 0, F 0 0]

theorem adjugate2_mul (F : Mat2) : adjugate2 F * F = F.det • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.smul_apply] <;> ring

theorem mul_adjugate2 (F : Mat2) : F * adjugate2 F = F.det • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.smul_apply] <;> ring

theorem matrixElectricWedge (X Y B : Mat2) :
    (X * B) 0 0 * (Y * B) 0 1 - (X * B) 0 1 * (Y * B) 0 0 =
      B.det * (Y * adjugate2 X) 0 1 := by
  simp [adjugate2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- The physical input-state normalization supplies the exact factor of transmission. -/
theorem matrixElectricWedge_normSq (k : ℝ) (hk : k ≠ 0) (rL t : ℂ) (X Y : Mat2) :
    Complex.normSq
      ((X * inputFieldStates rL t) 0 0 * (Y * inputFieldStates rL t) 0 1 -
        (X * inputFieldStates rL t) 0 1 * (Y * inputFieldStates rL t) 0 0) =
      4 * k ^ 2 * Complex.normSq t *
        Complex.normSq ((Y * adjugate2 X) 0 1 / (Complex.I * (k : ℂ))) := by
  rw [matrixElectricWedge, inputFieldStates_det]
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal,
    Complex.normSq_div, Complex.normSq_I]
  norm_num [Complex.normSq_apply]
  field_simp

/-- The actual field Gram integral, defined entrywise, before multiplying by `k`. -/
def weightedGram {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : α → ℝ) (v : α → Fin 2 → ℂ) : Mat2 :=
  fun i j => ∫ x, (q x : ℂ) * star (v x i) * v x j ∂μ

def gramPairKernel {α : Type*} (q : α → ℝ) (v : α → Fin 2 → ℂ)
    (p : α × α) : ℝ :=
  q p.1 * q p.2 * Complex.normSq (v p.1 0 * v p.2 1 - v p.1 1 * v p.2 0)

theorem gramPairKernel_complex_expand {α : Type*} (q : α → ℝ)
    (v : α → Fin 2 → ℂ) (p : α × α) :
    (gramPairKernel q v p : ℂ) =
      ((q p.1 : ℂ) * star (v p.1 0) * v p.1 0) *
        ((q p.2 : ℂ) * star (v p.2 1) * v p.2 1) +
      ((q p.1 : ℂ) * star (v p.1 1) * v p.1 1) *
        ((q p.2 : ℂ) * star (v p.2 0) * v p.2 0) -
      ((q p.1 : ℂ) * star (v p.1 0) * v p.1 1) *
        ((q p.2 : ℂ) * star (v p.2 1) * v p.2 0) -
      ((q p.1 : ℂ) * star (v p.1 1) * v p.1 0) *
        ((q p.2 : ℂ) * star (v p.2 0) * v p.2 1) := by
  unfold gramPairKernel
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sub, map_mul, Complex.star_def]
  ring

theorem weightedGram_det_squareIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (q : α → ℝ) (v : α → Fin 2 → ℂ)
    (hint : ∀ i j, Integrable (fun x => (q x : ℂ) * star (v x i) * v x j) μ) :
    ∫ p, (gramPairKernel q v p : ℂ) ∂μ.prod μ = 2 * (weightedGram μ q v).det := by
  have h00 := hint 0 0
  have h01 := hint 0 1
  have h10 := hint 1 0
  have h11 := hint 1 1
  have hexpand := funext (gramPairKernel_complex_expand q v)
  rw [hexpand]
  rw [integral_sub, integral_sub, integral_add]
  rotate_left 1
  · exact h00.mul_prod h11
  · exact h11.mul_prod h00
  · exact (h00.mul_prod h11).add (h11.mul_prod h00)
  · exact h01.mul_prod h10
  · exact ((h00.mul_prod h11).add (h11.mul_prod h00)).sub (h01.mul_prod h10)
  · exact h10.mul_prod h01
  rw [integral_prod_mul (μ := μ) (ν := μ)
    (fun x => (q x : ℂ) * star (v x 0) * v x 0)
    (fun x => (q x : ℂ) * star (v x 1) * v x 1)]
  rw [integral_prod_mul (μ := μ) (ν := μ)
    (fun x => (q x : ℂ) * star (v x 1) * v x 1)
    (fun x => (q x : ℂ) * star (v x 0) * v x 0)]
  rw [integral_prod_mul (μ := μ) (ν := μ)
    (fun x => (q x : ℂ) * star (v x 0) * v x 1)
    (fun x => (q x : ℂ) * star (v x 1) * v x 0)]
  rw [integral_prod_mul (μ := μ) (ν := μ)
    (fun x => (q x : ℂ) * star (v x 1) * v x 0)
    (fun x => (q x : ℂ) * star (v x 0) * v x 1)]
  simp only [weightedGram, Matrix.det_fin_two]
  ring

theorem mixedFlux_matrix_entry (B : Mat2) (i j : Fin 2) :
    mixedFlux (B 0 i) (B 1 i) (B 0 j) (B 1 j) =
      (B.conjTranspose * fluxForm * B) i j := by
  simp [mixedFlux, fluxForm, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  ring

theorem fluxDefect_congruence_entry (F B : Mat2) (i j : Fin 2) :
    (B.conjTranspose * fluxDefect F * B) i j =
      mixedFlux (B 0 i) (B 1 i) (B 0 j) (B 1 j) -
        mixedFlux ((F * B) 0 i) ((F * B) 1 i) ((F * B) 0 j) ((F * B) 1 j) := by
  have hc : B.conjTranspose * fluxDefect F * B =
      B.conjTranspose * fluxForm * B - (F * B).conjTranspose * fluxForm * (F * B) := by
    simp [fluxDefect, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  rw [hc, Matrix.sub_apply, mixedFlux_matrix_entry, mixedFlux_matrix_entry]

theorem layerTransfer_fieldColumn (k : ℝ) (layer : HomogeneousLayer) (B : Mat2)
    (j : Fin 2) :
    (layerTransfer k layer * B) 0 j =
      layerElectricField k layer (B 0 j) (B 1 j) layer.width ∧
    (layerTransfer k layer * B) 1 j =
      layerMagneticField k layer (B 0 j) (B 1 j) layer.width := by
  constructor <;>
    simp [layerTransfer, homogeneousTransfer, layerElectricField, layerMagneticField,
      electricField, magneticField, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact Gram integral of an actual homogeneous Maxwell layer for any initial field states. -/
theorem layerFluxDefect_gram_entry (k : ℝ) {layer : HomogeneousLayer}
    (hp : 1 ≤ layer.p) (B : Mat2) (i j : Fin 2) :
    (B.conjTranspose * fluxDefect (layerTransfer k layer) * B) i j =
      (2 * (k : ℂ) * (layer.q : ℂ)) *
        ∫ z in 0..layer.width,
          star (layerElectricField k layer (B 0 i) (B 1 i) z) *
            layerElectricField k layer (B 0 j) (B 1 j) z := by
  rw [fluxDefect_congruence_entry]
  rw [(layerTransfer_fieldColumn k layer B i).1,
    (layerTransfer_fieldColumn k layer B i).2,
    (layerTransfer_fieldColumn k layer B j).1,
    (layerTransfer_fieldColumn k layer B j).2]
  exact layerMixedFlux_integral k hp _ _ _ _

theorem gramPairKernel_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (q : α → ℝ) (v : α → Fin 2 → ℂ)
    (hint : ∀ i j, Integrable (fun x => (q x : ℂ) * star (v x i) * v x j) μ) :
    Integrable (gramPairKernel q v) (μ.prod μ) := by
  have hC : Integrable (fun p => (gramPairKernel q v p : ℂ)) (μ.prod μ) := by
    have h := (((hint 0 0).mul_prod (hint 1 1)).add
      ((hint 1 1).mul_prod (hint 0 0))).sub
        ((hint 0 1).mul_prod (hint 1 0)) |>.sub
          ((hint 1 0).mul_prod (hint 0 1))
    exact h.congr (Filter.Eventually.of_forall fun p =>
      (gramPairKernel_complex_expand q v p).symm)
  simpa using hC.re

theorem gramPairKernel_swap {α : Type*} (q : α → ℝ)
    (v : α → Fin 2 → ℂ) (p : α × α) :
    gramPairKernel q v p.swap = gramPairKernel q v p := by
  have hw : v p.2 0 * v p.1 1 - v p.2 1 * v p.1 0 =
      -(v p.1 0 * v p.2 1 - v p.1 1 * v p.2 0) := by ring
  change q p.2 * q p.1 * Complex.normSq
      (v p.2 0 * v p.1 1 - v p.2 1 * v p.1 0) =
    q p.1 * q p.2 * Complex.normSq (v p.1 0 * v p.2 1 - v p.1 1 * v p.2 0)
  rw [hw, Complex.normSq_neg]
  ring

theorem gramPairKernel_diagonal {α : Type*} (q : α → ℝ)
    (v : α → Fin 2 → ℂ) (x : α) : gramPairKernel q v (x, x) = 0 := by
  simp [gramPairKernel, mul_comm]

/-- Symmetry and the vanishing diagonal convert the Gram square integral into a triangle. -/
theorem gramPairKernel_square_eq_twice_triangle (μ : Measure ℝ) [SFinite μ]
    (q : ℝ → ℝ) (v : ℝ → Fin 2 → ℂ)
    (hint : Integrable (gramPairKernel q v) (μ.prod μ)) :
    ∫ p, gramPairKernel q v p ∂μ.prod μ =
      2 * ∫ p in {p : ℝ × ℝ | p.1 < p.2}, gramPairKernel q v p ∂μ.prod μ := by
  let s : Set (ℝ × ℝ) := {p | p.1 < p.2}
  let t : Set (ℝ × ℝ) := {p | p.2 < p.1}
  have hs : MeasurableSet s := measurableSet_lt measurable_fst measurable_snd
  have ht : MeasurableSet t := measurableSet_lt measurable_snd measurable_fst
  have hsplit : gramPairKernel q v = s.indicator (gramPairKernel q v) +
      t.indicator (gramPairKernel q v) := by
    funext p
    by_cases hxy : p.1 < p.2
    · simp [s, t, hxy, not_lt.mpr (le_of_lt hxy)]
    · by_cases hyx : p.2 < p.1
      · simp [s, t, hxy, hyx]
      · have heq : p.1 = p.2 := le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)
        have hz : gramPairKernel q v p = 0 := by
          rcases p with ⟨x, y⟩
          dsimp at heq
          subst y
          exact gramPairKernel_diagonal q v x
        simp [s, t, hxy, hyx, hz]
  have hswap : (fun p => s.indicator (gramPairKernel q v) p.swap) =
      t.indicator (gramPairKernel q v) := by
    funext p
    by_cases h : p.2 < p.1
    · have hpS : p.swap ∈ s := h
      have hpT : p ∈ t := h
      rw [Set.indicator_of_mem hpS, Set.indicator_of_mem hpT]
      exact gramPairKernel_swap q v p
    · simp [s, t, Set.indicator, Prod.swap, h]
  have hi : ∫ p, t.indicator (gramPairKernel q v) p ∂μ.prod μ =
      ∫ p, s.indicator (gramPairKernel q v) p ∂μ.prod μ := by
    rw [← hswap]
    exact integral_prod_swap _
  calc
    ∫ p, gramPairKernel q v p ∂μ.prod μ =
        ∫ p, s.indicator (gramPairKernel q v) p +
          t.indicator (gramPairKernel q v) p ∂μ.prod μ := by
      congr 1
    _ = (∫ p, s.indicator (gramPairKernel q v) p ∂μ.prod μ) +
        ∫ p, t.indicator (gramPairKernel q v) p ∂μ.prod μ :=
      integral_add (hint.indicator hs) (hint.indicator ht)
    _ = 2 * ∫ p, s.indicator (gramPairKernel q v) p ∂μ.prod μ := by rw [hi]; ring
    _ = _ := by rw [integral_indicator hs]

/-- The exact determinant of a weighted two-field Gram integral, on the physical order triangle. -/
theorem weightedGram_det_triangleIntegral (μ : Measure ℝ) [SFinite μ]
    (q : ℝ → ℝ) (v : ℝ → Fin 2 → ℂ)
    (hint : ∀ i j, Integrable (fun x => (q x : ℂ) * star (v x i) * v x j) μ) :
    (weightedGram μ q v).det =
      ((∫ p in {p : ℝ × ℝ | p.1 < p.2}, gramPairKernel q v p ∂μ.prod μ : ℝ) : ℂ) := by
  have hs := weightedGram_det_squareIntegral μ q v hint
  have ht := gramPairKernel_square_eq_twice_triangle μ q v
    (gramPairKernel_integrable μ q v hint)
  rw [integral_complex_ofReal, ht] at hs
  push_cast at hs
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  exact hs.symm

#print axioms mixedFlux_derivative_algebra
#print axioms maxwellMixedFlux_hasDerivAt
#print axioms layerMixedFlux_hasDerivAt
#print axioms layerMixedFlux_integral
#print axioms adjugate2_mul
#print axioms mul_adjugate2
#print axioms matrixElectricWedge
#print axioms matrixElectricWedge_normSq
#print axioms gramPairKernel_complex_expand
#print axioms weightedGram_det_squareIntegral
#print axioms mixedFlux_matrix_entry
#print axioms fluxDefect_congruence_entry
#print axioms layerTransfer_fieldColumn
#print axioms layerFluxDefect_gram_entry
#print axioms gramPairKernel_integrable
#print axioms gramPairKernel_swap
#print axioms gramPairKernel_diagonal
#print axioms gramPairKernel_square_eq_twice_triangle
#print axioms weightedGram_det_triangleIntegral

end OQ7
