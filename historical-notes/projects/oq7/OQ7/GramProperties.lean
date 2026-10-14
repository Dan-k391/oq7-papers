import OQ7.Gram

noncomputable section

namespace OQ7

open MeasureTheory
open scoped Matrix ComplexOrder

theorem weightedGram_conjTranspose {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : α → ℝ) (v : α → Fin 2 → ℂ) :
    (weightedGram μ q v).conjTranspose = weightedGram μ q v := by
  ext i j
  simp only [weightedGram, Matrix.conjTranspose_apply, Complex.star_def]
  rw [← integral_conj]
  congr 1
  funext x
  simp
  ring

theorem weightedGram_quadraticDensity {α : Type*} (q : α → ℝ)
    (v : α → Fin 2 → ℂ) (u : Fin 2 → ℂ) (x : α) :
    ((q x * Complex.normSq (v x 0 * u 0 + v x 1 * u 1) : ℝ) : ℂ) =
      star (u 0) * ((q x : ℂ) * star (v x 0) * v x 0) * u 0 +
      star (u 0) * ((q x : ℂ) * star (v x 0) * v x 1) * u 1 +
      star (u 1) * ((q x : ℂ) * star (v x 1) * v x 0) * u 0 +
      star (u 1) * ((q x : ℂ) * star (v x 1) * v x 1) * u 1 := by
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_add, map_mul, Complex.star_def]
  ring

theorem weightedGram_quadratic {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : α → ℝ) (v : α → Fin 2 → ℂ)
    (hint : ∀ i j, Integrable (fun x => (q x : ℂ) * star (v x i) * v x j) μ)
    (u : Fin 2 → ℂ) :
    star u ⬝ᵥ (weightedGram μ q v *ᵥ u) =
      ((∫ x, q x * Complex.normSq (v x 0 * u 0 + v x 1 * u 1) ∂μ : ℝ) : ℂ) := by
  have h00 := ((hint 0 0).const_mul (star (u 0))).mul_const (u 0)
  have h01 := ((hint 0 1).const_mul (star (u 0))).mul_const (u 1)
  have h10 := ((hint 1 0).const_mul (star (u 1))).mul_const (u 0)
  have h11 := ((hint 1 1).const_mul (star (u 1))).mul_const (u 1)
  rw [← integral_complex_ofReal]
  rw [funext (weightedGram_quadraticDensity q v u)]
  rw [integral_add, integral_add, integral_add]
  rotate_left 1
  · exact h00
  · exact h01
  · exact h00.add h01
  · exact h10
  · exact (h00.add h01).add h10
  · exact h11
  simp only [integral_mul_const, integral_const_mul]
  simp [weightedGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem weightedGram_posSemidef {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : α → ℝ) (v : α → Fin 2 → ℂ)
    (hint : ∀ i j, Integrable (fun x => (q x : ℂ) * star (v x i) * v x j) μ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ q x) : (weightedGram μ q v).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact weightedGram_conjTranspose μ q v
  · intro u
    rw [weightedGram_quadratic μ q v hint]
    apply RCLike.nonneg_iff.mpr
    constructor
    · exact integral_nonneg_of_ae (hq.mono fun x hx =>
        mul_nonneg hx (Complex.normSq_nonneg _))
    · simp

#print axioms weightedGram_conjTranspose
#print axioms weightedGram_quadraticDensity
#print axioms weightedGram_quadratic
#print axioms weightedGram_posSemidef

end OQ7
