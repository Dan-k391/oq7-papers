import OQ7.FourierSquare
import OQ7.FourierCap
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace OQ7
open MeasureTheory Set

theorem symmetric_squareIntegral_twice_triangle (μ : Measure ℝ) [SFinite μ]
    (f : ℝ × ℝ → ℝ) (hint : Integrable f (μ.prod μ))
    (hsym : ∀ x y, f (x, y) = f (y, x)) (hdiag : ∀ x, f (x, x) = 0) :
    (∫ p, f p ∂μ.prod μ) = 2 * ∫ p in {p : ℝ × ℝ | p.1 < p.2}, f p ∂μ.prod μ := by
  classical
  let upper : Set (ℝ × ℝ) := {p | p.1 < p.2}
  let lower : Set (ℝ × ℝ) := {p | p.2 < p.1}
  have hupper : MeasurableSet upper := (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hlower : MeasurableSet lower := (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hsplit : f = fun p => upper.indicator f p + lower.indicator f p := by
    funext p
    rcases p with ⟨x, y⟩
    by_cases hxy : x < y
    · have hyx : ¬ y < x := not_lt.mpr hxy.le
      simp [upper, lower, hxy, hyx]
    · by_cases hyx : y < x
      · simp [upper, lower, hxy, hyx]
      · have hEq : x = y := le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)
        subst y
        simp [upper, lower, hdiag]
  have hswap : (fun p : ℝ × ℝ => upper.indicator f p.swap) = lower.indicator f := by
    funext p
    rcases p with ⟨x, y⟩
    by_cases hyx : y < x
    · simp only [Prod.swap_prod_mk, indicator_of_mem (show (y, x) ∈ upper from hyx),
        indicator_of_mem (show (x, y) ∈ lower from hyx)]
      exact (hsym x y).symm
    · simp only [Prod.swap_prod_mk,
        indicator_of_notMem (show (y, x) ∉ upper from hyx),
        indicator_of_notMem (show (x, y) ∉ lower from hyx)]
  have hsame := integral_prod_swap (μ := μ) (ν := μ) (upper.indicator f)
  rw [hswap, integral_indicator hupper, integral_indicator hlower] at hsame
  calc
    _ = (∫ p in upper, f p ∂μ.prod μ) + ∫ p in lower, f p ∂μ.prod μ := by
      conv_lhs => rw [hsplit]
      rw [integral_add (hint.indicator hupper) (hint.indicator hlower),
        integral_indicator hupper, integral_indicator hlower]
    _ = _ := by rw [hsame]; ring

theorem sineSquare_product_integrable {q : ℝ → ℝ} {a b K : ℝ}
    (hq : IntervalIntegrable q volume a b) :
    Integrable (fun p : ℝ × ℝ => q p.1 * q p.2 * Real.sin (K * (p.2 - p.1)) ^ 2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (K * (p.2 - p.1)) ^ 2) := by fun_prop
  apply (hq.1.mul_prod hq.1).mul_bdd (c := 1) hsin.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.sin (K * (p.2 - p.1))))] using
      Real.sin_sq_le_one (K * (p.2 - p.1))

theorem sineSquare_triangleIntegral_fourier {q : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b) (hq : IntervalIntegrable q volume a b) :
    (∫ p in {p : ℝ × ℝ | p.1 < p.2},
        q p.1 * q p.2 * Real.sin (K * (p.2 - p.1)) ^ 2
        ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) =
      ((∫ x in a..b, q x) ^ 2 -
        Complex.normSq (∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I))) / 4 := by
  let μ := volume.restrict (Ioc a b)
  let f : ℝ × ℝ → ℝ := fun p => q p.1 * q p.2 * Real.sin (K * (p.2 - p.1)) ^ 2
  have hint : Integrable f (μ.prod μ) := sineSquare_product_integrable hq
  have hsym : ∀ x y, f (x, y) = f (y, x) := by
    intro x y
    dsimp [f]
    have hneg : K * (x - y) = -(K * (y - x)) := by ring
    rw [hneg, Real.sin_neg]
    ring
  have hdiag : ∀ x, f (x, x) = 0 := by intro x; simp [f]
  have htriangle := symmetric_squareIntegral_twice_triangle μ f hint hsym hdiag
  have hsquare := sineSquare_squareIntegral_fourier (K := K) hq
  have hprod : (∫ x in a..b, ∫ y in a..b,
      q x * q y * Real.sin (K * (y - x)) ^ 2) = ∫ p, f p ∂μ.prod μ := by
    simp only [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.integral_integral hint
  rw [hprod, htriangle] at hsquare
  change (∫ p in {p : ℝ × ℝ | p.1 < p.2}, f p ∂μ.prod μ) = _
  linarith

theorem sineSquare_triangleIntegral_capped {q : ℝ → ℝ} {a b K Q : ℝ}
    (hab : a ≤ b) (hK : 0 < K) (hQ : 0 < Q)
    (hlength : b - a ≤ Real.pi / K)
    (hq : IntervalIntegrable q volume a b)
    (hcap : ∀ z ∈ Icc a b, 0 ≤ q z ∧ q z ≤ Q) :
    Q ^ 2 / (4 * K ^ 2) *
      ((K * (∫ z in a..b, q z) / Q) ^ 2 -
        Real.sin (K * (∫ z in a..b, q z) / Q) ^ 2) ≤
      ∫ p in {p : ℝ × ℝ | p.1 < p.2},
        q p.1 * q p.2 * Real.sin (K * (p.2 - p.1)) ^ 2
        ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) := by
  let m : ℝ := ∫ z in a..b, q z
  let M : ℂ := ∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)
  have hb := capped_fourier_moment hab hK hQ hlength hq hcap
  change ‖M‖ ≤ Q / K * Real.sin (K * m / Q) at hb
  have hr : 0 ≤ Q / K * Real.sin (K * m / Q) := (norm_nonneg M).trans hb
  have hs := (sq_le_sq₀ (norm_nonneg M) hr).mpr hb
  rw [← Complex.normSq_eq_norm_sq] at hs
  rw [sineSquare_triangleIntegral_fourier hab hq]
  change Q ^ 2 / (4 * K ^ 2) * ((K * m / Q) ^ 2 - Real.sin (K * m / Q) ^ 2) ≤
    (m ^ 2 - Complex.normSq M) / 4
  have heq : Q ^ 2 / (4 * K ^ 2) *
      ((K * m / Q) ^ 2 - Real.sin (K * m / Q) ^ 2) =
      (m ^ 2 - (Q / K * Real.sin (K * m / Q)) ^ 2) / 4 := by
    field_simp
  rw [heq]
  linarith

#print axioms symmetric_squareIntegral_twice_triangle
#print axioms sineSquare_product_integrable
#print axioms sineSquare_triangleIntegral_fourier
#print axioms sineSquare_triangleIntegral_capped
end OQ7
