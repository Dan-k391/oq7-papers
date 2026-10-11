import PrescribedExtinction.Maxwell

/-! Audit of the smooth-test correction. In this Mathlib, the untyped top
regularity is analytic (omega), whereas the coerced ENat top is smooth
(infinity). The corrected weak curl quantifies over all smooth compact vector
tests and implies the original, weaker analytic-test condition. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

/-- The exact weak-curl test condition used before the smoothness correction. -/
def AnalyticTestWeakCurl (F G : Field) : Prop :=
  ∀ φ : Field, ContDiff ℝ ⊤ φ → HasCompactSupport φ →
    (∫ x : Position, bilinear (F x) (curl φ x)) =
      ∫ x : Position, bilinear (G x) (φ x)

/-- The physical smooth-test correction strengthens the old encoding. -/
theorem HasWeakCurl.implies_analyticTestWeakCurl (F G : Field)
    (h : HasWeakCurl F G) : AnalyticTestWeakCurl F G := by
  intro φ hc hs
  exact h φ (hc.of_le le_top) hs

/-- Every order of finite differentiability is included in the smooth test
condition. This declaration also exposes the exact regularity type to audit. -/
theorem weakCurlTest_all_finite_orders (φ : Field)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) : ContDiff ℝ n φ :=
  hφ.of_le (by exact_mod_cast le_top)

end OQ7Prescribed
