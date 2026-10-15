import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! An equal-volume threshold rearrangement theorem. This is a general measure
theorem, not an assumption of the desired Green-kernel norm bound. Applying it
to `f(y)=1/‖x-y‖` and a same-volume ball still requires the exact three-dimensional
ball-volume and Newton-kernel integrals and the continuum Schur test. -/

noncomputable section
namespace QuarticMaxwell
open MeasureTheory Set

/-- A superlevel set maximizes the integral among measurable sets of the same
finite measure, with no smooth-boundary or open-interior hypothesis. -/
theorem threshold_rearrangement {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s b : Set α) (hs : MeasurableSet s) (hb : MeasurableSet b)
    (hsfin : μ s ≠ ⊤) (hbfin : μ b ≠ ⊤) (hvol : μ.real s = μ.real b)
    (f : α → ℝ) (hfs : IntegrableOn f s μ) (hfb : IntegrableOn f b μ)
    (c : ℝ) (hin : ∀ᵐ x ∂μ, x ∈ b → c ≤ f x)
    (hout : ∀ᵐ x ∂μ, x ∉ b → f x ≤ c) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in b, f x ∂μ := by
  have hcs : IntegrableOn (fun _ : α => c) s μ := by
    exact integrableOn_const hsfin
  have hcb : IntegrableOn (fun _ : α => c) b μ := by
    exact integrableOn_const hbfin
  have his : Integrable (s.indicator (fun x => f x - c)) μ :=
    (hfs.sub hcs).integrable_indicator hs
  have hib : Integrable (b.indicator (fun x => f x - c)) μ :=
    (hfb.sub hcb).integrable_indicator hb
  have hpoint : ∀ᵐ x ∂μ, s.indicator (fun y => f y - c) x ≤
      b.indicator (fun y => f y - c) x := by
    filter_upwards [hin, hout] with x hinx houtx
    by_cases hxs : x ∈ s <;> by_cases hxb : x ∈ b
    · simp only [indicator_of_mem hxs, indicator_of_mem hxb]
      exact le_rfl
    · simp only [indicator_of_mem hxs, indicator_of_notMem hxb]
      linarith [houtx hxb]
    · simp only [indicator_of_notMem hxs, indicator_of_mem hxb]
      linarith [hinx hxb]
    · simp only [indicator_of_notMem hxs, indicator_of_notMem hxb]
      exact le_rfl
  have hm := integral_mono_ae his hib hpoint
  rw [integral_indicator hs, integral_indicator hb,
    integral_sub hfs hcs, integral_sub hfb hcb] at hm
  simp only [setIntegral_const, smul_eq_mul] at hm
  rw [hvol] at hm
  linarith

end QuarticMaxwell
