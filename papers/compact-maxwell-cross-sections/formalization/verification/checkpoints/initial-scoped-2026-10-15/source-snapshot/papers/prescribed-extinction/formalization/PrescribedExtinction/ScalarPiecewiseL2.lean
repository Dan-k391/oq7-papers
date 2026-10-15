import PrescribedExtinction.SetSupportedL2

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical
variable {α : Type*} [MeasurableSpace α]

def scalarIndicatorCLM (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (setSupportedL2 (E := ℂ) μ s).subtypeL ∘L setRestrictionCLM μ s hs

def scalarPiecewiseL2 (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (a b : ℂ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  a • scalarIndicatorCLM μ s hs + b • (ContinuousLinearMap.id ℂ _ - scalarIndicatorCLM μ s hs)

theorem scalarPiecewiseL2_coe (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (a b : ℂ)
    (f : Lp ℂ 2 μ) : scalarPiecewiseL2 μ s hs a b f =ᵐ[μ]
      fun x => if x ∈ s then a * f x else b * f x := by
  let g := indicatorL2 μ s hs f
  filter_upwards [Lp.coeFn_add (a • g) (b • (f - g)), Lp.coeFn_smul a g,
    Lp.coeFn_smul b (f - g), Lp.coeFn_sub f g, indicatorL2_coe μ s hs f] with x ha h1 h2 hd hg
  change (a • g + b • (f - g)) x = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [h1, h2]
  change a * g x + b * (f - g) x = _
  rw [hd]
  change a * g x + b * (f x - g x) = _
  rw [hg]
  by_cases hx : x ∈ s <;> simp [hx]

theorem scalarPiecewiseL2_norm_le (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (f : Lp ℂ 2 μ) :
    ‖scalarPiecewiseL2 μ s hs a b f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [scalarPiecewiseL2_coe μ s hs a b f] with x hx
  rw [hx]
  split_ifs <;> rw [norm_mul]
  · exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_eq (one_mul _)
  · exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

end OQ7Prescribed

