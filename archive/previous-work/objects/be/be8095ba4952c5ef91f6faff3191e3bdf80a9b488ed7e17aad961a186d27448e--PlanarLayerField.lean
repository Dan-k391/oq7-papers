import work.PlanarGreenBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

structure PlanarLayerField (k a b : ℝ) where
  electric : ℝ → ℂ
  magnetic : ℝ → ℂ
  current : ℝ → ℂ
  electric_continuous : ContinuousOn electric (Icc a b)
  magnetic_continuous : ContinuousOn magnetic (Icc a b)
  current_continuous : ContinuousOn current (Icc a b)
  electric_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt electric (Complex.I * (k : ℂ) * magnetic t) t
  magnetic_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt magnetic (Complex.I * (k : ℂ) * (electric t + current t)) t

def homogeneousPlanarLayerField (k a b z₀ : ℝ) (n : ℂ) (hn : n ≠ 0) (E₀ H₀ : ℂ) :
    PlanarLayerField k a b := by
  let E := fun t : ℝ => OQ7.electricField k n E₀ H₀ (t - z₀)
  let H := fun t : ℝ => OQ7.magneticField k n E₀ H₀ (t - z₀)
  have hE (t : ℝ) : HasDerivAt E (Complex.I * (k : ℂ) * H t) t := by
    convert (OQ7.electricField_hasDerivAt k hn E₀ H₀ (t - z₀)).scomp t
      ((hasDerivAt_id t).sub_const z₀) using 1 <;> simp [E, H, Function.comp_def]
  have hH (t : ℝ) : HasDerivAt H (Complex.I * (k : ℂ) * n ^ 2 * E t) t := by
    convert (OQ7.magneticField_hasDerivAt k hn E₀ H₀ (t - z₀)).scomp t
      ((hasDerivAt_id t).sub_const z₀) using 1 <;> simp [E, H, Function.comp_def]
  have hEc : Continuous E := continuous_iff_continuousAt.mpr fun t => (hE t).continuousAt
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun t => (hH t).continuousAt
  refine ⟨E, H, fun t => (n ^ 2 - 1) * E t, hEc.continuousOn, hHc.continuousOn,
    (continuous_const.mul hEc).continuousOn, fun t _ => hE t, ?_⟩
  intro t _
  convert hH t using 1
  ring

def PlanarLayerField.add {k a b : ℝ} (F G : PlanarLayerField k a b) : PlanarLayerField k a b where
  electric := fun t => F.electric t + G.electric t
  magnetic := fun t => F.magnetic t + G.magnetic t
  current := fun t => F.current t + G.current t
  electric_continuous := F.electric_continuous.add G.electric_continuous
  magnetic_continuous := F.magnetic_continuous.add G.magnetic_continuous
  current_continuous := F.current_continuous.add G.current_continuous
  electric_derivative t ht := by
    convert (F.electric_derivative t ht).add (G.electric_derivative t ht) using 1
    ring
  magnetic_derivative t ht := by
    convert (F.magnetic_derivative t ht).add (G.magnetic_derivative t ht) using 1
    ring

def PlanarLayerField.const_mul {k a b : ℝ} (c : ℂ) (F : PlanarLayerField k a b) :
    PlanarLayerField k a b where
  electric := fun t => c * F.electric t
  magnetic := fun t => c * F.magnetic t
  current := fun t => c * F.current t
  electric_continuous := F.electric_continuous.const_mul c
  magnetic_continuous := F.magnetic_continuous.const_mul c
  current_continuous := F.current_continuous.const_mul c
  electric_derivative t ht := by
    convert (F.electric_derivative t ht).const_mul c using 1
    ring
  magnetic_derivative t ht := by
    convert (F.magnetic_derivative t ht).const_mul c using 1
    ring

end OQ7Prescribed
