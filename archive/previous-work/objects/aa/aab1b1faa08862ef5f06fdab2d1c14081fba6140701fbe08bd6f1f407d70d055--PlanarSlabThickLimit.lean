import work.PlanarSlabExponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Complex.Norm

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Filter
open scoped Topology

theorem slabPropagation_norm (k : ℝ) (n : ℂ) (d : ℝ) :
    ‖slabPropagation k n d‖ = Real.exp (-(k * n.im) * d) := by
  rw [slabPropagation, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem slabPropagation_tendsto_zero (k : ℝ) (hk : 0 < k) (n : ℂ) (hnim : 0 < n.im) :
    Tendsto (slabPropagation k n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [slabPropagation_norm]
  exact Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos (mul_pos hk hnim))).mpr tendsto_id)

theorem homogeneousSlabReflection_thick_limit (k : ℝ) (hk : 0 < k) (n : ℂ)
    (hn : n ≠ 0) (hnp : 1 + n ≠ 0) (hnim : 0 < n.im) :
    Tendsto (fun d : ℝ => OQ7.transferReflectionLeft (OQ7.waveTransfer (OQ7.homogeneousTransfer k n d)))
      atTop (𝓝 (slabInterfaceReflection n)) := by
  have hp := slabPropagation_tendsto_zero k hk n hnim
  have hp2 : Tendsto (fun d => slabPropagation k n d ^ 2) atTop (𝓝 (0 : ℂ)) := by
    simpa using hp.pow 2
  have hnum : Tendsto (fun d => slabInterfaceReflection n * (1 - slabPropagation k n d ^ 2))
      atTop (𝓝 (slabInterfaceReflection n)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => slabInterfaceReflection n) atTop (𝓝 (slabInterfaceReflection n))).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1)).sub hp2)
    convert h using 1 <;> first | rfl | simp
  have hden : Tendsto (fun d => 1 - slabInterfaceReflection n ^ 2 * slabPropagation k n d ^ 2)
      atTop (𝓝 (1 : ℂ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hp2)
  have hlim := hnum.div hden (by norm_num)
  simp_rw [homogeneousSlabReflection_interface_formula k _ n hn hnp]
  convert hlim using 1 <;> first | rfl | simp

theorem homogeneousSlabTransmission_thick_limit (k : ℝ) (hk : 0 < k) (n : ℂ)
    (hn : n ≠ 0) (hnp : 1 + n ≠ 0) (hnim : 0 < n.im) :
    Tendsto (fun d : ℝ => OQ7.transferTransmissionRight (OQ7.waveTransfer (OQ7.homogeneousTransfer k n d)))
      atTop (𝓝 (0 : ℂ)) := by
  have hp := slabPropagation_tendsto_zero k hk n hnim
  have hp2 : Tendsto (fun d => slabPropagation k n d ^ 2) atTop (𝓝 (0 : ℂ)) := by
    simpa using hp.pow 2
  have hnum : Tendsto (fun d => (1 - slabInterfaceReflection n ^ 2) * slabPropagation k n d)
      atTop (𝓝 (0 : ℂ)) := by
    simpa using tendsto_const_nhds.mul hp
  have hden : Tendsto (fun d => 1 - slabInterfaceReflection n ^ 2 * slabPropagation k n d ^ 2)
      atTop (𝓝 (1 : ℂ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hp2)
  have hlim := hnum.div hden (by norm_num)
  simp_rw [homogeneousSlabTransmission_interface_formula k _ n hn hnp]
  convert hlim using 1 <;> first | rfl | simp

theorem homogeneousSlabAbsorptance_thick_limit (k : ℝ) (hk : 0 < k) (n : ℂ)
    (hn : n ≠ 0) (hnp : 1 + n ≠ 0) (hnim : 0 < n.im) :
    Tendsto (fun d : ℝ => OQ7.absorptanceLeft
        (OQ7.transferReflectionLeft (OQ7.waveTransfer (OQ7.homogeneousTransfer k n d)))
        (OQ7.transferTransmissionRight (OQ7.waveTransfer (OQ7.homogeneousTransfer k n d))))
      atTop (𝓝 (1 - Complex.normSq (slabInterfaceReflection n))) := by
  have hr := Complex.continuous_normSq.continuousAt.tendsto.comp
    (homogeneousSlabReflection_thick_limit k hk n hn hnp hnim)
  have ht := Complex.continuous_normSq.continuousAt.tendsto.comp
    (homogeneousSlabTransmission_thick_limit k hk n hn hnp hnim)
  simpa [OQ7.absorptanceLeft] using (tendsto_const_nhds.sub hr).sub ht

end OQ7Prescribed
