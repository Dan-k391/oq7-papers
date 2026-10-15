import PrescribedExtinction.PlanarDielectricIndex
import PrescribedExtinction.PlanarSlabThickLimit
import PrescribedExtinction.PlanarSlabCoefficients
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The actual weak-loss/thick-slab sequence in the generalized manuscript.
Both loss and thickness vary: a fixed-index thick-slab limit is insufficient.
The exact interface formulas below are the proved Maxwell transfer coefficients. -/

noncomputable section
namespace GeneralizedResearch
namespace DiagonalAbsorber
open OQ7Prescribed Filter
open scoped Topology

def N (m : ℕ) : ℝ := (m : ℝ) + 1
def loss (m : ℕ) : ℝ := 1 / N m
def width (k : ℝ) (m : ℕ) : ℝ := N m ^ 2 / k
def index (m : ℕ) : ℂ := dielectricSlabIndex 1 (loss m)
def propagation (k : ℝ) (m : ℕ) : ℂ := slabPropagation k (index m) (width k m)
def reflection (k : ℝ) (m : ℕ) : ℂ := dielectricSlabReflection k 1 (loss m) (width k m)
def transmission (k : ℝ) (m : ℕ) : ℂ := dielectricSlabTransmission k 1 (loss m) (width k m)
def absorptance (k : ℝ) (m : ℕ) : ℝ := OQ7.absorptanceLeft (reflection k m) (transmission k m)

theorem N_pos (m : ℕ) : 0 < N m := by unfold N; positivity
theorem loss_pos (m : ℕ) : 0 < loss m := one_div_pos.mpr (N_pos m)
theorem width_pos {k : ℝ} (hk : 0 < k) (m : ℕ) : 0 < width k m := by
  exact div_pos (sq_pos_of_pos (N_pos m)) hk

theorem N_tendsto : Tendsto N atTop atTop :=
  tendsto_atTop_mono (fun m => by dsimp [N]; linarith) tendsto_natCast_atTop_atTop
theorem loss_tendsto : Tendsto loss atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
theorem index_tendsto : Tendsto index atTop (𝓝 (1 : ℂ)) := by
  have h := (dielectricSlabIndex_loss_continuous 1 (by norm_num)).continuousAt.tendsto.comp loss_tendsto
  change Tendsto (fun m => dielectricSlabIndex 1 (loss m)) atTop (𝓝 1)
  simpa [Function.comp_def,dielectricSlabIndex] using h
theorem interface_tendsto :
    Tendsto (fun m => slabInterfaceReflection (index m)) atTop (𝓝 (0 : ℂ)) := by
  have h := weakDielectric_interface_continuous.continuousAt.tendsto.comp loss_tendsto
  simpa only [Function.comp_def, index,weakDielectric_interface_at_zero] using h

theorem damping_identity (m : ℕ) :
    N m ^ 2 * (index m).im = N m * (1 / (2 * (index m).re)) := by
  have hr : 0 < (index m).re := dielectricSlabIndex_re_pos 1 (loss m) (by norm_num)
  have hi := congrArg Complex.im (dielectricSlabIndex_sq 1 (loss m))
  change ((index m) ^ 2).im = ((1 : ℂ) + Complex.I * ((loss m : ℝ) : ℂ)).im at hi
  simp only [pow_two, Complex.mul_im, Complex.add_im, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add] at hi
  unfold loss at hi
  field_simp [(N_pos m).ne'] at hi
  field_simp [hr.ne']
  linear_combination (N m) * hi

theorem propagation_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (propagation k) atTop (𝓝 (0 : ℂ)) := by
  have hre := Complex.continuous_re.continuousAt.tendsto.comp index_tendsto
  have hg : Tendsto (fun m => 1 / (2 * (index m).re)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).div
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hre) (by norm_num : (2 : ℝ) * 1 ≠ 0)
    change Tendsto (fun m => 1 / (2 * (index m).re)) atTop (𝓝 (1 / (2 * 1 : ℝ))) at h
    simpa only [mul_one] using h
  have hd : Tendsto (fun m => N m * (1 / (2 * (index m).re))) atTop atTop :=
    N_tendsto.atTop_mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) hg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hd)
  convert he using 1
  funext m
  rw [propagation,slabPropagation_norm]
  congr 1
  unfold width
  rw [show -(k * (index m).im) * (N m ^ 2 / k) = -(N m ^ 2 * (index m).im) by field_simp]
  rw [damping_identity]
  rfl

theorem reflection_formula (k : ℝ) (m : ℕ) :
    reflection k m = slabInterfaceReflection (index m) * (1 - propagation k m ^ 2) /
      (1 - slabInterfaceReflection (index m) ^ 2 * propagation k m ^ 2) := by
  simpa only [reflection, propagation, index, dielectricSlabReflection, OQ7.layerTransfer,
    OQ7.refractiveIndex, OQ7.relativePermittivity, dielectricSlab, dielectricSlabIndex] using
    homogeneousSlabReflection_interface_formula k (width k m) (index m)
      (dielectricSlabIndex_ne_zero 1 (loss m) (by norm_num))
      (dielectricSlabIndex_one_add_ne_zero 1 (loss m) (by norm_num))

theorem transmission_formula (k : ℝ) (m : ℕ) :
    transmission k m = (1 - slabInterfaceReflection (index m) ^ 2) * propagation k m /
      (1 - slabInterfaceReflection (index m) ^ 2 * propagation k m ^ 2) := by
  simpa only [transmission, propagation, index, dielectricSlabTransmission, OQ7.layerTransfer,
    OQ7.refractiveIndex, OQ7.relativePermittivity, dielectricSlab, dielectricSlabIndex] using
    homogeneousSlabTransmission_interface_formula k (width k m) (index m)
      (dielectricSlabIndex_ne_zero 1 (loss m) (by norm_num))
      (dielectricSlabIndex_one_add_ne_zero 1 (loss m) (by norm_num))

theorem reflection_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (reflection k) atTop (𝓝 (0 : ℂ)) := by
  change Tendsto (fun m => reflection k m) atTop (𝓝 (0 : ℂ))
  simp_rw [reflection_formula]
  have hp := propagation_tendsto hk
  have hr := interface_tendsto
  have h : Tendsto (fun m => slabInterfaceReflection (index m) * (1 - propagation k m ^ 2) /
      (1 - slabInterfaceReflection (index m) ^ 2 * propagation k m ^ 2)) atTop
      (𝓝 ((0 : ℂ) * (1 - 0 ^ 2) / (1 - 0 ^ 2 * 0 ^ 2))) :=
    (hr.mul (tendsto_const_nhds.sub (hp.pow 2))).div
      (tendsto_const_nhds.sub ((hr.pow 2).mul (hp.pow 2))) (by norm_num)
  simpa using h

theorem transmission_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (transmission k) atTop (𝓝 (0 : ℂ)) := by
  change Tendsto (fun m => transmission k m) atTop (𝓝 (0 : ℂ))
  simp_rw [transmission_formula]
  have hp := propagation_tendsto hk
  have hr := interface_tendsto
  have h : Tendsto (fun m => (1 - slabInterfaceReflection (index m) ^ 2) * propagation k m /
      (1 - slabInterfaceReflection (index m) ^ 2 * propagation k m ^ 2)) atTop
      (𝓝 ((1 - (0 : ℂ) ^ 2) * 0 / (1 - 0 ^ 2 * 0 ^ 2))) :=
    ((tendsto_const_nhds.sub (hr.pow 2)).mul hp).div
      (tendsto_const_nhds.sub ((hr.pow 2).mul (hp.pow 2))) (by norm_num)
  simpa using h

theorem absorptance_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (absorptance k) atTop (𝓝 (1 : ℝ)) := by
  have hr := Complex.continuous_normSq.continuousAt.tendsto.comp (reflection_tendsto hk)
  have ht := Complex.continuous_normSq.continuousAt.tendsto.comp (transmission_tendsto hk)
  change Tendsto (fun m => 1 - Complex.normSq (reflection k m) - Complex.normSq (transmission k m)) atTop (𝓝 1)
  simpa using (tendsto_const_nhds.sub hr).sub ht

theorem loss_eventually_below {Q : ℝ} (hQ : 0 < Q) : ∀ᶠ m in atTop, loss m < Q :=
  loss_tendsto.eventually_lt_const hQ

theorem integrated_loss {k : ℝ} (hk : k ≠ 0) (m : ℕ) :
    loss m * width k m = N m / k := by
  unfold loss width
  field_simp [(N_pos m).ne']

end DiagonalAbsorber
end GeneralizedResearch
