import PrescribedExtinction.PlanarSlabAbsorptionWork
import PrescribedExtinction.PlanarSlabExtinctionIntegral
import PrescribedExtinction.PlanarSlabCoupledContinuity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

def slabIntegralAbsorption (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction)
    (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p) : ℝ :=
  k * (A.q * (∫ z in (0 : ℝ)..A.width, Complex.normSq ((slabCoupledAbsorber k A W θ σ hpA).electric z)) +
    W.q * (∫ z in A.width..(A.width + W.width), Complex.normSq ((slabCoupledPlate k A W θ σ hpW).electric z)))

def slabFormulaExtinction (k : ℝ) (A W : OQ7.HomogeneousLayer) (θ : ℝ) : ℝ :=
  2 * ((1 - apertureOscillation (-k) W.width * dielectricSlabTransmission k W.p W.q W.width) /
    slabFeedback k A W θ).re

theorem planarNormalizedAbsorption_eq_slabIntegral (k : ℝ) (hk : 0 < k)
    (A W : OQ7.HomogeneousLayer) (θ : ℝ) (σ : Direction) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 < A.q) (hqW : 0 < W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) :
    planarNormalizedAbsorption k hk σ (A.width + W.width) (by linarith) A.width θ
      (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
      (by simpa only [relativePermittivity_susceptibility_im] using hqA)
      (by simpa only [relativePermittivity_susceptibility_im] using hqW) =
      slabIntegralAbsorption k A W θ σ hpA hpW := by
  unfold planarNormalizedAbsorption
  rw [← slabCoupledCurrent_eq_planarNormalizedResponse k hk A W θ σ hpA hpW hqA hqW hdA hdW,
    slabCoupledCurrent_absorption_integral k A W θ σ hpA hpW hdA hdW
      (relativePermittivity_susceptibility_ne_zero A hqA) (relativePermittivity_susceptibility_ne_zero W hqW)]
  rfl

theorem planarNormalizedExtinction_plus_eq_slabFormula (k : ℝ) (hk : 0 < k)
    (A W : OQ7.HomogeneousLayer) (θ : ℝ) (hpA : 1 ≤ A.p) (hpW : 1 ≤ W.p)
    (hqA : 0 < A.q) (hqW : 0 < W.q) (hdA : 0 ≤ A.width) (hdW : 0 ≤ W.width) :
    planarNormalizedExtinction k hk .plus (A.width + W.width) (by linarith) A.width θ
      (OQ7.relativePermittivity A - 1) (OQ7.relativePermittivity W - 1)
      (by simpa only [relativePermittivity_susceptibility_im] using hqA)
      (by simpa only [relativePermittivity_susceptibility_im] using hqW) =
      slabFormulaExtinction k A W θ := by
  have hm := slabCoupledPlate_plus_weighted_moment k hk A W θ hpW hqW.le hdW
  rw [← slabCoupledCurrent_plus_drive_inner k A W θ hpA hpW hdA hdW] at hm
  have halg : 2 * slabPlusPlateAmplitude k A W θ *
      (apertureOscillation (-k) (A.width + W.width) * dielectricSlabTransmission k W.p W.q W.width -
        apertureOscillation (-k) A.width) =
      -2 * ((1 - apertureOscillation (-k) W.width * dielectricSlabTransmission k W.p W.q W.width) /
        slabFeedback k A W θ) := by
    unfold slabPlusPlateAmplitude
    rw [apertureOscillation_add]
    calc
      _ = 2 * (apertureOscillation k A.width * apertureOscillation (-k) A.width) *
          (apertureOscillation (-k) W.width * dielectricSlabTransmission k W.p W.q W.width - 1) /
          slabFeedback k A W θ := by ring
      _ = _ := by rw [apertureOscillation_opposite_mul]; ring
  rw [halg] at hm
  have hr := congrArg Complex.re hm
  norm_num [Complex.mul_re, Complex.mul_im] at hr
  unfold planarNormalizedExtinction slabFormulaExtinction
  rw [← slabCoupledCurrent_eq_planarNormalizedResponse k hk A W θ .plus hpA hpW hqA hqW hdA hdW]
  exact hr

theorem slabFormulaExtinction_loss_angle_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ : X → ℝ) (hq : Continuous q) (hθ : Continuous θ) :
    Continuous (fun x => slabFormulaExtinction k A (dielectricSlab p (q x) d) (θ x)) := by
  have ht := (dielectricSlabTransmission_loss_continuous k hk p d hp hd).comp hq
  have hD := slabFeedback_loss_angle_continuous k hk A p d hp hd q θ hq hθ
  change Continuous (fun x => 2 * ((1 - apertureOscillation (-k) d * dielectricSlabTransmission k p (q x) d) /
    slabFeedback k A (dielectricSlab p (q x) d) (θ x)).re)
  have hnum : Continuous (fun x => (1 : ℂ) - apertureOscillation (-k) d * dielectricSlabTransmission k p (q x) d) :=
    continuous_const.sub (continuous_const.mul ht)
  exact continuous_const.mul (Complex.continuous_re.comp
    (hnum.div hD
      (fun x => slabFeedback_ne_zero k hk A _ hpA hqA hdA hp (q x).property hd (θ x))))

theorem slabIntegralAbsorption_loss_angle_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ : X → ℝ) (hq : Continuous q) (hθ : Continuous θ) (σ : Direction) :
    Continuous (fun x => slabIntegralAbsorption k A (dielectricSlab p (q x) d) (θ x) σ hpA hp) := by
  have hEA := slabCoupledAbsorber_loss_angle_position_continuous k hk A hpA hqA hdA p d hp hd
    (fun x : X × ℝ => q x.1) (fun x : X × ℝ => θ x.1) (fun x : X × ℝ => x.2)
    (hq.comp continuous_fst) (hθ.comp continuous_fst) continuous_snd σ
  have hEW := slabCoupledPlate_loss_angle_position_continuous k hk A hpA hqA hdA p d hp hd
    (fun x : X × ℝ => q x.1) (fun x : X × ℝ => θ x.1) (fun x : X × ℝ => x.2)
    (hq.comp continuous_fst) (hθ.comp continuous_fst) continuous_snd σ
  have hIA : Continuous (fun x => ∫ z in (0 : ℝ)..A.width, Complex.normSq
      ((slabCoupledAbsorber k A (dielectricSlab p (q x) d) (θ x) σ hpA).electric z)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x z => Complex.normSq ((slabCoupledAbsorber k A (dielectricSlab p (q x) d) (θ x) σ hpA).electric z))
    (Complex.continuous_normSq.comp hEA) 0 A.width
  have hIW : Continuous (fun x => ∫ z in A.width..(A.width + d), Complex.normSq
      ((slabCoupledPlate k A (dielectricSlab p (q x) d) (θ x) σ hp).electric z)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x z => Complex.normSq ((slabCoupledPlate k A (dielectricSlab p (q x) d) (θ x) σ hp).electric z))
    (Complex.continuous_normSq.comp hEW) A.width (A.width + d)
  change Continuous (fun x => k * (A.q * _ + (q x : ℝ) * _))
  exact continuous_const.mul ((continuous_const.mul hIA).add ((continuous_subtype_val.comp hq).mul hIW))

end OQ7Prescribed
