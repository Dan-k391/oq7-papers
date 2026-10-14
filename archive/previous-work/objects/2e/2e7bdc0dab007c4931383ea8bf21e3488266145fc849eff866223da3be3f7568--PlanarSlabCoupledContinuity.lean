import work.PlanarSlabParameterContinuity
import PrescribedExtinction.PlanarSlabCoupledFields
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed

theorem slabFeedback_loss_angle_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ : X → ℝ) (hq : Continuous q) (hθ : Continuous θ) :
    Continuous (fun x => slabFeedback k A (dielectricSlab p (q x) d) (θ x)) := by
  have hr := (dielectricSlabReflection_loss_continuous k hk p d hp hd).comp hq
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)
  exact continuous_const.sub ((continuous_const.mul hr).mul (hc.pow 2))

theorem slabAbsorberAmplitude_loss_angle_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ : X → ℝ) (hq : Continuous q) (hθ : Continuous θ) (σ : Direction) :
    Continuous (fun x => slabAbsorberAmplitude k A (dielectricSlab p (q x) d) (θ x) σ) := by
  have hr := (dielectricSlabReflection_loss_continuous k hk p d hp hd).comp hq
  have ht := (dielectricSlabTransmission_loss_continuous k hk p d hp hd).comp hq
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)
  have hD := slabFeedback_loss_angle_continuous k hk A p d hp hd q θ hq hθ
  have hne (x : X) : slabFeedback k A (dielectricSlab p (q x) d) (θ x) ≠ 0 :=
    slabFeedback_ne_zero k hk A _ hpA hqA hdA hp (q x).property hd (θ x)
  cases σ
  · change Continuous (fun x => (Real.cos (θ x) : ℂ) * dielectricSlabReflection k p (q x) d *
      (apertureOscillation k A.width / slabFeedback k A (dielectricSlab p (q x) d) (θ x)))
    exact (hc.mul hr).mul (continuous_const.div hD hne)
  · change Continuous (fun x => (Real.cos (θ x) : ℂ) *
      (dielectricSlabTransmission k p (q x) d - apertureOscillation k d) *
      apertureOscillation (-k) (A.width + d) / slabFeedback k A (dielectricSlab p (q x) d) (θ x))
    exact ((hc.mul (ht.sub continuous_const)).mul continuous_const).div hD hne

theorem slabPlateLeftAmplitude_loss_angle_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ : X → ℝ) (hq : Continuous q) (hθ : Continuous θ) (σ : Direction) :
    Continuous (fun x => slabPlateLeftAmplitude k A (dielectricSlab p (q x) d) (θ x) σ) := by
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)
  cases σ
  · exact continuous_const.div (slabFeedback_loss_angle_continuous k hk A p d hp hd q θ hq hθ)
      (fun x => slabFeedback_ne_zero k hk A _ hpA hqA hdA hp (q x).property hd (θ x))
  · exact (hc.mul continuous_const).mul
      (slabAbsorberAmplitude_loss_angle_continuous k hk A hpA hqA hdA p d hp hd q θ hq hθ .minus)

theorem dielectricSlabLeftAt_loss_position_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (p a b : ℝ) (hp : 1 ≤ p) (hab : a ≤ b)
    (q : X → NonnegativeSlabLoss) (z : X → ℝ) (hq : Continuous q) (hz : Continuous z) :
    Continuous (fun x => (dielectricSlabLeftAt k p (q x) a b hp).electric (z x)) := by
  have hn := (dielectricSlabIndex_loss_continuous p (by linarith)).comp (continuous_subtype_val.comp hq)
  have hr := (dielectricSlabReflection_loss_continuous k hk p (b - a) hp (sub_nonneg.mpr hab)).comp hq
  exact homogeneousElectricField_parameter_continuous k _ _ _ _ hn
    (continuous_const.add hr) (continuous_const.sub hr) (hz.sub continuous_const)
    (fun x => dielectricSlabIndex_ne_zero p (q x) (by linarith))

theorem dielectricSlabRightAt_loss_position_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (p a b : ℝ) (hp : 1 ≤ p) (hab : a ≤ b)
    (q : X → NonnegativeSlabLoss) (z : X → ℝ) (hq : Continuous q) (hz : Continuous z) :
    Continuous (fun x => (dielectricSlabRightAt k p (q x) a b hp).electric (z x)) :=
  dielectricSlabLeftAt_loss_position_continuous k hk p a b hp hab q _ hq (continuous_const.sub hz)

theorem slabCoupledPlate_loss_angle_position_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ z : X → ℝ)
    (hq : Continuous q) (hθ : Continuous θ) (hz : Continuous z) (σ : Direction) :
    Continuous (fun x => (slabCoupledPlate k A (dielectricSlab p (q x) d) (θ x) σ hp).electric (z x)) := by
  have hl := dielectricSlabLeftAt_loss_position_continuous k hk p A.width (A.width + d) hp (by linarith) q z hq hz
  have hr := dielectricSlabRightAt_loss_position_continuous k hk p A.width (A.width + d) hp (by linarith) q z hq hz
  have hrr : Continuous (fun x => slabPlateRightAmplitude k A (dielectricSlab p (q x) d) σ) := by
    cases σ
    · change Continuous (fun _ : X => (0 : ℂ))
      exact continuous_const
    · change Continuous (fun _ : X => apertureOscillation (-k) (A.width + d))
      exact continuous_const
  exact ((slabPlateLeftAmplitude_loss_angle_continuous k hk A hpA hqA hdA p d hp hd q θ hq hθ σ).mul hl).add
    (hrr.mul hr)

theorem slabCoupledAbsorber_loss_angle_position_continuous {X : Type*} [TopologicalSpace X]
    (k : ℝ) (hk : 0 < k) (A : OQ7.HomogeneousLayer) (hpA : 1 ≤ A.p)
    (hqA : 0 ≤ A.q) (hdA : 0 ≤ A.width) (p d : ℝ) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (q : X → NonnegativeSlabLoss) (θ z : X → ℝ)
    (hq : Continuous q) (hθ : Continuous θ) (hz : Continuous z) (σ : Direction) :
    Continuous (fun x => (slabCoupledAbsorber k A (dielectricSlab p (q x) d) (θ x) σ hpA).electric (z x)) := by
  have hr := dielectricSlabRightAt_loss_position_continuous k hk A.p 0 A.width hpA hdA
    (fun _ : X => (⟨A.q, hqA⟩ : NonnegativeSlabLoss)) z continuous_const hz
  exact (slabAbsorberAmplitude_loss_angle_continuous k hk A hpA hqA hdA p d hp hd q θ hq hθ σ).mul hr

end OQ7Prescribed
