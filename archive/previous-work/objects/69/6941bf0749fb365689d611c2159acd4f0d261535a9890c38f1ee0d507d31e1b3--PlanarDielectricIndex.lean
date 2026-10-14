import work.PlanarSlabExponential
import Mathlib.Analysis.Complex.SqrtDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Filter
open scoped Topology

def dielectricSlabIndex (p q : ℝ) : ℂ := Complex.sqrt ((p : ℂ) + Complex.I * (q : ℂ))

theorem dielectricSlabIndex_sq (p q : ℝ) :
    dielectricSlabIndex p q ^ 2 = (p : ℂ) + Complex.I * (q : ℂ) := by
  simp [dielectricSlabIndex, Complex.sqrt]

theorem dielectricSlabIndex_re_pos (p q : ℝ) (hp : 0 < p) : 0 < (dielectricSlabIndex p q).re := by
  unfold dielectricSlabIndex
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, add_zero]
  split_ifs <;> simp [Complex.mul_re, Complex.mul_im] <;> positivity

theorem dielectricSlabIndex_im_pos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 < (dielectricSlabIndex p q).im := by
  have hr := dielectricSlabIndex_re_pos p q hp
  have hi := congrArg Complex.im (dielectricSlabIndex_sq p q)
  simp only [pow_two, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at hi
  by_contra hn
  have him : (dielectricSlabIndex p q).im ≤ 0 := le_of_not_gt hn
  nlinarith

theorem dielectricSlabIndex_ne_zero (p q : ℝ) (hp : 0 < p) : dielectricSlabIndex p q ≠ 0 := by
  intro hz
  have hr := dielectricSlabIndex_re_pos p q hp
  rw [hz, Complex.zero_re] at hr
  exact lt_irrefl _ hr

theorem dielectricSlabIndex_one_add_ne_zero (p q : ℝ) (hp : 0 < p) : 1 + dielectricSlabIndex p q ≠ 0 := by
  intro hz
  have hr := dielectricSlabIndex_re_pos p q hp
  have he := congrArg Complex.re hz
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
  linarith

theorem dielectricSlabIndex_loss_continuous (p : ℝ) (hp : 0 < p) :
    Continuous (dielectricSlabIndex p) := by
  have hc : Continuous (fun q : ℝ => (p : ℂ) + Complex.I * (q : ℂ)) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (Complex.continuousAt_sqrt (Or.inl (by simpa using hp.le))).comp hc.continuousAt

theorem weakDielectric_interface_continuous :
    Continuous (fun η : ℝ => slabInterfaceReflection (dielectricSlabIndex 1 η)) := by
  have hn := dielectricSlabIndex_loss_continuous 1 (by norm_num)
  exact (continuous_const.sub hn).div (continuous_const.add hn)
    (fun η => dielectricSlabIndex_one_add_ne_zero 1 η (by norm_num))

theorem weakDielectric_interface_at_zero : slabInterfaceReflection (dielectricSlabIndex 1 0) = 0 := by
  simp [dielectricSlabIndex, slabInterfaceReflection]

theorem exists_weakDielectric_interface_with_loss_cap (Q ε : ℝ) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < Q / 3 ∧ Complex.normSq (slabInterfaceReflection (dielectricSlabIndex 1 η)) < ε := by
  have hf := Complex.continuous_normSq.comp weakDielectric_interface_continuous
  have he : ∀ᶠ η : ℝ in 𝓝 0,
      Complex.normSq (slabInterfaceReflection (dielectricSlabIndex 1 η)) < ε :=
    hf.continuousAt.eventually_lt_const (by simpa only [Function.comp_apply,
      weakDielectric_interface_at_zero, Complex.normSq_zero] using hε)
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp he
  let η := min (r / 2) (Q / 6)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨η, hη, ?_, ?_⟩
  · have hh : η ≤ Q / 6 := min_le_right _ _
    linarith
  · apply he
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hη]
    have hh : η ≤ r / 2 := min_le_left _ _
    linarith

end OQ7Prescribed
