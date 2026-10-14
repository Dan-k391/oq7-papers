import PrescribedExtinction.StaticFourier
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! Complex Hilbert-space invertibility from a positive imaginary coercivity
bound. This is functional analysis infrastructure, not an assumption about
the physical outgoing or material operator. -/
noncomputable section
namespace OQ7Prescribed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complex_imaginary_coercive_bijective (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) : Function.Bijective A := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let Ar : H →L[ℝ] H := ((-Complex.I) • A).restrictScalars ℝ
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp Ar
  have hB : IsCoercive B := by
    refine ⟨c, hc, ?_⟩
    intro u
    change c * ‖u‖ * ‖u‖ ≤ inner ℝ ((-Complex.I) • A u) u
    rw [real_inner_comm, real_inner_eq_re_inner ℂ, inner_smul_right]
    simpa [Complex.mul_re, pow_two, mul_assoc] using hA u
  have he : Function.Bijective Ar := by
    have hid : hB.continuousLinearEquivOfBilin.toContinuousLinearMap = Ar := by
      ext u
      apply (innerSL_inj (𝕜 := ℝ)).mp
      ext v
      exact hB.continuousLinearEquivOfBilin_apply u v
    rw [← hid]
    exact hB.continuousLinearEquivOfBilin.bijective
  constructor
  · intro u v huv
    apply he.injective
    change (-Complex.I) • A u = (-Complex.I) • A v
    rw [huv]
  · intro v
    obtain ⟨u, hu⟩ := he.surjective ((-Complex.I) • v)
    refine ⟨u, ?_⟩
    have h := congrArg (fun w : H => Complex.I • w) hu
    change Complex.I • ((-Complex.I) • A u) = Complex.I • ((-Complex.I) • v) at h
    simpa [smul_smul] using h

theorem complex_imaginary_coercive_norm_bound (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) (u : H) :
    c * ‖u‖ ≤ ‖A u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have h := (hA u).trans ((Complex.im_le_norm _).trans (norm_inner_le_norm u (A u)))
  have he : c * ‖u‖ ^ 2 = (c * ‖u‖) * ‖u‖ := by ring
  rw [he, mul_comm ‖u‖ ‖A u‖] at h
  exact (mul_le_mul_iff_left₀ hn).mp h

def complexImaginaryCoerciveEquiv (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (complex_imaginary_coercive_bijective A c hc hA).injective)
    (LinearMap.range_eq_top.mpr (complex_imaginary_coercive_bijective A c hc hA).surjective)

theorem complexImaginaryCoerciveEquiv_apply (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) (u : H) :
    complexImaginaryCoerciveEquiv A c hc hA u = A u := rfl

theorem complexImaginaryCoerciveEquiv_inverse_norm_le (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) :
    ‖(complexImaginaryCoerciveEquiv A c hc hA).symm.toContinuousLinearMap‖ ≤ 1 / c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have h := complex_imaginary_coercive_norm_bound A c hc hA
    ((complexImaginaryCoerciveEquiv A c hc hA).symm f)
  rw [← complexImaginaryCoerciveEquiv_apply A c hc hA,
    ContinuousLinearEquiv.apply_symm_apply] at h
  change ‖(complexImaginaryCoerciveEquiv A c hc hA).symm f‖ ≤ (1 / c) * ‖f‖
  rw [div_mul_eq_mul_div, one_mul]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)

theorem complexImaginaryCoerciveEquiv_inverse_imaginary_bound
    (A : H →L[ℂ] H) (c : ℝ) (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) (u : H) :
    (c / (‖A‖ + 1) ^ 2) * ‖u‖ ^ 2 ≤
      -(inner ℂ u ((complexImaginaryCoerciveEquiv A c hc hA).symm u)).im := by
  let w := (complexImaginaryCoerciveEquiv A c hc hA).symm u
  have hw : A w = u := by
    rw [← complexImaginaryCoerciveEquiv_apply A c hc hA]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hn : ‖u‖ ≤ (‖A‖ + 1) * ‖w‖ := by
    rw [← hw]
    exact (A.le_opNorm w).trans (by nlinarith [norm_nonneg w])
  have hsq : ‖u‖ ^ 2 ≤ (‖A‖ + 1) ^ 2 * ‖w‖ ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg w, norm_nonneg A]
  have hd : 0 < (‖A‖ + 1) ^ 2 := by positivity
  have hscale : (c / (‖A‖ + 1) ^ 2) * ‖u‖ ^ 2 ≤ c * ‖w‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hi : (inner ℂ w (A w)).im = -(inner ℂ u w).im := by
    rw [hw]
    exact inner_im_symm (𝕜 := ℂ) w u
  exact hscale.trans (by simpa only [hi] using hA w)

end OQ7Prescribed
