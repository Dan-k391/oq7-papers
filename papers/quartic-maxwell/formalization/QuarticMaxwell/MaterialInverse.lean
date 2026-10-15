import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic

/-! A sharp resource bound for the actual inverse of a complex-linear
susceptibility on a Hilbert space. The measurable tensor multiplier construction
is a separate continuum obligation; no Maxwell solution is assumed here. -/

noncomputable section
namespace QuarticMaxwell

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Imaginary coercivity implies a genuine bounded inverse via Lax--Milgram.
This proof follows the same functional-analysis construction used by the
unchanged prescribed-extinction project, with no extra axioms. -/
theorem imaginary_coercive_bijective (A : H →L[ℂ] H) {m : ℝ} (hm : 0 < m)
    (hA : ∀ u, m * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) : Function.Bijective A := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let Ar : H →L[ℝ] H := ((-Complex.I) • A).restrictScalars ℝ
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp Ar
  have hB : IsCoercive B := by
    refine ⟨m, hm, ?_⟩
    intro u
    change m * ‖u‖ * ‖u‖ ≤ inner ℝ ((-Complex.I) • A u) u
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

def materialInverseEquiv (A : H →L[ℂ] H) {m : ℝ} (hm : 0 < m)
    (hA : ∀ u, m * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (imaginary_coercive_bijective A hm hA).injective)
    (LinearMap.range_eq_top.mpr (imaginary_coercive_bijective A hm hA).surjective)

theorem materialInverseEquiv_apply (A : H →L[ℂ] H) {m : ℝ} (hm : 0 < m)
    (hA : ∀ u, m * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) (u : H) :
    materialInverseEquiv A hm hA u = A u := rfl

theorem imaginary_coercive_norm_bound (A : H →L[ℂ] H) {m : ℝ} (hm : 0 < m)
    (hA : ∀ u, m * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) (u : H) :
    m * ‖u‖ ≤ ‖A u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have h := (hA u).trans ((Complex.im_le_norm _).trans (norm_inner_le_norm u (A u)))
  have he : m * ‖u‖ ^ 2 = (m * ‖u‖) * ‖u‖ := by ring
  rw [he, mul_comm ‖u‖ ‖A u‖] at h
  exact (mul_le_mul_iff_left₀ hn).mp h

theorem materialInverseEquiv_norm_le (A : H →L[ℂ] H) {m : ℝ} (hm : 0 < m)
    (hA : ∀ u, m * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) :
    ‖(materialInverseEquiv A hm hA).symm.toContinuousLinearMap‖ ≤ 1 / m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have h := imaginary_coercive_norm_bound A hm hA
    ((materialInverseEquiv A hm hA).symm f)
  rw [← materialInverseEquiv_apply A hm hA,
    ContinuousLinearEquiv.apply_symm_apply] at h
  change ‖(materialInverseEquiv A hm hA).symm f‖ ≤ (1 / m) * ‖f‖
  rw [div_mul_eq_mul_div, one_mul]
  exact (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using h)

/-- The paper's sharp inverse-loss factor `m/M²`, rather than a weakened
`m/(M+1)²` factor, follows from the susceptibility norm cap. -/
theorem inverse_loss_resource_bound (A : H →L[ℂ] H) {m M : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hcap : ‖A‖ ≤ M)
    (hA : ∀ u, m * ‖u‖ ^ 2 ≤ (inner ℂ u (A u)).im) (v : H) :
    m / M ^ 2 * ‖v‖ ^ 2 ≤
      -(inner ℂ v ((materialInverseEquiv A hm hA).symm v)).im := by
  let e := materialInverseEquiv A hm hA
  let u := e.symm v
  have huv : A u = v := by
    rw [← materialInverseEquiv_apply A hm hA]
    exact e.apply_symm_apply v
  have hn : ‖v‖ ≤ M * ‖u‖ := by
    rw [← huv]
    exact (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hcap (norm_nonneg u))
  have hsq : ‖v‖ ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg u]
  have hscale : m / M ^ 2 * ‖v‖ ^ 2 ≤ m * ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    nlinarith
  have hi : (inner ℂ u (A u)).im = -(inner ℂ v u).im := by
    rw [huv]
    exact inner_im_symm (𝕜 := ℂ) u v
  exact hscale.trans (by simpa only [hi] using hA u)

end QuarticMaxwell
