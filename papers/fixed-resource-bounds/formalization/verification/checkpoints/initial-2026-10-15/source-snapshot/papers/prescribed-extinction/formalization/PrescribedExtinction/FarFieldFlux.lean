import PrescribedExtinction.FarFieldCurrent
import PrescribedExtinction.RadiationEnergyBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OQ7Prescribed
open MeasureTheory

theorem real_inner_norm_square_error (u v f : Vector) :
    |(inner ℂ u v).re - ‖f‖ ^ 2| ≤
      ‖u‖ * ‖v - u‖ + (‖u‖ + ‖f‖) * ‖u - f‖ := by
  have he : inner ℂ u v - inner ℂ f f =
      inner ℂ u (v - u) + inner ℂ (u - f) u + inner ℂ f (u - f) := by
    rw [inner_sub_right, inner_sub_left, inner_sub_right]
    ring
  have hf : (inner ℂ f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  rw [← hf, ← Complex.sub_re, he]
  calc
    _ ≤ ‖inner ℂ u (v - u) + inner ℂ (u - f) u + inner ℂ f (u - f)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ u (v - u)‖ + ‖inner ℂ (u - f) u‖ + ‖inner ℂ f (u - f)‖ := norm_add₃_le
    _ ≤ ‖u‖ * ‖v - u‖ + ‖u - f‖ * ‖u‖ + ‖f‖ * ‖u - f‖ := by
      gcongr <;> exact norm_inner_le_norm _ _
    _ = _ := by ring

theorem scaled_pairing_real (a : ℂ) (E C : Vector) :
    (pairing (a • E) (a • C)).re = ‖a‖ ^ 2 * (pairing E C).re := by
  rw [pairing_eq_inner, pairing_eq_inner, inner_smul_left, inner_smul_right]
  have ha : (starRingEnd ℂ) a * a = (‖a‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← mul_assoc, ha]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

def farFieldFluxConstant (k R : ℝ) : ℝ :=
  let b := k ^ 2 / (4 * Real.pi)
  let C := farFieldKernelConstant k R
  (b + C) * radiationKernelConstant k R + (2 * b + C) * C

theorem exterior_poynting_farField_error (k : ℝ) (p : CompactPolarization)
    (x : Position) (hx : 2 * p.radius + 2 ≤ ‖x‖) :
    |‖x‖ ^ 2 * (pairing (exteriorElectric k p x)
      (cross (exteriorMagnetic k p x) (complexify (radialDirection x)))).re -
        ‖compactCurrentFarField k p (radialDirection x)‖ ^ 2| ≤
      farFieldFluxConstant k p.radius / ‖x‖ * (∫ y : Position, ‖p.current y‖) ^ 2 := by
  let a : ℂ := (‖x‖ : ℂ) * Complex.exp (-Complex.I * ((k * ‖x‖ : ℝ) : ℂ))
  let E := a • exteriorElectric k p x
  let H := a • cross (exteriorMagnetic k p x) (complexify (radialDirection x))
  let F := compactCurrentFarField k p (radialDirection x)
  let N := ∫ y : Position, ‖p.current y‖
  let b := k ^ 2 / (4 * Real.pi)
  let C := farFieldKernelConstant k p.radius
  let D := radiationKernelConstant k p.radius
  have hr : 1 ≤ ‖x‖ := by linarith [p.radius_nonneg]
  have ha : ‖a‖ = ‖x‖ := by dsimp [a]; simp [Complex.norm_exp]
  have hN : 0 ≤ N := integral_nonneg (fun y => norm_nonneg (p.current y))
  have hC : 0 ≤ C := by dsimp [C, farFieldKernelConstant, farFieldLowerConstant]; have hR := p.radius_nonneg; positivity
  have hD : 0 ≤ D := by dsimp [D, radiationKernelConstant]; have hR := p.radius_nonneg; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hEF : ‖E - F‖ ≤ C / ‖x‖ * N := exteriorElectric_uniform_farField_error k p x hx
  have hF : ‖F‖ ≤ b * N := compactCurrentFarField_norm_le k p _
    (radialDirection_norm x (norm_pos_iff.mp (by linarith)))
  have hEH : ‖H - E‖ ≤ D / ‖x‖ * N := by
    dsimp [H, E]
    rw [← smul_sub, norm_smul, ha]
    calc
      _ ≤ ‖x‖ * (D / ‖x‖ ^ 2 * N) := mul_le_mul_of_nonneg_left
        (exterior_radiation_integral_norm_le k p x hx) (norm_nonneg x)
      _ = _ := by field_simp
  have hE : ‖E‖ ≤ (b + C) * N := by
    calc
      _ ≤ ‖F‖ + ‖E - F‖ := by simpa [norm_sub_rev] using norm_le_norm_add_norm_sub F E
      _ ≤ b * N + C / ‖x‖ * N := add_le_add hF hEF
      _ ≤ b * N + C * N := add_le_add le_rfl (mul_le_mul_of_nonneg_right (div_le_self hC hr) hN)
      _ = _ := by ring
  have hbound := real_inner_norm_square_error E H F
  have he : (inner ℂ E H).re = ‖x‖ ^ 2 * (pairing (exteriorElectric k p x)
      (cross (exteriorMagnetic k p x) (complexify (radialDirection x)))).re := by
    rw [← pairing_eq_inner]
    exact (scaled_pairing_real a _ _).trans (by rw [ha])
  rw [he] at hbound
  apply hbound.trans
  calc
    _ ≤ ((b + C) * N) * (D / ‖x‖ * N) + (((b + C) * N) + b * N) * (C / ‖x‖ * N) := by
      apply add_le_add
      · exact mul_le_mul hE hEH (norm_nonneg _) (mul_nonneg (add_nonneg hb hC) hN)
      · exact mul_le_mul (add_le_add hE hF) hEF (norm_nonneg _)
          (add_nonneg (mul_nonneg (add_nonneg hb hC) hN) (mul_nonneg hb hN))
    _ = _ := by dsimp [farFieldFluxConstant, b, C, D, N]; ring

end OQ7Prescribed
