import PrescribedExtinction.RadialCalculus

/-! Actual classical derivatives of the Newtonian kernel off the origin.
The distributional contact term remains a separate integration theorem. -/
noncomputable section
namespace OQ7Prescribed

def newtonRadial (r : ℝ) : ℂ := (((4 * Real.pi)⁻¹ * r⁻¹ : ℝ) : ℂ)
def newtonRadialFirst (r : ℝ) : ℂ := ((-(4 * Real.pi)⁻¹ * (r ^ 2)⁻¹ : ℝ) : ℂ)
def newtonRadialSecond (r : ℝ) : ℂ := (((2 * (4 * Real.pi)⁻¹) * (r ^ 3)⁻¹ : ℝ) : ℂ)

theorem outgoingGreen_zero_eq_newton (x : Position) :
    outgoingGreen 0 x = newtonRadial ‖x‖ := by
  simp [outgoingGreen, newtonRadial, div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem newtonRadial_hasDerivAt (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt newtonRadial (newtonRadialFirst r) r := by
  change HasDerivAt (fun y : ℝ => (((4 * Real.pi)⁻¹ * y⁻¹ : ℝ) : ℂ)) _ r
  simpa [newtonRadial, newtonRadialFirst, mul_neg] using
    ((hasDerivAt_inv hr).const_mul (4 * Real.pi)⁻¹).ofReal_comp

theorem newtonRadialFirst_hasDerivAt (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt newtonRadialFirst (newtonRadialSecond r) r := by
  have h := (((hasDerivAt_id r).pow 2).inv (pow_ne_zero 2 hr)).const_mul
    (-(4 * Real.pi)⁻¹)
  convert h.ofReal_comp using 1
  · funext y
    rfl
  · simp only [newtonRadialSecond, Pi.pow_apply, id_eq]
    push_cast
    field_simp

theorem newton_classical_hessian (x : Position) (hx : x ≠ 0) (i j : Fin 3) :
    lineDeriv ℝ (fun y : Position => lineDeriv ℝ (outgoingGreen 0) y (basisR j))
      x (basisR i) =
      (((3 * x i * x j - ‖x‖ ^ 2 * (if i = j then 1 else 0)) /
        (4 * Real.pi * ‖x‖ ^ 5) : ℝ) : ℂ) := by
  have hfun : outgoingGreen 0 = fun y : Position => newtonRadial ‖y‖ :=
    funext outgoingGreen_zero_eq_newton
  rw [hfun, radial_second_lineDeriv newtonRadial newtonRadialFirst newtonRadialSecond
    (fun r hr => newtonRadial_hasDerivAt r hr.ne')
    (fun r hr => newtonRadialFirst_hasDerivAt r hr.ne') x hx i j]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [newtonRadialFirst, newtonRadialSecond, Complex.real_smul]
  push_cast
  split_ifs <;> field_simp <;> ring

end OQ7Prescribed
