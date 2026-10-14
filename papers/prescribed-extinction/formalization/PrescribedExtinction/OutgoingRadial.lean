import PrescribedExtinction.NewtonKernel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Classical derivatives of the actual outgoing scalar kernel off zero.
Distributional extension across the origin is not assumed. -/
noncomputable section
namespace OQ7Prescribed

def outgoingRadial (k r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (k : ℂ) * (r : ℂ)) / ((4 * Real.pi : ℝ) : ℂ) / (r : ℂ)

def outgoingRadialFirst (k r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (k : ℂ) * (r : ℂ)) *
    (Complex.I * (k : ℂ) * (r : ℂ) - 1) /
      (((4 * Real.pi : ℝ) : ℂ) * (r : ℂ) ^ 2)

def outgoingRadialSecond (k r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (k : ℂ) * (r : ℂ)) *
    ((Complex.I * (k : ℂ) * (r : ℂ)) ^ 2 -
      2 * (Complex.I * (k : ℂ) * (r : ℂ)) + 2) /
        (((4 * Real.pi : ℝ) : ℂ) * (r : ℂ) ^ 3)

theorem outgoingGreen_eq_radial (k : ℝ) (x : Position) :
    outgoingGreen k x = outgoingRadial k ‖x‖ := by
  simp only [outgoingGreen, outgoingRadial, Complex.ofReal_mul,
    mul_assoc, div_mul_eq_div_div]

theorem outgoingRadial_hasDerivAt (k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (outgoingRadial k) (outgoingRadialFirst k r) r := by
  have hid := (hasDerivAt_id r).ofReal_comp
  have he := (hid.const_mul (Complex.I * (k : ℂ))).cexp
  have h := (he.div_const (((4 * Real.pi : ℝ) : ℂ))).div hid
    (Complex.ofReal_ne_zero.mpr hr)
  convert h using 1
  · funext y
    rfl
  · unfold outgoingRadialFirst
    simp only [id_eq, Complex.ofReal_one, mul_one]
    field_simp

theorem outgoingRadialFirst_hasDerivAt (k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (outgoingRadialFirst k) (outgoingRadialSecond k r) r := by
  have hid := (hasDerivAt_id r).ofReal_comp
  have he := (hid.const_mul (Complex.I * (k : ℂ))).cexp
  have hn := he.mul ((hid.const_mul (Complex.I * (k : ℂ))).sub_const 1)
  have h := hn.div ((hid.pow 2).const_mul (((4 * Real.pi : ℝ) : ℂ)))
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr)))
  convert h using 1
  · funext y
    rfl
  · unfold outgoingRadialSecond
    simp only [id_eq, Complex.ofReal_one, mul_one, Nat.cast_ofNat,
      Pi.pow_apply, Pi.mul_apply, Nat.reduceSub, pow_one]
    field_simp
    ring

theorem outgoing_classical_hessian (k : ℝ) (x : Position) (hx : x ≠ 0) (i j : Fin 3) :
    lineDeriv ℝ (fun y : Position => lineDeriv ℝ (outgoingGreen k) y (basisR j))
      x (basisR i) =
      (x i * x j / ‖x‖ ^ 2) • outgoingRadialSecond k ‖x‖ +
        ((if i = j then 1 else 0) / ‖x‖ - x i * x j / ‖x‖ ^ 3) •
          outgoingRadialFirst k ‖x‖ := by
  have hfun : outgoingGreen k = fun y : Position => outgoingRadial k ‖y‖ :=
    funext (outgoingGreen_eq_radial k)
  rw [hfun]
  exact radial_second_lineDeriv (outgoingRadial k) (outgoingRadialFirst k)
    (outgoingRadialSecond k) (fun r hr => outgoingRadial_hasDerivAt k r hr.ne')
    (fun r hr => outgoingRadialFirst_hasDerivAt k r hr.ne') x hx i j

end OQ7Prescribed
