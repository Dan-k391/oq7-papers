import PrescribedExtinction.NewtonCutoff

/-! Whole-space integration by parts for the actual Newton kernel regularized
outside a positive-radius puncture. This file does not assume a boundary formula. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

def newtonReal (x : Position) : ℝ := (4 * Real.pi * ‖x‖)⁻¹
def newtonGradient (j : Fin 3) (x : Position) : ℝ :=
  -x j / (4 * Real.pi * ‖x‖ ^ 3)

theorem newtonReal_eq_green (x : Position) : (newtonReal x : ℂ) = outgoingGreen 0 x := by
  simp [outgoingGreen, newtonReal]

theorem newtonReal_contDiffAt (x : Position) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 newtonReal x := by
  exact (contDiffAt_const.mul (contDiffAt_norm ℝ hx)).inv
    (mul_ne_zero (by positivity) (norm_ne_zero_iff.mpr hx))

theorem newtonGradient_contDiffAt (j : Fin 3) (x : Position) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (newtonGradient j) x := by
  have hc : ContDiffAt ℝ 1 (fun y : Position => y j) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Position →L[ℝ] ℝ).contDiff.contDiffAt
  exact hc.neg.div (contDiffAt_const.mul ((contDiffAt_norm ℝ hx).pow 3))
    (mul_ne_zero (by positivity) (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx)))

theorem newtonReal_hasLineDerivAt (j : Fin 3) (x : Position) (hx : x ≠ 0) :
    HasLineDerivAt ℝ newtonReal (newtonGradient j x) x (basisR j) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := ((hasFDerivAt_inv (mul_ne_zero (by positivity) hr)).comp x
    ((radialNorm_hasFDerivAt x hx).const_mul (4 * Real.pi))).hasLineDerivAt (basisR j)
  convert h using 1
  · rfl
  · simp [newtonGradient, real_inner_basis]
    field_simp

theorem newtonGradient_hasLineDerivAt (i j : Fin 3) (x : Position) (hx : x ≠ 0) :
    HasLineDerivAt ℝ (newtonGradient j) (newtonHessianKernel i j x) x (basisR i) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Position →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hn := (hasFDerivAt_inv (mul_ne_zero (by positivity) (pow_ne_zero 3 hr))).comp x
    (((radialNorm_hasFDerivAt x hx).pow 3).const_mul (4 * Real.pi))
  have h := (hc.neg.mul hn).hasLineDerivAt (basisR i)
  convert h using 1
  · funext y
    simp [newtonGradient, div_eq_mul_inv]
  · simp [newtonHessianKernel, basisR, PiLp.inner_apply, RCLike.inner_apply, eq_comm]
    split_ifs <;> field_simp <;> ring

theorem exteriorCutoff_mul_contDiff (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (F : Position → ℝ) (hF : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 F x) :
    ContDiff ℝ 1 (fun x => exteriorCutoff r t x * F x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (show ContDiffAt ℝ 1 (fun _ : Position => (0 : ℝ)) 0 from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simpa using hr)] with y hy
    simp only [exteriorCutoff_zero ht y hy.le, zero_mul]
  · exact (exteriorCutoff_contDiff r t hr ht).contDiffAt.mul (hF x hx)

theorem testPartial_hasLineDerivAt (φ : ScalarTest) (i : Fin 3) (x : Position) :
    HasLineDerivAt ℝ (φ : Position → ℝ) ((testPartial i φ) x) x (basisR i) := by
  have h := (φ.contDiff.differentiable (by simp) x).lineDifferentiableAt (v := basisR i) |>.hasLineDerivAt
  simpa only [testPartial, TestFunction.lineDerivCLM_apply, le_top, ite_true] using h

theorem contDiff_lineDeriv_continuous (F : Position → ℝ) (hF : ContDiff ℝ 1 F) (i : Fin 3) :
    Continuous (fun x => lineDeriv ℝ F x (basisR i)) := by
  have he : (fun x => lineDeriv ℝ F x (basisR i)) = fun x => fderiv ℝ F x (basisR i) := by
    funext x
    exact (hF.differentiable one_ne_zero x).lineDeriv_eq_fderiv
  rw [he]
  exact (hF.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)

theorem contDiff_test_ibp (F : Position → ℝ) (hF : ContDiff ℝ 1 F)
    (φ : ScalarTest) (i : Fin 3) :
    (∫ x, F x * (testPartial i φ) x) =
      -(∫ x, lineDeriv ℝ F x (basisR i) * φ x) := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) (v := basisR i)
  · exact ((contDiff_lineDeriv_continuous F hF i).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  · exact (hF.continuous.mul (testPartial i φ).continuous).integrable_of_hasCompactSupport
      (testPartial i φ).hasCompactSupport.mul_left
  · exact (hF.continuous.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  · intro x _
    exact (hF.differentiable one_ne_zero x).lineDifferentiableAt (v := basisR i) |>.hasLineDerivAt
  · intro x _
    exact testPartial_hasLineDerivAt φ i x

theorem exteriorCutoff_mul_lineDeriv (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (F F' : Position → ℝ) (i : Fin 3)
    (hF' : ∀ x, x ≠ 0 → HasLineDerivAt ℝ F (F' x) x (basisR i)) (x : Position) :
    lineDeriv ℝ (fun y => exteriorCutoff r t y * F y) x (basisR i) =
      exteriorCutoffPartial r t i x * F x + exteriorCutoff r t x * F' x := by
  by_cases hx : x = 0
  · subst x
    have he : (fun y => exteriorCutoff r t y * F y) =ᶠ[𝓝 (0 : Position)] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simpa using hr)] with y hy
      simp only [exteriorCutoff_zero ht y hy.le, zero_mul]
    have hd := (hasFDerivAt_const (𝕜 := ℝ) (E := Position) (0 : ℝ) (0 : Position)).hasLineDerivAt (basisR i)
      |>.congr_of_eventuallyEq he
    rw [hd.lineDeriv, exteriorCutoff_zero ht 0 (by simpa using hr.le)]
    simp [exteriorCutoffPartial]
  · have hχ := exteriorCutoff_hasLineDerivAt r t hr ht i x
    have hF := hF' x hx
    change HasDerivAt (fun s : ℝ => exteriorCutoff r t (x + s • basisR i)) _ 0 at hχ
    change HasDerivAt (fun s : ℝ => F (x + s • basisR i)) _ 0 at hF
    have h := hχ.mul hF
    change HasLineDerivAt ℝ (fun y => exteriorCutoff r t y * F y) _ x (basisR i) at h
    simpa only [zero_smul, add_zero] using h.lineDeriv

theorem exteriorCutoff_newton_ibp (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (φ : ScalarTest) (j : Fin 3) :
    (∫ x, exteriorCutoff r t x * newtonReal x * (testPartial j φ) x) =
      -(∫ x, (exteriorCutoffPartial r t j x * newtonReal x +
        exteriorCutoff r t x * newtonGradient j x) * φ x) := by
  have h := contDiff_test_ibp (fun x => exteriorCutoff r t x * newtonReal x)
    (exteriorCutoff_mul_contDiff r t hr ht newtonReal newtonReal_contDiffAt) φ j
  simpa only [exteriorCutoff_mul_lineDeriv r t hr ht newtonReal (newtonGradient j) j
    (newtonReal_hasLineDerivAt j)] using h

theorem exteriorCutoff_gradient_ibp (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (φ : ScalarTest) (i j : Fin 3) :
    (∫ x, exteriorCutoff r t x * newtonGradient j x * (testPartial i φ) x) =
      -(∫ x, (exteriorCutoffPartial r t i x * newtonGradient j x +
        exteriorCutoff r t x * newtonHessianKernel i j x) * φ x) := by
  have h := contDiff_test_ibp (fun x => exteriorCutoff r t x * newtonGradient j x)
    (exteriorCutoff_mul_contDiff r t hr ht (newtonGradient j) (newtonGradient_contDiffAt j)) φ i
  simpa only [exteriorCutoff_mul_lineDeriv r t hr ht (newtonGradient j) (newtonHessianKernel i j) i
    (newtonGradient_hasLineDerivAt i j)] using h

end OQ7Prescribed
