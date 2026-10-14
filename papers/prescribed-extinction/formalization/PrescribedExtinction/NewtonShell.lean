import PrescribedExtinction.NewtonCutoffIBP
import PrescribedExtinction.NewtonCutoffLimit

/-! Conversion of the Newtonian cutoff derivative terms to genuine angular
integrals, using the existing polar measure. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter Metric
open scoped Topology

theorem exteriorCutoffPartial_zero_inner (r t : ℝ) (ht : 0 < t) (i : Fin 3)
    (x : Position) (hx : ‖x‖ ≤ r) : exteriorCutoffPartial r t i x = 0 := by
  unfold exteriorCutoffPartial
  rw [transitionDerivative_zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) ht.le)]
  simp

theorem exteriorCutoffPartial_zero_outer (r t : ℝ) (ht : 0 < t) (i : Fin 3)
    (x : Position) (hx : r + t ≤ ‖x‖) : exteriorCutoffPartial r t i x = 0 := by
  unfold exteriorCutoffPartial
  rw [transitionDerivative_zero_of_one_le ((le_div_iff₀ ht).mpr (by linarith))]
  simp

theorem exteriorCutoffPartial_mul_continuous (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (i : Fin 3) (F : Position → ℝ) (hF : ∀ x, x ≠ 0 → ContinuousAt F x) :
    Continuous (fun x => exteriorCutoffPartial r t i x * F x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : (fun y => exteriorCutoffPartial r t i y * F y) =ᶠ[𝓝 (0 : Position)] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simpa using hr)] with y hy
      simp only [exteriorCutoffPartial_zero_inner r t ht i y hy.le, zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he
  · have hc := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : Position →L[ℝ] ℝ).continuous.continuousAt (x := x)
    exact (((transitionDerivative_continuous.continuousAt.comp
      ((continuous_norm.continuousAt.sub continuousAt_const).div_const t)).mul
      (hc.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx))).div_const t).mul (hF x hx)

theorem exteriorCutoffPartial_mul_integrable (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (i : Fin 3) (F : Position → ℝ) (hF : ∀ x, x ≠ 0 → ContinuousAt F x) :
    Integrable (fun x => exteriorCutoffPartial r t i x * F x) volume := by
  have hc := exteriorCutoffPartial_mul_continuous r t hr ht i F hF
  have hs : Function.support (fun x => exteriorCutoffPartial r t i x * F x) ⊆ closedBall 0 (r + t) := by
    intro x hx
    by_contra hn
    have ho : r + t ≤ ‖x‖ := (lt_of_not_ge (by simpa only [mem_closedBall, dist_zero_right] using hn)).le
    exact hx (by
      change exteriorCutoffPartial r t i x * F x = 0
      rw [exteriorCutoffPartial_zero_outer r t ht i x ho, zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _))

theorem transition_radial_integral (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (A : ℝ → ℝ) :
    (∫ s in Ioi (0 : ℝ), transitionDerivative ((s - r) / t) * A s) =
      ∫ s in r..r + t, transitionDerivative ((s - r) / t) * A s := by
  have hz (s : ℝ) (hs : ¬(r < s ∧ s ≤ r + t)) :
      transitionDerivative ((s - r) / t) * A s = 0 := by
    by_cases h : s ≤ r
    · rw [transitionDerivative_zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) ht.le), zero_mul]
    · have ho : r + t ≤ s := (lt_of_not_ge (fun hle => hs ⟨lt_of_not_ge h, hle⟩)).le
      rw [transitionDerivative_zero_of_one_le ((le_div_iff₀ ht).mpr (by linarith)), zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => hz s (by
    have h : s ≤ 0 := le_of_not_gt hs
    exact fun h' => (hr.trans h'.1).not_ge h))]
  rw [intervalIntegral.integral_of_le (by linarith : r ≤ r + t)]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => hz s hs)).symm

theorem transition_radial_rescale (r t : ℝ) (ht : 0 < t) (A : ℝ → ℝ) :
    t⁻¹ * (∫ s in r..r + t, transitionDerivative ((s - r) / t) * A s) =
      ∫ u in (0 : ℝ)..1, transitionDerivative u * A (r + t * u) := by
  have h := intervalIntegral.integral_comp_mul_add
    (fun s => transitionDerivative ((s - r) / t) * A s)
    (a := (0 : ℝ)) (b := 1) ht.ne' r
  simpa [smul_eq_mul, add_comm, add_left_comm, mul_div_cancel_left₀ _ ht.ne'] using h.symm

theorem transition_average_tendsto (r : ℝ) (A : ℝ → ℝ) (hA : Continuous A) :
    Tendsto (fun t : ℝ => ∫ u in (0 : ℝ)..1, transitionDerivative u * A (r + t * u))
      (𝓝 (0 : ℝ)) (𝓝 (A r)) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1)
    (f := fun t : ℝ => fun u : ℝ => transitionDerivative u * A (r + t * u))
    (by have hc := transitionDerivative_continuous; fun_prop) isCompact_Icc
  have he (t : ℝ) :
      (∫ u in (0 : ℝ)..1, transitionDerivative u * A (r + t * u)) =
        ∫ u in Icc (0 : ℝ) 1, transitionDerivative u * A (r + t * u) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  have hz : (∫ u in (0 : ℝ)..1, transitionDerivative u * A (r + 0 * u)) = A r := by
    simp only [zero_mul, add_zero, intervalIntegral.integral_mul_const, transitionDerivative_integral, one_mul]
  have hh := h.continuousAt (x := 0)
  simp_rw [← he] at hh
  simpa only [hz] using hh.tendsto

end OQ7Prescribed
