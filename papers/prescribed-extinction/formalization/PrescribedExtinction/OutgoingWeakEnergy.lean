import PrescribedExtinction.WeakPoynting
import PrescribedExtinction.FarFieldRadial

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem poynting_flux_residual_lower (E H : Vector) (n : Position) :
    -(‖cross H (complexify n) - E‖ ^ 2) ≤
      (pairing E (cross H (complexify n))).re := by
  let C := cross H (complexify n)
  let D := C - E
  have he : E = C - D := by dsimp [D]; abel
  have hp := (Complex.re_le_norm (inner ℂ D C)).trans (norm_inner_le_norm D C)
  rw [pairing_eq_inner]
  change -(‖D‖ ^ 2) ≤ (inner ℂ E C).re
  rw [he, inner_sub_left, Complex.sub_re,
    show (inner ℂ C C).re = ‖C‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) C]
  nlinarith [sq_nonneg (‖C‖ - ‖D‖), sq_nonneg ‖D‖]

theorem outgoing_radial_flux_lower (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ)
    (hout : ∀ x : Position, ρ ≤ ‖x‖ →
      ‖x‖ * ‖cross (H x) (complexify (‖x‖⁻¹ • x)) - E x‖ < ε)
    (r : ℝ) (hr : 0 < r) (hρr : ρ ≤ r) :
    -(4 * Real.pi * ε ^ 2) ≤
      ∫ x : Position, sourceEnergyWeight r x *
        (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re := by
  have hl : Integrable (fun x : Position => -(ε ^ 2) *
      (sourceEnergyWeight r x / ‖x‖ ^ 2 * (1 : ℝ))) volume :=
    (sourceEnergyWeight_direction_integrable r hr (fun _ => 1) continuous_const).const_mul _
  have hu := weak_radial_flux_integrable E H hE hH r hr
  have hc : (∫ x : Position, -(ε ^ 2) * (sourceEnergyWeight r x / ‖x‖ ^ 2 * (1 : ℝ))) =
      -(4 * Real.pi * ε ^ 2) := by
    rw [integral_const_mul, sourceEnergyWeight_direction_integral r hr (fun _ => 1)]
    simp [integral_const, smul_eq_mul, sphereArea_real_univ]
    ring
  rw [← hc]
  apply integral_mono_ae hl hu
  apply ae_of_all
  intro x
  by_cases hx : ‖x‖ ≤ r
  · simp [sourceEnergyWeight_zero_inner r hr x hx]
  · have hnx : 0 < ‖x‖ := hr.trans (lt_of_not_ge hx)
    have hb := hout x (hρr.trans (lt_of_not_ge hx).le)
    have hp := poynting_flux_residual_lower (E x) (H x) (radialDirection x)
    have hn : ‖cross (H x) (complexify (radialDirection x)) - E x‖ ^ 2 ≤ ε ^ 2 / ‖x‖ ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hnx)).mpr
      dsimp [radialDirection]
      nlinarith [mul_nonneg (norm_nonneg x)
        (norm_nonneg (cross (H x) (complexify (‖x‖⁻¹ • x)) - E x))]
    have hflux : -(ε ^ 2 / ‖x‖ ^ 2) ≤
        (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re := by linarith
    have hm := mul_le_mul_of_nonneg_left hflux (sourceEnergyWeight_nonneg r hr x)
    simpa only [mul_one] using (show -(ε ^ 2) * (sourceEnergyWeight r x / ‖x‖ ^ 2) ≤ _ by
      calc
        _ = sourceEnergyWeight r x * -(ε ^ 2 / ‖x‖ ^ 2) := by ring
        _ ≤ _ := hm)

/-- Any outgoing weak compact-source Maxwell pair has nonnegative total outward work. -/
theorem outgoing_weak_source_work_nonneg (k : ℝ) (E H : Field) (p : CompactPolarization)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • (E x + p.current x)))
    (hout : Outgoing E H) : 0 ≤ k * (∫ x : Position, pairing (p.current x) (E x)).im := by
  let W := k * (∫ x : Position, pairing (p.current x) (E x)).im
  change 0 ≤ W
  by_contra hn
  have hw : W < 0 := lt_of_not_ge hn
  let ε := min 1 (-W / (8 * Real.pi))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  obtain ⟨ρ, hρ, hb⟩ := hout ε hε
  let r := max (p.radius + 1) ρ
  have hr : 0 < r := hρ.trans_le (le_max_right _ _)
  have hpr : p.radius ≤ r := (by linarith : p.radius ≤ p.radius + 1).trans (le_max_left _ _)
  have heq := weak_source_radial_energy k E H p hE hH he hh r hr hpr
  have hlo := outgoing_radial_flux_lower E H hE hH ε ρ hε hρ hb r hr (le_max_right _ _)
  change W = _ at heq
  rw [← heq] at hlo
  have he1 : ε ≤ 1 := min_le_left _ _
  have hew : ε ≤ -W / (8 * Real.pi) := min_le_right _ _
  have hem : ε * (8 * Real.pi) ≤ -W := (le_div_iff₀ (by positivity)).mp hew
  have hes : ε ^ 2 ≤ ε := by nlinarith
  have hscale : 4 * Real.pi * ε ^ 2 ≤ 4 * Real.pi * ε :=
    mul_le_mul_of_nonneg_left hes (by positivity)
  linarith

end OQ7Prescribed
