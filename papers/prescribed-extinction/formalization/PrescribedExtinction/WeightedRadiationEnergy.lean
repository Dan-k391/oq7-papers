import PrescribedExtinction.OutgoingWeakEnergy

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

theorem locallyL2_weighted_norm_sq_integrable (F : Field) (hF : LocallySquareIntegrable F)
    (w : Position → ℝ) (hw : Continuous w) (hs : HasCompactSupport w)
    (hn : ∀ x, 0 ≤ w x) : Integrable (fun x => w x * ‖F x‖ ^ 2) volume := by
  have hc : Continuous (fun x => Real.sqrt (w x)) := hw.sqrt
  have hcs : HasCompactSupport (fun x => Real.sqrt (w x)) := hs.comp_left Real.sqrt_zero
  have h2 := compactScalarWeight_memLp F hF _ hc hcs
  apply (memLp_inner_integrable _ _ h2 h2).re.congr
  apply ae_of_all
  intro x
  change RCLike.re (inner ℂ (Real.sqrt (w x) • F x) (Real.sqrt (w x) • F x)) = w x * ‖F x‖ ^ 2
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hn x)]

theorem vacuum_weak_radial_flux_zero (k : ℝ) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (r : ℝ) (hr : 0 < r) :
    (∫ x : Position, sourceEnergyWeight r x *
      (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re) = 0 := by
  let p : CompactPolarization := ⟨0, 0, le_rfl, MemLp.zero, fun _ _ => rfl⟩
  have hh' : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • (E x + p.current x)) := by
    simpa only [p, Pi.zero_apply, add_zero] using hh
  have h := weak_source_radial_energy k E H p hE hH he hh' r hr hr.le
  simpa [p, pairing] using h.symm

/-- Uniform Silver–Muller residual and the weak vacuum energy identity
control the complete electric field in every weighted outgoing annulus. -/
theorem vacuum_weak_weighted_electric_energy (k : ℝ) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (ε ρ : ℝ) (hε : 0 < ε)
    (hout : ∀ x : Position, ρ ≤ ‖x‖ →
      ‖x‖ * ‖cross (H x) (complexify (‖x‖⁻¹ • x)) - E x‖ < ε)
    (r : ℝ) (hr : 0 < r) (hρr : ρ ≤ r) :
    (∫ x : Position, sourceEnergyWeight r x * ‖E x‖ ^ 2) ≤ 4 * Real.pi * ε ^ 2 := by
  have hiE := locallyL2_weighted_norm_sq_integrable E hE _ (sourceEnergyWeight_continuous r)
    (sourceEnergyWeight_hasCompactSupport r hr) (sourceEnergyWeight_nonneg r hr)
  have hiF := weak_radial_flux_integrable E H hE hH r hr
  have hiM := sourceEnergyWeight_direction_integrable r hr (fun _ => (1 : ℝ)) continuous_const
  have hm : (∫ x : Position, 2 * (sourceEnergyWeight r x *
      (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re) +
      ε ^ 2 * (sourceEnergyWeight r x / ‖x‖ ^ 2 * (1 : ℝ))) = 4 * Real.pi * ε ^ 2 := by
    rw [integral_add (hiF.const_mul _) (hiM.const_mul _), integral_const_mul,
      vacuum_weak_radial_flux_zero k E H hE hH he hh r hr, integral_const_mul,
      sourceEnergyWeight_direction_integral r hr (fun _ => (1 : ℝ))]
    simp [integral_const, smul_eq_mul, sphereArea_real_univ]
    ring
  rw [← hm]
  apply integral_mono_ae hiE ((hiF.const_mul _).add (hiM.const_mul _))
  apply ae_of_all
  intro x
  by_cases hx : ‖x‖ ≤ r
  · simp [sourceEnergyWeight_zero_inner r hr x hx]
  · have hnx : 0 < ‖x‖ := hr.trans (lt_of_not_ge hx)
    have hb := hout x (hρr.trans (lt_of_not_ge hx).le)
    have hd : ‖cross (H x) (complexify (radialDirection x)) - E x‖ ^ 2 ≤ ε ^ 2 / ‖x‖ ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hnx)).mpr
      dsimp [radialDirection]
      nlinarith [mul_nonneg (norm_nonneg x)
        (norm_nonneg (cross (H x) (complexify (‖x‖⁻¹ • x)) - E x))]
    have hs := norm_sub_sq (𝕜 := ℂ) (E x) (cross (H x) (complexify (radialDirection x)))
    rw [norm_sub_rev] at hs
    change ‖cross (H x) (complexify (radialDirection x)) - E x‖ ^ 2 =
      ‖E x‖ ^ 2 - 2 * (inner ℂ (E x) (cross (H x) (complexify (radialDirection x)))).re +
        ‖cross (H x) (complexify (radialDirection x))‖ ^ 2 at hs
    have heL : ‖E x‖ ^ 2 ≤
        2 * (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re + ε ^ 2 / ‖x‖ ^ 2 := by
      rw [pairing_eq_inner]
      nlinarith [sq_nonneg ‖cross (H x) (complexify (radialDirection x))‖]
    have hw := mul_le_mul_of_nonneg_left heL (sourceEnergyWeight_nonneg r hr x)
    change sourceEnergyWeight r x * ‖E x‖ ^ 2 ≤
      2 * (sourceEnergyWeight r x * (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re) +
        ε ^ 2 * (sourceEnergyWeight r x / ‖x‖ ^ 2 * 1)
    calc
      _ ≤ _ := hw
      _ = _ := by ring

end OQ7Prescribed
