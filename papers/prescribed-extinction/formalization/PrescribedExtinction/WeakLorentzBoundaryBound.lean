import PrescribedExtinction.WeightedRadiationEnergy
import PrescribedExtinction.WeakSmoothLorentz

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def weakLorentzRadialFlux (E H Eq Hq : Field) (r : ℝ) (x : Position) : ℂ :=
  (sourceEnergyWeight r x : ℂ) *
    (bilinear (E x) (cross (Hq x) (complexify (radialDirection x))) -
      bilinear (Eq x) (cross (H x) (complexify (radialDirection x))))

/-- Weighted energy, together with the two genuine radiation residuals,
makes the weak Lorentz boundary pairing small. -/
theorem weak_Lorentz_boundary_bound (E H Eq Hq : Field)
    (hE : LocallySquareIntegrable E) (r ε B ρ : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (hB : 0 ≤ B) (hρr : ρ ≤ r)
    (hout : ∀ x : Position, ρ ≤ ‖x‖ →
      ‖x‖ * ‖cross (H x) (complexify (‖x‖⁻¹ • x)) - E x‖ < ε)
    (hcanonical : ∀ᵐ x ∂volume, r ≤ ‖x‖ →
      ‖Eq x‖ ≤ B / ‖x‖ ∧
      ‖cross (Hq x) (complexify (radialDirection x)) - Eq x‖ ≤ ε / ‖x‖)
    (henergy : (∫ x : Position, sourceEnergyWeight r x * ‖E x‖ ^ 2) ≤ 4 * Real.pi * ε ^ 2) :
    ‖∫ x : Position, weakLorentzRadialFlux E H Eq Hq r x‖ ≤ 4 * Real.pi * (ε ^ 2 + B * ε) := by
  let b : Position → ℝ := fun x =>
    (sourceEnergyWeight r x * ‖E x‖ ^ 2) / 2 +
      (ε ^ 2 / 2 + B * ε) * (sourceEnergyWeight r x / ‖x‖ ^ 2 * (1 : ℝ))
  have hiE := locallyL2_weighted_norm_sq_integrable E hE _ (sourceEnergyWeight_continuous r)
    (sourceEnergyWeight_hasCompactSupport r hr) (sourceEnergyWeight_nonneg r hr)
  have hiM := sourceEnergyWeight_direction_integrable r hr (fun _ => (1 : ℝ)) continuous_const
  have hib : Integrable b volume := (hiE.div_const 2).add (hiM.const_mul _)
  have hnorm : ∀ᵐ x ∂volume, ‖weakLorentzRadialFlux E H Eq Hq r x‖ ≤ b x := by
    filter_upwards [hcanonical] with x hc
    by_cases hx : ‖x‖ ≤ r
    · simp [weakLorentzRadialFlux, b, sourceEnergyWeight_zero_inner r hr x hx]
    · have hnx : 0 < ‖x‖ := hr.trans (lt_of_not_ge hx)
      have hsr := (lt_of_not_ge hx).le
      obtain ⟨hEq, hdq⟩ := hc hsr
      have hdf : ‖cross (H x) (complexify (radialDirection x)) - E x‖ ≤ ε / ‖x‖ := by
        apply (le_div_iff₀ hnx).mpr
        simpa only [radialDirection, mul_comm] using (hout x (hρr.trans hsr)).le
      have hf := Lorentz_flux_norm_bound (E x) (H x) (Eq x) (Hq x) (complexify (radialDirection x))
      have hprod : ‖bilinear (E x) (cross (Hq x) (complexify (radialDirection x))) -
          bilinear (Eq x) (cross (H x) (complexify (radialDirection x)))‖ ≤
          ‖E x‖ * (ε / ‖x‖) + (B / ‖x‖) * (ε / ‖x‖) := by
        exact hf.trans (add_le_add (mul_le_mul_of_nonneg_left hdq (norm_nonneg _))
          (mul_le_mul hEq hdf (norm_nonneg _) (div_nonneg hB hnx.le)))
      have hYoung : ‖E x‖ * (ε / ‖x‖) ≤ ‖E x‖ ^ 2 / 2 + ε ^ 2 / (2 * ‖x‖ ^ 2) := by
        have hy : 2 * ‖E x‖ * (ε / ‖x‖) ≤ ‖E x‖ ^ 2 + (ε / ‖x‖) ^ 2 := by
          nlinarith [sq_nonneg (‖E x‖ - ε / ‖x‖)]
        rw [div_pow] at hy
        calc
          _ ≤ (‖E x‖ ^ 2 + ε ^ 2 / ‖x‖ ^ 2) / 2 := by linarith
          _ = _ := by ring
      change ‖(sourceEnergyWeight r x : ℂ) * _‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sourceEnergyWeight_nonneg r hr x)]
      calc
        _ ≤ sourceEnergyWeight r x * (‖E x‖ * (ε / ‖x‖) + (B / ‖x‖) * (ε / ‖x‖)) :=
          mul_le_mul_of_nonneg_left hprod (sourceEnergyWeight_nonneg r hr x)
        _ ≤ sourceEnergyWeight r x * (‖E x‖ ^ 2 / 2 + ε ^ 2 / (2 * ‖x‖ ^ 2) + (B / ‖x‖) * (ε / ‖x‖)) :=
          mul_le_mul_of_nonneg_left (add_le_add hYoung le_rfl) (sourceEnergyWeight_nonneg r hr x)
        _ = b x := by dsimp [b]; field_simp; ring
  have hbound := norm_integral_le_of_norm_le hib hnorm
  have hm : (∫ x : Position, sourceEnergyWeight r x / ‖x‖ ^ 2 * (1 : ℝ)) = 4 * Real.pi := by
    rw [sourceEnergyWeight_direction_integral r hr (fun _ => (1 : ℝ))]
    simp [integral_const, smul_eq_mul, sphereArea_real_univ]
  have hb : (∫ x : Position, b x) ≤ 4 * Real.pi * (ε ^ 2 + B * ε) := by
    dsimp [b]
    rw [integral_add (hiE.div_const 2) (hiM.const_mul _), integral_div, integral_const_mul, hm]
    linarith
  exact hbound.trans hb

end OQ7Prescribed
