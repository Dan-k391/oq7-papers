import work.WeakSmoothLorentz

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem smooth_source_weak_decay (k : ℝ) (q : CompactPolarization)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q.current) (r ε : ℝ) (hε : 0 ≤ ε)
    (hqr : 2 * q.radius + 2 ≤ r)
    (hc : radiationKernelConstant k q.radius * (∫ y : Position, ‖q.current y‖) ≤ ε * r) :
    ∀ᵐ x ∂volume, r ≤ ‖x‖ →
      ‖smoothElectricSource k q x‖ ≤
        (electricDecayConstant k q.radius * (∫ y : Position, ‖q.current y‖)) / ‖x‖ ∧
      ‖cross (smoothMagneticSource k q x) (complexify (radialDirection x)) -
        smoothElectricSource k q x‖ ≤ ε / ‖x‖ := by
  have hEx : ∀ᵐ x ∂volume, x ∈ currentExterior q → exteriorElectric k q x = electricVolumeField k q x :=
    (ae_restrict_iff' (currentExterior q).isOpen.measurableSet).mp (electricExterior_eq_ae k q)
  filter_upwards [hEx, smoothElectricSource_eq_ae k q hq, smoothMagneticSource_eq_ae k q hq]
    with x hEq hE hH
  intro hx
  have hfar : 2 * q.radius + 2 ≤ ‖x‖ := hqr.trans hx
  have hnx : 0 < ‖x‖ := by linarith [q.radius_nonneg]
  have hout : x ∈ currentExterior q := by change q.radius + 1 < ‖x‖; linarith [q.radius_nonneg]
  rw [hE, hH, ← hEq hout, ← magneticExterior_eq_pointwise_far k q x (by linarith [q.radius_nonneg])]
  constructor
  · exact (exteriorElectric_norm_decay k q x hfar).trans_eq (by ring)
  · apply (exterior_radiation_integral_norm_le k q x hfar).trans
    have hnum : radiationKernelConstant k q.radius * (∫ y : Position, ‖q.current y‖) ≤ ε * ‖x‖ :=
      hc.trans (mul_le_mul_of_nonneg_left hx hε)
    calc
      _ = (radiationKernelConstant k q.radius * (∫ y : Position, ‖q.current y‖) / ‖x‖) / ‖x‖ := by ring
      _ ≤ ε / ‖x‖ := div_le_div_of_nonneg_right ((div_le_iff₀ hnx).mpr hnum) hnx.le

end OQ7Prescribed
