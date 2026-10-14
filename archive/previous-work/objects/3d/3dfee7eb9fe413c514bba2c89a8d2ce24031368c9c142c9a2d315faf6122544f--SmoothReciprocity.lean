import work.LorentzBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

theorem integral_compact_ball_complex_bound (f : Position → ℂ) (hf : Integrable f volume)
    (r C : ℝ) (hr : 0 < r) (hz : ∀ x : Position, 2 * r < ‖x‖ → f x = 0)
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ C / r ^ 4) :
    ‖∫ x : Position, f x‖ ≤ (64 * Real.pi / 3) * C / r := by
  have hre := integral_compact_ball_abs_bound (fun x => (f x).re) hf.re r C hr
    (fun x hx => by rw [hz x hx]; rfl)
    (hb.mono (fun x hx => (Complex.abs_re_le_norm (f x)).trans hx))
  have him := integral_compact_ball_abs_bound (fun x => (f x).im) hf.im r C hr
    (fun x hx => by rw [hz x hx]; rfl)
    (hb.mono (fun x hx => (Complex.abs_im_le_norm (f x)).trans hx))
  have h := Complex.norm_le_abs_re_add_abs_im (∫ x : Position, f x)
  change ‖∫ x : Position, f x‖ ≤ |RCLike.re (∫ x : Position, f x)| + |RCLike.im (∫ x : Position, f x)| at h
  rw [← integral_re hf, ← integral_im hf] at h
  change ‖∫ x : Position, f x‖ ≤ |∫ x : Position, (f x).re| + |∫ x : Position, (f x).im| at h
  calc
    _ ≤ (32 * Real.pi / 3) * C / r + (32 * Real.pi / 3) * C / r :=
      h.trans (add_le_add hre him)
    _ = _ := by ring

theorem smoothPhysicalSources_Lorentz_boundary_error (k : ℝ) (p q : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current)
    (M : ℝ) (hM : 0 ≤ M) (hMb : ∀ s : ℝ, transitionDerivative s ≤ M)
    (r : ℝ) (hr : 0 < r) (hpr : 2 * p.radius + 2 ≤ r) (hqr : 2 * q.radius + 2 ≤ r) :
    ‖(-Complex.I * (k : ℂ)) * (∫ x : Position,
      bilinear (p.current x) (smoothElectricSource k q x) -
        bilinear (q.current x) (smoothElectricSource k p x))‖ ≤
          (64 * Real.pi / 3) * (M * LorentzDecayConstant k p q) / r := by
  rw [← smoothPhysicalSources_radial_Lorentz k p q hp hq r hr
    (by linarith [p.radius_nonneg]) (by linarith [q.radius_nonneg])]
  apply integral_compact_ball_complex_bound _ (smoothPhysicalSources_radial_flux_integrable k p q hp hq r hr) r _ hr
  · intro x hx
    simp [smoothLorentzRadialFlux, sourceEnergyWeight_zero_outer r hr x hx.le]
  · exact smoothPhysicalSources_radial_flux_bound_ae k p q hp hq M hM hMb r hr hpr hqr

theorem smoothPhysicalSources_reciprocity (k : ℝ) (hk : 0 < k) (p q : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current) :
    (∫ x : Position, bilinear (p.current x) (electricVolumeField k q x)) =
      ∫ x : Position, bilinear (q.current x) (electricVolumeField k p x) := by
  obtain ⟨M, hM, hMb⟩ := transitionDerivative_global_bound
  have hbound (s : ℝ) : transitionDerivative s ≤ M :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMb s)
  have ht : Tendsto (fun r : ℝ => (64 * Real.pi / 3) * (M * LorentzDecayConstant k p q) / r)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((64 * Real.pi / 3) * (M * LorentzDecayConstant k p q))
  have hb : ∀ᶠ r : ℝ in atTop,
      ‖(-Complex.I * (k : ℂ)) * (∫ x : Position, bilinear (p.current x) (smoothElectricSource k q x) -
        bilinear (q.current x) (smoothElectricSource k p x))‖ ≤
          (64 * Real.pi / 3) * (M * LorentzDecayConstant k p q) / r := by
    filter_upwards [eventually_ge_atTop (2 * p.radius + 2), eventually_ge_atTop (2 * q.radius + 2)] with r hpr hqr
    exact smoothPhysicalSources_Lorentz_boundary_error k p q hp hq M hM hbound r
      (by linarith [p.radius_nonneg]) hpr hqr
  have hz : (-Complex.I * (k : ℂ)) * (∫ x : Position, bilinear (p.current x) (smoothElectricSource k q x) -
      bilinear (q.current x) (smoothElectricSource k p x)) = 0 :=
    norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht hb) (norm_nonneg _))
  have hkC : (-Complex.I * (k : ℂ)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hk.ne')
  have hw := (mul_eq_zero.mp hz).resolve_left hkC
  have hip : Integrable (fun x => bilinear (p.current x) (smoothElectricSource k q x)) volume := by
    simp_rw [bilinear_comm (p.current _) (smoothElectricSource k q _)]
    exact compactField_bilinear_integrable _ (smoothElectricSource_contDiff k q hq).continuous.locallyIntegrable
      p.current hp.continuous (compactPolarization_current_hasCompactSupport p)
  have hiq : Integrable (fun x => bilinear (q.current x) (smoothElectricSource k p x)) volume := by
    simp_rw [bilinear_comm (q.current _) (smoothElectricSource k p _)]
    exact compactField_bilinear_integrable _ (smoothElectricSource_contDiff k p hp).continuous.locallyIntegrable
      q.current hq.continuous (compactPolarization_current_hasCompactSupport q)
  rw [integral_sub hip hiq] at hw
  calc
    _ = ∫ x : Position, bilinear (p.current x) (smoothElectricSource k q x) := by
      apply integral_congr_ae
      filter_upwards [smoothElectricSource_eq_ae k q hq] with x hx
      rw [hx]
    _ = ∫ x : Position, bilinear (q.current x) (smoothElectricSource k p x) := sub_eq_zero.mp hw
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [smoothElectricSource_eq_ae k p hp] with x hx
      rw [hx]

end OQ7Prescribed
