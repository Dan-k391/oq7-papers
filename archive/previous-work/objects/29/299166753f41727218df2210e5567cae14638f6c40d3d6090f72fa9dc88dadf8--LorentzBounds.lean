import work.LorentzIdentity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set

def electricDecayConstant (k R : ℝ) : ℝ := magneticDecayConstant k + radiationKernelConstant k R

theorem electricDecayConstant_nonneg (k R : ℝ) (hR : 0 ≤ R) : 0 ≤ electricDecayConstant k R := by
  unfold electricDecayConstant magneticDecayConstant radiationKernelConstant
  positivity

theorem exteriorElectric_norm_decay (k : ℝ) (p : CompactPolarization) (x : Position)
    (hx : 2 * p.radius + 2 ≤ ‖x‖) :
    ‖exteriorElectric k p x‖ ≤ electricDecayConstant k p.radius / ‖x‖ * ∫ y : Position, ‖p.current y‖ := by
  have hn : x ≠ 0 := norm_pos_iff.mp (by linarith [p.radius_nonneg])
  have hx1 : 1 ≤ ‖x‖ := by linarith [p.radius_nonneg]
  have hpR := p.radius_nonneg
  have hD : 0 ≤ radiationKernelConstant k p.radius := by unfold radiationKernelConstant; positivity
  have hN : 0 ≤ ∫ y : Position, ‖p.current y‖ := integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ ‖cross (exteriorMagnetic k p x) (complexify (radialDirection x))‖ +
        ‖cross (exteriorMagnetic k p x) (complexify (radialDirection x)) - exteriorElectric k p x‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
        (cross (exteriorMagnetic k p x) (complexify (radialDirection x))) (exteriorElectric k p x)
    _ ≤ ‖exteriorMagnetic k p x‖ +
        radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖ := by
      exact add_le_add (by simpa [complexify_norm, radialDirection_norm x hn] using
        (cross_norm_le (exteriorMagnetic k p x) (complexify (radialDirection x))))
        (exterior_radiation_integral_norm_le k p x hx)
    _ ≤ magneticDecayConstant k / ‖x‖ * (∫ y : Position, ‖p.current y‖) +
        radiationKernelConstant k p.radius / ‖x‖ * (∫ y : Position, ‖p.current y‖) := by
      apply add_le_add (exteriorMagnetic_norm_decay k p x hx)
      apply mul_le_mul_of_nonneg_right _ hN
      exact div_le_div_of_nonneg_left hD (by positivity)
        (by nlinarith [norm_nonneg x])
    _ = _ := by unfold electricDecayConstant; ring

theorem Lorentz_flux_norm_bound (E₁ H₁ E₂ H₂ n : Vector) :
    ‖bilinear E₁ (cross H₂ n) - bilinear E₂ (cross H₁ n)‖ ≤
      ‖E₁‖ * ‖cross H₂ n - E₂‖ + ‖E₂‖ * ‖cross H₁ n - E₁‖ := by
  have he : bilinear E₁ (cross H₂ n) - bilinear E₂ (cross H₁ n) =
      bilinear E₁ (cross H₂ n - E₂) - bilinear E₂ (cross H₁ n - E₁) := by
    rw [bilinear_sub_right, bilinear_sub_right, bilinear_comm E₂ E₁]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (bilinear_norm_le _ _) (bilinear_norm_le _ _))

def LorentzDecayConstant (k : ℝ) (p q : CompactPolarization) : ℝ :=
  (electricDecayConstant k p.radius * radiationKernelConstant k q.radius +
    electricDecayConstant k q.radius * radiationKernelConstant k p.radius) *
      (∫ y : Position, ‖p.current y‖) * (∫ y : Position, ‖q.current y‖)

theorem LorentzDecayConstant_nonneg (k : ℝ) (p q : CompactPolarization) : 0 ≤ LorentzDecayConstant k p q := by
  have hpR := p.radius_nonneg
  have hqR := q.radius_nonneg
  have hpN : 0 ≤ ∫ y : Position, ‖p.current y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hqN : 0 ≤ ∫ y : Position, ‖q.current y‖ := integral_nonneg (fun _ => norm_nonneg _)
  unfold LorentzDecayConstant electricDecayConstant magneticDecayConstant radiationKernelConstant
  positivity

theorem exterior_Lorentz_flux_norm_bound (k : ℝ) (p q : CompactPolarization) (x : Position)
    (hp : 2 * p.radius + 2 ≤ ‖x‖) (hq : 2 * q.radius + 2 ≤ ‖x‖) :
    ‖bilinear (exteriorElectric k p x) (cross (exteriorMagnetic k q x) (complexify (radialDirection x))) -
      bilinear (exteriorElectric k q x) (cross (exteriorMagnetic k p x) (complexify (radialDirection x)))‖ ≤
        LorentzDecayConstant k p q / ‖x‖ ^ 3 := by
  have hAp := electricDecayConstant_nonneg k p.radius p.radius_nonneg
  have hAq := electricDecayConstant_nonneg k q.radius q.radius_nonneg
  have hpN : 0 ≤ ∫ y : Position, ‖p.current y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hqN : 0 ≤ ∫ y : Position, ‖q.current y‖ := integral_nonneg (fun _ => norm_nonneg _)
  apply (Lorentz_flux_norm_bound _ _ _ _ _).trans
  calc
    _ ≤ (electricDecayConstant k p.radius / ‖x‖ * ∫ y : Position, ‖p.current y‖) *
          (radiationKernelConstant k q.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖q.current y‖) +
        (electricDecayConstant k q.radius / ‖x‖ * ∫ y : Position, ‖q.current y‖) *
          (radiationKernelConstant k p.radius / ‖x‖ ^ 2 * ∫ y : Position, ‖p.current y‖) := by
      exact add_le_add
        (mul_le_mul (exteriorElectric_norm_decay k p x hp) (exterior_radiation_integral_norm_le k q x hq)
          (norm_nonneg _) (mul_nonneg (div_nonneg hAp (norm_nonneg _)) hpN))
        (mul_le_mul (exteriorElectric_norm_decay k q x hq) (exterior_radiation_integral_norm_le k p x hp)
          (norm_nonneg _) (mul_nonneg (div_nonneg hAq (norm_nonneg _)) hqN))
    _ = _ := by unfold LorentzDecayConstant; ring

theorem smoothPhysicalSources_radial_flux_integrable (k : ℝ) (p q : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current)
    (r : ℝ) (hr : 0 < r) : Integrable (smoothLorentzRadialFlux k p q r) volume := by
  have hi₁ := smooth_cutoff_bilinear_flux_integrable k _ _ _
    (smoothElectricSource_contDiff k q hq) (smoothMagneticSource_contDiff k p hp)
    (smoothMagneticSource_contDiff k q hq).continuous (smoothElectricSource_curl k q hq)
    (sourceEnergyCutoff r) (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  have hi₂ := smooth_cutoff_bilinear_flux_integrable k _ _ _
    (smoothElectricSource_contDiff k p hp) (smoothMagneticSource_contDiff k q hq)
    (smoothMagneticSource_contDiff k p hp).continuous (smoothElectricSource_curl k p hp)
    (sourceEnergyCutoff r) (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  apply (hi₁.sub hi₂).congr
  apply ae_of_all
  intro x
  dsimp only [Pi.sub_apply, smoothLorentzRadialFlux]
  rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, cross_complexify_real_smul,
    bilinear_real_smul_right, bilinear_real_smul_right]
  simp only [Complex.ofReal_neg]
  ring

theorem smoothPhysicalSources_radial_flux_bound_ae (k : ℝ) (p q : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current)
    (M : ℝ) (hM : 0 ≤ M) (hMb : ∀ s : ℝ, transitionDerivative s ≤ M)
    (r : ℝ) (hr : 0 < r) (hpr : 2 * p.radius + 2 ≤ r) (hqr : 2 * q.radius + 2 ≤ r) :
    ∀ᵐ x ∂volume, ‖smoothLorentzRadialFlux k p q r x‖ ≤ M * LorentzDecayConstant k p q / r ^ 4 := by
  have hpEx : ∀ᵐ x ∂volume, x ∈ currentExterior p → exteriorElectric k p x = electricVolumeField k p x :=
    (ae_restrict_iff' (currentExterior p).isOpen.measurableSet).mp (electricExterior_eq_ae k p)
  have hqEx : ∀ᵐ x ∂volume, x ∈ currentExterior q → exteriorElectric k q x = electricVolumeField k q x :=
    (ae_restrict_iff' (currentExterior q).isOpen.measurableSet).mp (electricExterior_eq_ae k q)
  filter_upwards [hpEx, hqEx, smoothElectricSource_eq_ae k p hp, smoothElectricSource_eq_ae k q hq,
    smoothMagneticSource_eq_ae k p hp, smoothMagneticSource_eq_ae k q hq] with x hpE hqE hep heq hmp hmq
  by_cases hinner : ‖x‖ ≤ r
  · simp only [smoothLorentzRadialFlux, sourceEnergyWeight_zero_inner r hr x hinner, Complex.ofReal_zero, zero_mul, norm_zero]
    exact div_nonneg (mul_nonneg hM (LorentzDecayConstant_nonneg k p q)) (pow_nonneg hr.le 4)
  have hsr : r ≤ ‖x‖ := (lt_of_not_ge hinner).le
  have hpOut : x ∈ currentExterior p := by change p.radius + 1 < ‖x‖; linarith [p.radius_nonneg]
  have hqOut : x ∈ currentExterior q := by change q.radius + 1 < ‖x‖; linarith [q.radius_nonneg]
  simp only [smoothLorentzRadialFlux]
  rw [hep, heq, hmp, hmq, ← hpE hpOut, ← hqE hqOut,
    ← magneticExterior_eq_pointwise_far k p x (by linarith [p.radius_nonneg]),
    ← magneticExterior_eq_pointwise_far k q x (by linarith [q.radius_nonneg]), norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (sourceEnergyWeight_nonneg r hr x)]
  calc
    _ ≤ (M / r) * (LorentzDecayConstant k p q / ‖x‖ ^ 3) :=
      mul_le_mul (sourceEnergyWeight_le r M hr hMb x)
        (exterior_Lorentz_flux_norm_bound k p q x (hpr.trans hsr) (hqr.trans hsr))
        (norm_nonneg _) (div_nonneg hM hr.le)
    _ ≤ (M / r) * (LorentzDecayConstant k p q / r ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hM hr.le)
      exact div_le_div_of_nonneg_left (LorentzDecayConstant_nonneg k p q) (pow_pos hr 3)
        (pow_le_pow_left₀ hr.le hsr 3)
    _ = _ := by ring

end OQ7Prescribed
