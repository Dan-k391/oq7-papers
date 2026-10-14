import work.LorentzCutoff
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem smooth_cutoff_bilinear_flux_integrable (k : ℝ) (E H G : Field)
    (hE : ContDiff ℝ (⊤ : ℕ∞) E) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hG : Continuous G)
    (he : curl E = fun x => (Complex.I * (k : ℂ)) • G x)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x => bilinear (E x) (cross (H x) (complexify (scalarGradient ψ x)))) volume := by
  let φ : Field := ψ • E
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.smul hE
  have hsφ : HasCompactSupport φ := HasCompactSupport.smul_right (f' := E) hs
  have hl := compactField_bilinear_integrable H hH.continuous.locallyIntegrable (curl φ)
    (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hg := compact_scalar_weight_integrable ψ hψ.continuous hs
    (fun x => bilinear (H x) (G x)) (bilinear_continuous _ _ hH.continuous hG)
  apply (hl.sub (hg.const_mul (Complex.I * (k : ℂ)))).congr
  apply ae_of_all
  intro x
  change bilinear (H x) (curl (fun y => ψ y • E y) x) -
    (Complex.I * (k : ℂ)) * ((ψ x : ℂ) * bilinear (H x) (G x)) = _
  rw [curl_real_smul ψ E hψ hE, bilinear_add_right, bilinear_cross_cyclic,
    bilinear_real_smul_right, congrFun he x, bilinear_complex_smul_right]
  ring

theorem smooth_sources_cutoff_Lorentz (k : ℝ) (E₁ H₁ p₁ E₂ H₂ p₂ : Field)
    (hE₁ : ContDiff ℝ (⊤ : ℕ∞) E₁) (hH₁ : ContDiff ℝ (⊤ : ℕ∞) H₁) (hp₁ : Continuous p₁)
    (hE₂ : ContDiff ℝ (⊤ : ℕ∞) E₂) (hH₂ : ContDiff ℝ (⊤ : ℕ∞) H₂) (hp₂ : Continuous p₂)
    (he₁ : curl E₁ = fun x => (Complex.I * (k : ℂ)) • H₁ x)
    (hh₁ : curl H₁ = fun x => (-Complex.I * (k : ℂ)) • (E₁ x + p₁ x))
    (he₂ : curl E₂ = fun x => (Complex.I * (k : ℂ)) • H₂ x)
    (hh₂ : curl H₂ = fun x => (-Complex.I * (k : ℂ)) • (E₂ x + p₂ x))
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Position, bilinear (E₂ x) (cross (H₁ x) (complexify (scalarGradient ψ x))) -
      bilinear (E₁ x) (cross (H₂ x) (complexify (scalarGradient ψ x)))) =
        (-Complex.I * (k : ℂ)) * (∫ x : Position, (ψ x : ℂ) *
          (bilinear (p₁ x) (E₂ x) - bilinear (p₂ x) (E₁ x))) := by
  have h12 := smooth_pair_cutoff_curl k E₁ H₁ p₁ E₂ H₂ hH₁ hE₂ hE₁.continuous hH₂.continuous hp₁ he₂ hh₁ ψ hψ hs
  have h21 := smooth_pair_cutoff_curl k E₂ H₂ p₂ E₁ H₁ hH₂ hE₁ hE₂.continuous hH₁.continuous hp₂ he₁ hh₂ ψ hψ hs
  simp_rw [bilinear_comm (H₂ _) (H₁ _)] at h21
  have hi12 := compact_scalar_weight_integrable ψ hψ.continuous hs
    (fun x => bilinear (E₁ x + p₁ x) (E₂ x)) (bilinear_continuous _ _ (hE₁.continuous.add hp₁) hE₂.continuous)
  have hi21 := compact_scalar_weight_integrable ψ hψ.continuous hs
    (fun x => bilinear (E₂ x + p₂ x) (E₁ x)) (bilinear_continuous _ _ (hE₂.continuous.add hp₂) hE₁.continuous)
  have heq : (∫ x : Position, (ψ x : ℂ) * bilinear (E₁ x + p₁ x) (E₂ x)) -
      (∫ x : Position, (ψ x : ℂ) * bilinear (E₂ x + p₂ x) (E₁ x)) =
        ∫ x : Position, (ψ x : ℂ) * (bilinear (p₁ x) (E₂ x) - bilinear (p₂ x) (E₁ x)) := by
    rw [← integral_sub hi12 hi21]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp only; rw [bilinear_add_left, bilinear_add_left, bilinear_comm (E₂ x) (E₁ x)]; ring)
  rw [integral_sub
    (smooth_cutoff_bilinear_flux_integrable k E₂ H₁ H₂ hE₂ hH₁ hH₂.continuous he₂ ψ hψ hs)
    (smooth_cutoff_bilinear_flux_integrable k E₁ H₂ H₁ hE₁ hH₂ hH₁.continuous he₁ ψ hψ hs), ← heq]
  linear_combination h12 - h21

theorem sourceEnergyCutoff_bilinear_work (p : CompactPolarization) (E : Field)
    (r : ℝ) (hr : 0 < r) (hpr : p.radius ≤ r) :
    (fun x : Position => (sourceEnergyCutoff r x : ℂ) * bilinear (p.current x) (E x)) =
      (fun x => bilinear (p.current x) (E x)) := by
  funext x
  by_cases hx : ‖x‖ ≤ r
  · simp [sourceEnergyCutoff, exteriorCutoff_zero hr x hx]
  · simp [p.vanish x (hpr.trans_lt (lt_of_not_ge hx)), bilinear]

def smoothLorentzRadialFlux (k : ℝ) (p q : CompactPolarization) (r : ℝ) (x : Position) : ℂ :=
  (sourceEnergyWeight r x : ℂ) *
    (bilinear (smoothElectricSource k p x) (cross (smoothMagneticSource k q x) (complexify (radialDirection x))) -
      bilinear (smoothElectricSource k q x) (cross (smoothMagneticSource k p x) (complexify (radialDirection x))))

theorem smoothPhysicalSources_radial_Lorentz (k : ℝ) (p q : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current)
    (r : ℝ) (hr : 0 < r) (hpr : p.radius ≤ r) (hqr : q.radius ≤ r) :
    (∫ x : Position, smoothLorentzRadialFlux k p q r x) =
      (-Complex.I * (k : ℂ)) * (∫ x : Position,
        bilinear (p.current x) (smoothElectricSource k q x) -
          bilinear (q.current x) (smoothElectricSource k p x)) := by
  have h := smooth_sources_cutoff_Lorentz k _ _ _ _ _ _
    (smoothElectricSource_contDiff k p hp) (smoothMagneticSource_contDiff k p hp) hp.continuous
    (smoothElectricSource_contDiff k q hq) (smoothMagneticSource_contDiff k q hq) hq.continuous
    (smoothElectricSource_curl k p hp) (smoothMagneticSource_curl k p hp)
    (smoothElectricSource_curl k q hq) (smoothMagneticSource_curl k q hq)
    (sourceEnergyCutoff r) (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  have hwork : (fun x : Position => (sourceEnergyCutoff r x : ℂ) *
      (bilinear (p.current x) (smoothElectricSource k q x) - bilinear (q.current x) (smoothElectricSource k p x))) =
      (fun x => bilinear (p.current x) (smoothElectricSource k q x) - bilinear (q.current x) (smoothElectricSource k p x)) := by
    funext x
    rw [mul_sub, congrFun (sourceEnergyCutoff_bilinear_work p (smoothElectricSource k q) r hr hpr) x,
      congrFun (sourceEnergyCutoff_bilinear_work q (smoothElectricSource k p) r hr hqr) x]
  rw [hwork] at h
  have hflux : (fun x : Position =>
      bilinear (smoothElectricSource k q x) (cross (smoothMagneticSource k p x) (complexify (scalarGradient (sourceEnergyCutoff r) x))) -
      bilinear (smoothElectricSource k p x) (cross (smoothMagneticSource k q x) (complexify (scalarGradient (sourceEnergyCutoff r) x)))) =
      smoothLorentzRadialFlux k p q r := by
    funext x
    rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, cross_complexify_real_smul,
      bilinear_real_smul_right, bilinear_real_smul_right]
    simp only [Complex.ofReal_neg, smoothLorentzRadialFlux]
    ring
  rw [hflux] at h
  exact h

end OQ7Prescribed
