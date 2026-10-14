import PrescribedExtinction.WeakPoynting
import PrescribedExtinction.LorentzBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem locallyIntegrable_weighted_smooth_bilinear (F G : Field)
    (hF : LocallyIntegrable F volume) (hG : Continuous G)
    (ψ : Position → ℝ) (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x => (ψ x : ℂ) * bilinear (F x) (G x)) volume := by
  have h := compactField_bilinear_integrable F hF (fun x => ψ x • G x)
    (hψ.smul hG) (hs.smul_right (f' := G))
  apply h.congr
  exact ae_of_all _ (fun x => by
    change bilinear (F x) (ψ x • G x) = _
    rw [bilinear_real_smul_right])

/-- Test a nonsmooth weak-curl field against a compactly weighted smooth field. -/
theorem weak_smooth_cutoff_bilinear_green (F C G : Field)
    (hF : LocallyIntegrable F volume) (hC : LocallyIntegrable C volume)
    (hcurl : HasWeakCurl F C) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Position, bilinear (G x) (cross (F x) (complexify (scalarGradient ψ x)))) +
      (∫ x : Position, (ψ x : ℂ) * bilinear (F x) (curl G x)) =
      ∫ x : Position, (ψ x : ℂ) * bilinear (C x) (G x) := by
  let φ : Field := fun x => ψ x • G x
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.smul hG
  have hsφ : HasCompactSupport φ := hs.smul_right (f' := G)
  have hw := hcurl φ hφ hsφ
  have hi := compactField_bilinear_integrable F hF (curl φ)
    (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hd := locallyIntegrable_weighted_smooth_bilinear F (curl G) hF
    (smoothField_curl_continuous G hG) ψ hψ.continuous hs
  have hc := locallyIntegrable_weighted_smooth_bilinear C G hC hG.continuous ψ hψ.continuous hs
  have hp (x : Position) : bilinear (F x) (curl φ x) =
      bilinear (G x) (cross (F x) (complexify (scalarGradient ψ x))) +
        (ψ x : ℂ) * bilinear (F x) (curl G x) := by
    change bilinear (F x) (curl (fun y => ψ y • G y) x) = _
    rw [curl_real_smul ψ G hψ hG, bilinear_add_right, bilinear_cross_cyclic,
      bilinear_real_smul_right]
  have hf : Integrable (fun x => bilinear (G x) (cross (F x) (complexify (scalarGradient ψ x)))) volume := by
    apply (hi.sub hd).congr
    exact ae_of_all _ fun x => by
      change bilinear (F x) (curl φ x) - (ψ x : ℂ) * bilinear (F x) (curl G x) = _
      rw [hp]
      ring
  rw [← integral_add hf hd]
  calc
    _ = ∫ x : Position, bilinear (F x) (curl φ x) :=
      integral_congr_ae (ae_of_all _ fun x => (hp x).symm)
    _ = ∫ x : Position, bilinear (C x) (φ x) := hw
    _ = _ := integral_congr_ae (ae_of_all _ fun x => bilinear_real_smul_right (C x) (G x) (ψ x))

theorem vacuum_weak_smooth_source_cutoff_Lorentz (k : ℝ) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (q : CompactPolarization) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Position, bilinear (smoothElectricSource k q x)
      (cross (H x) (complexify (scalarGradient ψ x)))) -
      (∫ x : Position, bilinear (E x)
        (cross (smoothMagneticSource k q x) (complexify (scalarGradient ψ x)))) =
      (Complex.I * (k : ℂ)) * (∫ x : Position, (ψ x : ℂ) * bilinear (q.current x) (E x)) := by
  have hEl := locallySquareIntegrable_locallyIntegrable E hE
  have hHl := locallySquareIntegrable_locallyIntegrable H hH
  have hEq := smoothElectricSource_contDiff k q hq
  have hHq := smoothMagneticSource_contDiff k q hq
  have h1 := weak_smooth_cutoff_bilinear_green H _ _ hHl
    (hEl.smul (-Complex.I * (k : ℂ))) hh hEq ψ hψ hs
  have h2 := weak_smooth_cutoff_bilinear_green E _ _ hEl
    (hHl.smul (Complex.I * (k : ℂ))) he hHq ψ hψ hs
  simp only [smoothElectricSource_curl k q hq, smoothMagneticSource_curl k q hq,
    Pi.smul_apply, bilinear_complex_smul_right, bilinear_complex_smul_left] at h1 h2
  have hz (x : Position) : bilinear (smoothMagneticSource k q x)
      (cross (E x) (complexify (scalarGradient ψ x))) =
      -bilinear (E x) (cross (smoothMagneticSource k q x) (complexify (scalarGradient ψ x))) := by
    rw [bilinear_cross_cycle, bilinear_cross_skew]
  simp only [hz, bilinear_add_right, bilinear_comm (H _) (smoothMagneticSource k q _),
    bilinear_comm (E _) (q.current _)] at h1 h2
  have hEE := locallyIntegrable_weighted_smooth_bilinear E _ hEl hEq.continuous ψ hψ.continuous hs
  have hHH := locallyIntegrable_weighted_smooth_bilinear H _ hHl hHq.continuous ψ hψ.continuous hs
  have hEqw := locallyIntegrable_weighted_smooth_bilinear E _ hEl hq.continuous ψ hψ.continuous hs
  have hQ : Integrable (fun x => (ψ x : ℂ) * bilinear (q.current x) (E x)) volume := by
    simpa only [bilinear_comm] using hEqw
  have hHH' : Integrable (fun x => (ψ x : ℂ) * bilinear (smoothMagneticSource k q x) (H x)) volume := by
    simpa only [bilinear_comm] using hHH
  have hs1 : (fun x => (ψ x : ℂ) * ((Complex.I * (k : ℂ)) *
      bilinear (smoothMagneticSource k q x) (H x))) =
      fun x => (Complex.I * (k : ℂ)) * ((ψ x : ℂ) * bilinear (smoothMagneticSource k q x) (H x)) := by
    funext x; ring
  have hs2 : (fun x => (ψ x : ℂ) * ((-Complex.I * (k : ℂ)) *
      (bilinear (E x) (smoothElectricSource k q x) + bilinear (q.current x) (E x)))) =
      fun x => (-Complex.I * (k : ℂ)) * ((ψ x : ℂ) * bilinear (E x) (smoothElectricSource k q x) +
        (ψ x : ℂ) * bilinear (q.current x) (E x)) := by funext x; ring
  have hs3 : (fun x => (ψ x : ℂ) * ((-Complex.I * (k : ℂ)) *
      bilinear (E x) (smoothElectricSource k q x))) =
      fun x => (-Complex.I * (k : ℂ)) * ((ψ x : ℂ) * bilinear (E x) (smoothElectricSource k q x)) := by
    funext x; ring
  rw [hs1, hs3, integral_const_mul, integral_const_mul] at h1
  rw [integral_neg, hs2, hs1, integral_const_mul, integral_add hEE hQ, integral_const_mul] at h2
  linear_combination h1 + h2

theorem vacuum_weak_smooth_source_radial_Lorentz (k : ℝ) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (q : CompactPolarization) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current)
    (r : ℝ) (hr : 0 < r) (hqr : q.radius ≤ r) :
    (∫ x : Position, (sourceEnergyWeight r x : ℂ) *
      (bilinear (E x) (cross (smoothMagneticSource k q x) (complexify (radialDirection x))) -
        bilinear (smoothElectricSource k q x) (cross (H x) (complexify (radialDirection x))))) =
      (Complex.I * (k : ℂ)) * (∫ x : Position, bilinear (q.current x) (E x)) := by
  have h := vacuum_weak_smooth_source_cutoff_Lorentz k E H hE hH he hh q hq (sourceEnergyCutoff r)
    (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  have hHl := locallySquareIntegrable_locallyIntegrable H hH
  have hEl := locallySquareIntegrable_locallyIntegrable E hE
  let V1 : Field := fun x => cross (complexify (scalarGradient (sourceEnergyCutoff r) x)) (smoothElectricSource k q x)
  let V2 : Field := fun x => cross (smoothMagneticSource k q x) (complexify (scalarGradient (sourceEnergyCutoff r) x))
  have hcgrad : Continuous (fun x => complexify (scalarGradient (sourceEnergyCutoff r) x)) :=
    complexify_continuous.comp (scalarGradient_contDiff _ (sourceEnergyCutoff_contDiff r hr)).continuous
  have hsgrad : HasCompactSupport (fun x => complexify (scalarGradient (sourceEnergyCutoff r) x)) :=
    (scalarGradient_hasCompactSupport _ (sourceEnergyCutoff_hasCompactSupport r hr)).comp_left
      (show complexify (0 : Position) = 0 by ext i; simp [complexify])
  have hi1 := compactField_bilinear_integrable H hHl V1
    (cross_continuous_fields _ _ hcgrad (smoothElectricSource_contDiff k q hq).continuous)
    (cross_compactSupport_left _ _ hsgrad)
  have hi2 := compactField_bilinear_integrable E hEl V2
    (cross_continuous_fields _ _ (smoothMagneticSource_contDiff k q hq).continuous hcgrad)
    (cross_compactSupport_right _ _ hsgrad)
  have hi1' : Integrable (fun x => bilinear (smoothElectricSource k q x)
      (cross (H x) (complexify (scalarGradient (sourceEnergyCutoff r) x)))) volume := by
    apply hi1.congr
    exact ae_of_all _ fun x => bilinear_cross_cyclic (H x) _ _
  rw [sourceEnergyCutoff_bilinear_work q E r hr hqr, ← integral_sub hi1' hi2] at h
  have hpoint (x : Position) : bilinear (smoothElectricSource k q x)
      (cross (H x) (complexify (scalarGradient (sourceEnergyCutoff r) x))) -
      bilinear (E x) (cross (smoothMagneticSource k q x) (complexify (scalarGradient (sourceEnergyCutoff r) x))) =
      (sourceEnergyWeight r x : ℂ) *
        (bilinear (E x) (cross (smoothMagneticSource k q x) (complexify (radialDirection x))) -
          bilinear (smoothElectricSource k q x) (cross (H x) (complexify (radialDirection x)))) := by
    rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, cross_complexify_real_smul,
      bilinear_real_smul_right, bilinear_real_smul_right]
    simp only [Complex.ofReal_neg]
    ring
  exact (integral_congr_ae (ae_of_all _ fun x => (hpoint x).symm)).trans h

end OQ7Prescribed
