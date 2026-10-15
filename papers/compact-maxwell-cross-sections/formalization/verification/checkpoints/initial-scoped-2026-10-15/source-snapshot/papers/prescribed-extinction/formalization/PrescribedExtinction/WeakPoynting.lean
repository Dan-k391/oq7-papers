import PrescribedExtinction.WeakCurlWeightedGreen
import PrescribedExtinction.RadialEnergyCutoff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem weak_cutoff_left_real (E H : Vector) (v : Position) (r k : ℝ) :
    (inner ℂ H (cross (complexify v) E + r • ((Complex.I * (k : ℂ)) • H))).re =
      (pairing E (cross H (complexify v))).re := by
  rw [inner_add_right, inner_smul_right_eq_smul, inner_smul_right]
  have hs : (inner ℂ H H).im = 0 := inner_self_im (𝕜 := ℂ) H
  have hx : (inner ℂ H (cross (complexify v) E)).re =
      (pairing E (cross H (complexify v))).re := by
    rw [← pairing_eq_inner]
    simp [pairing, cross, complexify, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
    ring
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.real_smul,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hs, hx]
  ring

theorem weak_cutoff_right_real (E p : Vector) (r k : ℝ) :
    (inner ℂ ((-Complex.I * (k : ℂ)) • (E + p)) (r • E)).re =
      -k * ((r : ℂ) * pairing p E).im := by
  rw [inner_smul_left, inner_smul_right_eq_smul, inner_add_left, pairing_eq_inner]
  have hs : (inner ℂ E E).im = 0 := inner_self_im (𝕜 := ℂ) E
  simp only [Complex.mul_re, Complex.mul_im, Complex.real_smul, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, hs]
  ring

/-- Compact cutoff energy identity for weak Maxwell source fields. -/
theorem weak_source_cutoff_energy (k : ℝ) (E H p : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (hp : LocallySquareIntegrable p)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • (E x + p x)))
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    k * (∫ x : Position, (ψ x : ℂ) * pairing (p x) (E x)).im =
      -(∫ x : Position, (pairing (E x) (cross (H x) (complexify (scalarGradient ψ x)))).re) := by
  have hc : LocallySquareIntegrable (fun x => (-Complex.I * (k : ℂ)) • (E x + p x)) := by
    intro K hK
    exact ((hE K hK).add (hp K hK)).const_smul (-Complex.I * (k : ℂ))
  have hd : LocallySquareIntegrable (fun x => (Complex.I * (k : ℂ)) • H x) := by
    intro K hK
    exact (hH K hK).const_smul (Complex.I * (k : ℂ))
  have hw := weakCurl_weighted_inner_identity H E _ _ hH hE hc hd hh he ψ hψ hs
  have hiL : Integrable (fun x => inner ℂ (H x)
      (cross (complexify (scalarGradient ψ x)) (E x) + ψ x • ((Complex.I * (k : ℂ)) • H x))) volume :=
    locallyL2_inner_compactL2_integrable H hH _ (localizedWeakCurl_memLp E _ hE hd ψ hψ hs)
      (localizedWeakCurl_hasCompactSupport E _ ψ hs)
  have hiR := locallyL2_weighted_inner_integrable _ E hc hE ψ hψ.continuous hs
  have hiW : Integrable (fun x => (ψ x : ℂ) * pairing (p x) (E x)) volume := by
    simpa only [pairing_eq_inner, inner_smul_right_eq_smul, Complex.real_smul] using
      locallyL2_weighted_inner_integrable p E hp hE ψ hψ.continuous hs
  have hr := congrArg Complex.re hw
  change RCLike.re (∫ x : Position, inner ℂ (H x)
      (cross (complexify (scalarGradient ψ x)) (E x) + ψ x • ((Complex.I * (k : ℂ)) • H x))) =
      RCLike.re (∫ x : Position, inner ℂ ((-Complex.I * (k : ℂ)) • (E x + p x)) (ψ x • E x)) at hr
  rw [← integral_re hiL, ← integral_re hiR] at hr
  change (∫ x : Position, (inner ℂ (H x)
      (cross (complexify (scalarGradient ψ x)) (E x) + ψ x • ((Complex.I * (k : ℂ)) • H x))).re) =
      (∫ x : Position, (inner ℂ ((-Complex.I * (k : ℂ)) • (E x + p x)) (ψ x • E x)).re) at hr
  have hl : (∫ x : Position, (inner ℂ (H x)
      (cross (complexify (scalarGradient ψ x)) (E x) + ψ x • ((Complex.I * (k : ℂ)) • H x))).re) =
      ∫ x : Position, (pairing (E x) (cross (H x) (complexify (scalarGradient ψ x)))).re :=
    integral_congr_ae (ae_of_all _ fun x => weak_cutoff_left_real (E x) (H x) _ (ψ x) k)
  have hright : (∫ x : Position, (inner ℂ ((-Complex.I * (k : ℂ)) • (E x + p x)) (ψ x • E x)).re) =
      -k * (∫ x : Position, (ψ x : ℂ) * pairing (p x) (E x)).im := by
    change _ = -k * RCLike.im (∫ x : Position, (ψ x : ℂ) * pairing (p x) (E x))
    rw [← integral_im hiW, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => weak_cutoff_right_real (E x) (p x) (ψ x) k)
  rw [hl, hright] at hr
  linarith

theorem weak_source_radial_energy (k : ℝ) (E H : Field) (p : CompactPolarization)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • (E x + p.current x)))
    (r : ℝ) (hr : 0 < r) (hpr : p.radius ≤ r) :
    k * (∫ x : Position, pairing (p.current x) (E x)).im =
      ∫ x : Position, sourceEnergyWeight r x *
        (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re := by
  have hp : LocallySquareIntegrable p.current := by
    intro K _
    exact p.memLp.restrict K
  have h := weak_source_cutoff_energy k E H p.current hE hH hp he hh (sourceEnergyCutoff r)
    (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  rw [sourceEnergyCutoff_current_work p E r hr hpr] at h
  have heq : (fun x : Position => (pairing (E x)
      (cross (H x) (complexify (scalarGradient (sourceEnergyCutoff r) x)))).re) =
      (fun x => -(sourceEnergyWeight r x *
        (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re)) := by
    funext x
    rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, pairing_real_smul_right]
    simp [Complex.mul_re]
  rw [heq, integral_neg, neg_neg] at h
  exact h

theorem weak_cutoff_flux_integrable (k : ℝ) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x : Position =>
      (pairing (E x) (cross (H x) (complexify (scalarGradient ψ x)))).re) volume := by
  have hd : LocallySquareIntegrable (fun x => (Complex.I * (k : ℂ)) • H x) := by
    intro K hK
    exact (hH K hK).const_smul (Complex.I * (k : ℂ))
  have hi := locallyL2_inner_compactL2_integrable H hH _
    (localizedWeakCurl_memLp E _ hE hd ψ hψ hs)
    (localizedWeakCurl_hasCompactSupport E _ ψ hs)
  exact hi.re.congr (ae_of_all _ fun x => weak_cutoff_left_real (E x) (H x) _ (ψ x) k)

theorem weak_radial_flux_integrable (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : Position => sourceEnergyWeight r x *
      (pairing (E x) (cross (H x) (complexify (radialDirection x)))).re) volume := by
  have hi := weak_cutoff_flux_integrable 0 E H hE hH (sourceEnergyCutoff r)
    (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  apply hi.neg.congr
  apply ae_of_all
  intro x
  change -(pairing (E x) (cross (H x) (complexify (scalarGradient (sourceEnergyCutoff r) x)))).re = _
  rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, pairing_real_smul_right]
  simp [Complex.mul_re]

end OQ7Prescribed
