import PrescribedExtinction.RadialEnergyCutoff
import PrescribedExtinction.FarFieldWork

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem bilinear_comm (u v : Vector) : bilinear u v = bilinear v u := by
  simp only [bilinear, mul_comm]

theorem bilinear_cross_cyclic (u v w : Vector) :
    bilinear u (cross v w) = bilinear w (cross u v) := by
  simp [bilinear, cross, Fin.sum_univ_three]
  ring

theorem bilinear_sub_left (u v w : Vector) : bilinear (u - v) w = bilinear u w - bilinear v w := by
  simp [bilinear, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem bilinear_sub_right (u v w : Vector) : bilinear u (v - w) = bilinear u v - bilinear u w := by
  rw [bilinear_comm, bilinear_sub_left, bilinear_comm v u, bilinear_comm w u]

theorem bilinear_complex_smul_left (u v : Vector) (z : ℂ) :
    bilinear (z • u) v = z * bilinear u v := by
  rw [bilinear_comm, bilinear_complex_smul_right, bilinear_comm v u]

theorem bilinear_eq_conjugate_inner (u v : Vector) :
    bilinear u v = inner ℂ (vectorConjugate u) v := by
  simp [bilinear, PiLp.inner_apply, RCLike.inner_apply, vectorConjugate_apply, mul_comm]

theorem vectorConjugate_norm (v : Vector) : ‖vectorConjugate v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← squareNorm_eq_norm_sq,
    ← squareNorm_eq_norm_sq]
  simp [squareNorm, vectorConjugate_apply]

theorem bilinear_norm_le (u v : Vector) : ‖bilinear u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [bilinear_eq_conjugate_inner]
  simpa only [vectorConjugate_norm] using norm_inner_le_norm (vectorConjugate u) v

theorem bilinear_continuous (F G : Field) (hF : Continuous F) (hG : Continuous G) :
    Continuous (fun x => bilinear (F x) (G x)) := by
  change Continuous (fun x => ∑ i : Fin 3, F x i * G x i)
  apply continuous_finset_sum
  intro i _
  exact ((vectorCoordinate i).continuous.comp hF).mul ((vectorCoordinate i).continuous.comp hG)

theorem smooth_pair_cutoff_curl (k : ℝ) (E₁ H₁ p₁ E₂ H₂ : Field)
    (hH₁ : ContDiff ℝ (⊤ : ℕ∞) H₁) (hE₂ : ContDiff ℝ (⊤ : ℕ∞) E₂)
    (hE₁ : Continuous E₁) (hH₂ : Continuous H₂) (hp₁ : Continuous p₁)
    (he₂ : curl E₂ = fun x => (Complex.I * (k : ℂ)) • H₂ x)
    (hh₁ : curl H₁ = fun x => (-Complex.I * (k : ℂ)) • (E₁ x + p₁ x))
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Position, bilinear (E₂ x) (cross (H₁ x) (complexify (scalarGradient ψ x)))) +
      (Complex.I * (k : ℂ)) * (∫ x : Position, (ψ x : ℂ) * bilinear (H₁ x) (H₂ x)) =
        (-Complex.I * (k : ℂ)) *
          (∫ x : Position, (ψ x : ℂ) * bilinear (E₁ x + p₁ x) (E₂ x)) := by
  let φ : Field := ψ • E₂
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.smul hE₂
  have hsφ : HasCompactSupport φ := HasCompactSupport.smul_right (f' := E₂) hs
  have h := smoothField_hasWeakCurl H₁ hH₁ φ hφ hsφ
  change (∫ x : Position, bilinear (H₁ x) (curl φ x)) =
    ∫ x : Position, bilinear (curl H₁ x) (φ x) at h
  have hleft := compactField_bilinear_integrable H₁ hH₁.continuous.locallyIntegrable
    (curl φ) (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hHH := compact_scalar_weight_integrable ψ hψ.continuous hs
    (fun x => bilinear (H₁ x) (H₂ x)) (bilinear_continuous _ _ hH₁.continuous hH₂)
  have hEP := compact_scalar_weight_integrable ψ hψ.continuous hs
    (fun x => bilinear (E₁ x + p₁ x) (E₂ x)) (bilinear_continuous _ _ (hE₁.add hp₁) hE₂.continuous)
  have hlpoint (x : Position) : bilinear (H₁ x) (curl φ x) =
      bilinear (E₂ x) (cross (H₁ x) (complexify (scalarGradient ψ x))) +
        (Complex.I * (k : ℂ)) * ((ψ x : ℂ) * bilinear (H₁ x) (H₂ x)) := by
    change bilinear (H₁ x) (curl (fun y => ψ y • E₂ y) x) = _
    rw [curl_real_smul ψ E₂ hψ hE₂, bilinear_add_right, bilinear_cross_cyclic,
      bilinear_real_smul_right, congrFun he₂ x, bilinear_complex_smul_right]
    ring
  have hflux : Integrable (fun x => bilinear (E₂ x) (cross (H₁ x) (complexify (scalarGradient ψ x)))) volume := by
    apply (hleft.sub (hHH.const_mul (Complex.I * (k : ℂ)))).congr
    exact ae_of_all _ (fun x => by dsimp only [Pi.sub_apply]; rw [hlpoint]; ring)
  have hl : (∫ x : Position, bilinear (H₁ x) (curl φ x)) =
      (∫ x : Position, bilinear (E₂ x) (cross (H₁ x) (complexify (scalarGradient ψ x)))) +
        (Complex.I * (k : ℂ)) * (∫ x : Position, (ψ x : ℂ) * bilinear (H₁ x) (H₂ x)) := by
    rw [← integral_const_mul, ← integral_add hflux (hHH.const_mul _)]
    exact integral_congr_ae (ae_of_all _ hlpoint)
  have hr : (∫ x : Position, bilinear (curl H₁ x) (φ x)) =
      (-Complex.I * (k : ℂ)) * (∫ x : Position, (ψ x : ℂ) * bilinear (E₁ x + p₁ x) (E₂ x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      change bilinear (curl H₁ x) (ψ x • E₂ x) = _
      rw [congrFun hh₁ x, bilinear_complex_smul_left, bilinear_real_smul_right]
      )
  exact hl.symm.trans (h.trans hr)

end OQ7Prescribed
