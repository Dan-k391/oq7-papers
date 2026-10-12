import PrescribedExtinction.PoyntingCutoff

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace OQ7Prescribed
open MeasureTheory

theorem bilinear_cross_cycle (u v w : Vector) : bilinear u (cross v w) = bilinear (cross u v) w := by
  simp [bilinear, cross, Fin.sum_univ_three]
  ring

theorem cross_antisymm (u v : Vector) : cross u v = -cross v u := by
  ext i
  fin_cases i <;> simp [cross, PiLp.neg_apply] <;> ring

theorem bilinear_cross_skew (u v w : Vector) :
    bilinear (cross u v) w = -bilinear v (cross u w) := by
  simp [bilinear, cross, Fin.sum_univ_three]
  ring

theorem bilinear_real_smul_swap (a : ℝ) (u v : Vector) :
    bilinear (a • u) v = bilinear u (a • v) := by
  simp [bilinear, PiLp.smul_apply, Complex.real_smul, mul_left_comm, mul_assoc, mul_comm]

theorem cross_continuous_fields (F G : Field) (hF : Continuous F) (hG : Continuous G) :
    Continuous (fun x => cross (F x) (G x)) := by
  unfold cross
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro i
  have hf (j : Fin 3) : Continuous (fun x => F x j) := (vectorCoordinate j).continuous.comp hF
  have hg (j : Fin 3) : Continuous (fun x => G x j) := (vectorCoordinate j).continuous.comp hG
  fin_cases i
  · exact ((hf 1).mul (hg 2)).sub ((hf 2).mul (hg 1))
  · exact ((hf 2).mul (hg 0)).sub ((hf 0).mul (hg 2))
  · exact ((hf 0).mul (hg 1)).sub ((hf 1).mul (hg 0))

theorem scalarGradient_contDiff (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarGradient ψ) := by
  unfold scalarGradient
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro j
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const

theorem cross_compactSupport_right (F G : Field) (hG : HasCompactSupport G) :
    HasCompactSupport (fun x => cross (F x) (G x)) := by
  apply hG.mono
  intro x hx
  by_contra hn
  have hz : G x = 0 := not_not.mp hn
  exact hx (by simp [hz, cross])

/-- Compact scalar multiplication rule for genuine weak curl fields. Only
the test function is differentiated; no regularity of the weak field is assumed. -/
theorem HasWeakCurl.real_smul_field (F G : Field) (hF : LocallyIntegrable F volume)
    (hG : LocallyIntegrable G volume) (hcurl : HasWeakCurl F G)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    HasWeakCurl (fun x => ψ x • F x)
      (fun x => cross (complexify (scalarGradient ψ x)) (F x) + ψ x • G x) := by
  intro φ hφ hsφ
  let V : Field := fun x => cross (complexify (scalarGradient ψ x)) (φ x)
  have hV : Continuous V := cross_continuous_fields _ _
    (complexify_continuous.comp (scalarGradient_contDiff ψ hψ).continuous) hφ.continuous
  have hsV : HasCompactSupport V := cross_compactSupport_right _ _ hsφ
  have hψφ : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x • φ x) := hψ.smul hφ
  have hsψφ : HasCompactSupport (fun x => ψ x • φ x) := hsφ.smul_left (f := ψ)
  have hdφ := smoothField_curl_continuous φ hφ
  have hsdf := compactField_curl_hasCompactSupport φ hsφ
  have hleft := compactField_bilinear_integrable F hF (fun x => ψ x • curl φ x)
    (hψ.continuous.smul hdφ) (hsdf.smul_left (f := ψ))
  have hcross := compactField_bilinear_integrable F hF V hV hsV
  have hright := compactField_bilinear_integrable G hG (fun x => ψ x • φ x)
    hψφ.continuous hsψφ
  have hc := hcurl (fun x => ψ x • φ x) hψφ hsψφ
  simp_rw [curl_real_smul ψ φ hψ hφ, bilinear_add_right] at hc
  rw [integral_add hcross hleft] at hc
  have hpoint (x : Position) :
      bilinear (cross (complexify (scalarGradient ψ x)) (F x) + ψ x • G x) (φ x) =
        bilinear (G x) (ψ x • φ x) - bilinear (F x) (V x) := by
    rw [bilinear_add_left, bilinear_cross_skew, bilinear_real_smul_swap]
    change -bilinear (F x) (V x) + bilinear (G x) (ψ x • φ x) = _
    abel
  have hleftpoint (x : Position) : bilinear (ψ x • F x) (curl φ x) =
      bilinear (F x) (ψ x • curl φ x) := by
    exact bilinear_real_smul_swap _ _ _
  simp_rw [hpoint, hleftpoint]
  rw [integral_sub hright hcross]
  linear_combination hc

theorem HasWeakCurl.sub_fields {F1 F2 G1 G2 : Field}
    (h1 : HasWeakCurl F1 G1) (h2 : HasWeakCurl F2 G2)
    (hF1 : LocallyIntegrable F1 volume) (hF2 : LocallyIntegrable F2 volume)
    (hG1 : LocallyIntegrable G1 volume) (hG2 : LocallyIntegrable G2 volume) :
    HasWeakCurl (F1 - F2) (G1 - G2) := by
  intro φ hφ hsφ
  have hf1 := compactField_bilinear_integrable F1 hF1 (curl φ)
    (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hf2 := compactField_bilinear_integrable F2 hF2 (curl φ)
    (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hg1 := compactField_bilinear_integrable G1 hG1 φ hφ.continuous hsφ
  have hg2 := compactField_bilinear_integrable G2 hG2 φ hφ.continuous hsφ
  have hsub (u v w : Vector) : bilinear (u - v) w = bilinear u w - bilinear v w := by
    simp [bilinear, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp_rw [Pi.sub_apply, hsub]
  rw [integral_sub hf1 hf2, integral_sub hg1 hg2, h1 φ hφ hsφ, h2 φ hφ hsφ]

end OQ7Prescribed
