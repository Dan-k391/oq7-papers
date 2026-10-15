import QuarticMaxwell.UniformBound

/-! The containing-ball form of the exact uniform bound, with its literal
`8/9` coefficient and no assumed volume-fraction or extinction floor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem volume_real_closedBall_three (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : Position) R) = 4 * Real.pi / 3 * R ^ 3 := by
  simp only [Measure.real, EuclideanSpace.volume_closedBall_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem bounded_support_volume_le (D : Set Position) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    volume.real D ≤ 4 * Real.pi / 3 * R ^ 3 := by
  have hfin : volume (Metric.closedBall (0 : Position) R) ≠ ⊤ :=
    (isCompact_closedBall (0 : Position) R).measure_ne_top
  have h := ENNReal.toReal_mono hfin (measure_mono (μ := volume) hsub)
  exact h.trans_eq (volume_real_closedBall_three R hR)

theorem bounded_support_volumeRadius_le (D : Set Position) (hV : 0 < volume.real D)
    {R : ℝ} (hR : 0 ≤ R) (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    volumeRadius (volume.real D) ≤ R := by
  have hvolume := bounded_support_volume_le D hR hsub
  have hav := volumeRadius_volume hV.le
  have hc : volumeRadius (volume.real D) ^ 3 ≤ R ^ 3 := by
    nlinarith [Real.pi_pos]
  exact (pow_le_pow_iff_left₀ (volumeRadius_pos hV).le hR (by decide : 3 ≠ 0)).mp hc

theorem quartic_coefficient_ball_bound (D : Set Position) (hV : 0 < volume.real D)
    {k R m ρ : ℝ} (_hk : 0 ≤ k) (hR : 0 ≤ R) (hm : 0 < m)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    2 / (3 * Real.pi) * ρ ^ 2 *
        (1 / m + 1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2) *
        k ^ 4 * R * volume.real D ≤
      8 / 9 * ρ ^ 2 * (1 / m + 1 + 3 / 4 * (k * R) ^ 2) * (k * R) ^ 4 := by
  have hvol := bounded_support_volume_le D hR hsub
  have hav := bounded_support_volumeRadius_le D hV hR hsub
  have hsq : volumeRadius (volume.real D) ^ 2 ≤ R ^ 2 := by
    nlinarith [volumeRadius_pos hV]
  have hL : 1 / m + 1 + 3 / 4 * k ^ 2 * volumeRadius (volume.real D) ^ 2 ≤
      1 / m + 1 + 3 / 4 * k ^ 2 * R ^ 2 := by nlinarith [sq_nonneg k]
  have hprod := mul_le_mul hL hvol hV.le
    (show 0 ≤ 1 / m + 1 + 3 / 4 * k ^ 2 * R ^ 2 by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 / (3 * Real.pi) * ρ ^ 2 * k ^ 4 * R by positivity)
  convert hscaled using 1 <;> field_simp <;> ring

namespace UniformBound
variable (D : Set Position) (hD : MeasurableSet D)
  (χ : Position → Vector →L[ℂ] Vector) (hχ : AEStronglyMeasurable χ volume)
  (M : ℝ) (hcap : ∀ᵐ x ∂volume, x ∈ D → ‖χ x‖ ≤ M)
  {m : ℝ} (hm : 0 < m)
  (hloss : ∀ᵐ x ∂volume, x ∈ D → ∀ v : Vector, m * ‖v‖ ^ 2 ≤ (inner ℂ v (χ x v)).im)

theorem uniform_ball_contrast {k : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hsym : ∀ᵐ x ∂volume, x ∈ D → ∀ u v : Vector, bilinear u (χ x v) = bilinear v (χ x u))
    (hfin : volume D ≠ ⊤) (hV : 0 < volume.real D) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1) :
    let A := VolumeInverse.equiv D hD χ hχ M hcap hm hloss hk hM hfin hR hsub
    let W := VolumeInverse.inverseSusceptibility D hD χ hχ M hcap hm hloss
    let f := domainIncidentSource k n e D hD hfin
    let g := domainIncidentSource (-k) n e D hD hfin
    let X := extinctionPower k A f
    0 < X ∧
      |absorptionPower k W (A.symm f) - absorptionPower k W (A.symm g)| / X ≤
        min 1 (8 / 9 * (M ^ 2 / m) ^ 2 * (1 / m + 1 + 3 / 4 * (k * R) ^ 2) * (k * R) ^ 4) := by
  have h := uniform_quartic_contrast D hD χ hχ M hcap hm hloss hk hM hsym hfin hV hR hsub n e he hen
  exact ⟨h.1, h.2.trans (min_le_min_left 1 (quartic_coefficient_ball_bound D hV hk.le hR hm hsub))⟩

end UniformBound
end QuarticMaxwell
