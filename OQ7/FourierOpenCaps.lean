import OQ7.FourierTriangle

noncomputable section
namespace OQ7
open Set MeasureTheory

/-- Single endpoint values do not restrict the capped Fourier theorem. -/
theorem capped_fourier_moment_Ioo {q : ℝ → ℝ} {a b K Q : ℝ}
    (hab : a ≤ b) (hK : 0 < K) (hQ : 0 < Q)
    (hlength : b - a ≤ Real.pi / K) (hq : IntervalIntegrable q volume a b)
    (hcap : ∀ z ∈ Ioo a b, 0 ≤ q z ∧ q z ≤ Q) :
    ‖∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)‖ ≤
      Q / K * Real.sin (K * (∫ z in a..b, q z) / Q) := by
  classical
  let qc : ℝ → ℝ := (Ioo a b).indicator q
  have heq : EqOn q qc (Ioo a b) := by
    intro z hz
    simp [qc, hz]
  have hqi : IntervalIntegrable qc volume a b :=
    hq.congr_uIoo (by simpa only [uIoo_of_le hab] using heq)
  have hcapc : ∀ z ∈ Icc a b, 0 ≤ qc z ∧ qc z ≤ Q := by
    intro z _
    by_cases hz : z ∈ Ioo a b
    · simpa [qc, hz] using hcap z hz
    · simp [qc, hz, hQ.le]
  have hc := capped_fourier_moment hab hK hQ hlength hqi hcapc
  have hmass : (∫ z in a..b, q z) = ∫ z in a..b, qc z :=
    intervalIntegral.integral_congr_Ioo_of_le hab heq
  have hmoment : (∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)) =
      ∫ z in a..b, (qc z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro z hz
    dsimp only
    rw [heq hz]
  rwa [← hmass, ← hmoment] at hc

theorem sineSquare_triangleIntegral_capped_Ioo {q : ℝ → ℝ} {a b K Q : ℝ}
    (hab : a ≤ b) (hK : 0 < K) (hQ : 0 < Q)
    (hlength : b - a ≤ Real.pi / K)
    (hq : IntervalIntegrable q volume a b)
    (hcap : ∀ z ∈ Ioo a b, 0 ≤ q z ∧ q z ≤ Q) :
    Q ^ 2 / (4 * K ^ 2) *
      ((K * (∫ z in a..b, q z) / Q) ^ 2 -
        Real.sin (K * (∫ z in a..b, q z) / Q) ^ 2) ≤
      ∫ p in {p : ℝ × ℝ | p.1 < p.2},
        q p.1 * q p.2 * Real.sin (K * (p.2 - p.1)) ^ 2
        ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)) := by
  let m : ℝ := ∫ z in a..b, q z
  let M : ℂ := ∫ z in a..b, (q z : ℂ) * Complex.exp ((2 * K * z : ℝ) * Complex.I)
  have hb := capped_fourier_moment_Ioo hab hK hQ hlength hq hcap
  change ‖M‖ ≤ Q / K * Real.sin (K * m / Q) at hb
  have hr : 0 ≤ Q / K * Real.sin (K * m / Q) := (norm_nonneg M).trans hb
  have hs := (sq_le_sq₀ (norm_nonneg M) hr).mpr hb
  rw [← Complex.normSq_eq_norm_sq] at hs
  rw [sineSquare_triangleIntegral_fourier hab hq]
  change Q ^ 2 / (4 * K ^ 2) * ((K * m / Q) ^ 2 - Real.sin (K * m / Q) ^ 2) ≤
    (m ^ 2 - Complex.normSq M) / 4
  have heq : Q ^ 2 / (4 * K ^ 2) *
      ((K * m / Q) ^ 2 - Real.sin (K * m / Q) ^ 2) =
      (m ^ 2 - (Q / K * Real.sin (K * m / Q)) ^ 2) / 4 := by
    field_simp
  rw [heq]
  linarith

#print axioms capped_fourier_moment_Ioo
#print axioms sineSquare_triangleIntegral_capped_Ioo
end OQ7
