import OQ7.PhysicalCoreRemainder
import OQ7.CoreFluxPolynomial
import OQ7.ScaledRemainder
import OQ7.ResourceBounds
import OQ7.PhysicalCoatings
import OQ7.MatrixNormBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7.CoreConstruction
open Filter Asymptotics
open scoped Topology Matrix Matrix.Norms.Operator

theorem actual_repeatedCore_scaledDifference_tendsto {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 •
      (strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M)))
      atTop (𝓝 (coreJ P Q (k * M))) := by
  obtain ⟨C, hC, hb⟩ := actual_repeatedCore_quartic_remainder_norm_bound hP hQ k M
  apply tendsto_scaled_quartic_remainder (C := C)
  filter_upwards [hb] with m hm
  simpa only [matrix_reciprocalPower_smul_eq_real] using hm

theorem actual_repeatedCore_tendsto {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    Tendsto (fun m : ℕ => strippedCellTransfer k P Q M m ^ m)
      atTop (𝓝 (limitingSheet (k * M))) :=
  tendsto_of_scaled_square_difference (actual_repeatedCore_scaledDifference_tendsto hP hQ k M)

theorem actual_repeatedCore_operatorNorm_tendsto {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    Tendsto (fun m : ℕ => matrixOperatorNorm
      (strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M))) atTop (𝓝 0) := by
  have h := (actual_repeatedCore_tendsto hP hQ k M).sub_const (limitingSheet (k * M))
  simpa only [matrixOperatorNorm, sub_self, norm_zero] using h.norm

theorem actual_repeatedCore_operatorNorm_isBigO {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    (fun m : ℕ => matrixOperatorNorm
      (strippedCellTransfer k P Q M m ^ m - limitingSheet (k * M)))
      =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
  have h := isBigO_of_scaled_square_difference
    (actual_repeatedCore_scaledDifference_tendsto hP hQ k M)
  simpa only [matrixOperatorNorm] using h.norm_left

theorem actual_repeatedCore_scaledFluxDeterminant_complex_tendsto {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ 2 : ℝ) : ℂ) *
      (fluxDefect (strippedCellTransfer k P Q M m ^ m)).det)
      atTop (𝓝 (((k * M : ℝ) : ℂ) ^ 4 / (3 * (Q : ℂ) ^ 2))) := by
  have h := limitingSheet_scaledFluxDeterminant_tendsto
    (actual_repeatedCore_tendsto hP hQ k M)
    (actual_repeatedCore_scaledDifference_tendsto hP hQ k M)
  rw [core_linear_determinant_coefficient hQ] at h
  exact h

theorem actual_repeatedCore_scaledFluxDeterminant_tendsto {P Q : ℝ}
    (hP : 1 ≤ P) (hQ : Q ≠ 0) (k M : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      (fluxDefect (strippedCellTransfer k P Q M m ^ m)).det.re)
      atTop (𝓝 ((k * M) ^ 4 / (3 * Q ^ 2))) := by
  have hc : ((k * M : ℝ) : ℂ) ^ 4 / (3 * (Q : ℂ) ^ 2) =
      (((k * M) ^ 4 / (3 * Q ^ 2) : ℝ) : ℂ) := by push_cast; rfl
  have h := (Complex.continuous_re.tendsto _).comp
    (actual_repeatedCore_scaledFluxDeterminant_complex_tendsto hP hQ k M)
  rw [hc] at h
  simpa only [Function.comp_def, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The coefficient is proved for the actual finite-layer core, including its quarter-wave ends. -/
theorem physicalUnmatchedCore_scaledFluxDeterminant_tendsto {k P Q : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : Q ≠ 0) (M : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      (fluxDefect (stackTransfer k (physicalUnmatchedCore k P Q M m))).det.re)
      atTop (𝓝 ((k * M) ^ 4 / (3 * Q ^ 2))) := by
  have h := actual_repeatedCore_scaledFluxDeterminant_tendsto hP hQ k M
  exact h.congr (fun m => by rw [physicalUnmatchedCore_transferFactorization hk
    (by linarith : 0 < P), signPow_fluxDefect])

/-- This is the native scattering invariant of an eventually admissible original physical core. -/
theorem physicalUnmatchedCore_scaledResourceInvariant_tendsto {k P Q M : ℝ}
    (hk : 0 < k) (hP : 1 < P) (hQ : 0 < Q) (hM : 0 < M) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      stackResourceInvariant k (physicalUnmatchedCore k P Q M m))
      atTop (𝓝 ((k * M) ^ 4 / (3 * Q ^ 2))) := by
  have h := physicalUnmatchedCore_scaledFluxDeterminant_tendsto hk hP.le hQ.ne' M
  apply h.congr'
  filter_upwards [physicalUnmatchedCore_eventually_admissible hk hP hQ hM] with m hm
  rw [stackResourceInvariant_eq_fluxDefect hk hm.1]

theorem physicallyCoated_fluxDeterminant {k : ℝ} (hk : 0 < k) (P ℓL ℓR : ℝ)
    {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR) (core : List HomogeneousLayer) :
    (fluxDefect (stackTransfer k
      (coatingLayers k P ℓL jL ++ core ++ coatingLayers k P ℓR jR))).det =
        (fluxDefect (stackTransfer k core)).det := by
  rw [physicallyCoated_transfer hk P ℓL ℓR hjL hjR, signPow_fluxDefect]
  exact coated_fluxDefect_det _ _ _ (losslessDiagonalScale_flux_preserving ℓL)
    (losslessDiagonalScale_flux_preserving ℓR) (losslessDiagonalScale_det ℓL)

theorem physicallyCoatedCore_scaledFluxDeterminant_tendsto {k P Q : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : Q ≠ 0) (M : ℝ)
    (ℓL ℓR : ℕ → ℝ) {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (fluxDefect (stackTransfer k
      (coatingLayers k P (ℓL m) jL ++ physicalUnmatchedCore k P Q M m ++
        coatingLayers k P (ℓR m) jR))).det.re)
      atTop (𝓝 ((k * M) ^ 4 / (3 * Q ^ 2))) := by
  have h := physicalUnmatchedCore_scaledFluxDeterminant_tendsto hk hP hQ M
  exact h.congr (fun m => by rw [physicallyCoated_fluxDeterminant hk P (ℓL m) (ℓR m) hjL hjR])

/-- Any eventually admissible physical coating sequence preserves the native invariant coefficient. -/
theorem physicallyCoatedCore_scaledResourceInvariant_tendsto {k P Q : ℝ}
    (hk : 0 < k) (hP : 1 ≤ P) (hQ : Q ≠ 0) (M : ℝ)
    (ℓL ℓR : ℕ → ℝ) {jL jR : ℕ} (hjL : 0 < jL) (hjR : 0 < jR)
    (hphysical : ∀ᶠ m : ℕ in atTop, StackAdmissible P Q
      (coatingLayers k P (ℓL m) jL ++ physicalUnmatchedCore k P Q M m ++
        coatingLayers k P (ℓR m) jR)) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * stackResourceInvariant k
      (coatingLayers k P (ℓL m) jL ++ physicalUnmatchedCore k P Q M m ++
        coatingLayers k P (ℓR m) jR))
      atTop (𝓝 ((k * M) ^ 4 / (3 * Q ^ 2))) := by
  have h := physicallyCoatedCore_scaledFluxDeterminant_tendsto hk hP hQ M ℓL ℓR hjL hjR
  apply h.congr'
  filter_upwards [hphysical] with m hm
  rw [stackResourceInvariant_eq_fluxDefect hk hm]

#print axioms actual_repeatedCore_scaledDifference_tendsto
#print axioms actual_repeatedCore_tendsto
#print axioms actual_repeatedCore_operatorNorm_tendsto
#print axioms actual_repeatedCore_operatorNorm_isBigO
#print axioms actual_repeatedCore_scaledFluxDeterminant_complex_tendsto
#print axioms actual_repeatedCore_scaledFluxDeterminant_tendsto
#print axioms physicalUnmatchedCore_scaledFluxDeterminant_tendsto
#print axioms physicalUnmatchedCore_scaledResourceInvariant_tendsto
#print axioms physicallyCoated_fluxDeterminant
#print axioms physicallyCoatedCore_scaledFluxDeterminant_tendsto
#print axioms physicallyCoatedCore_scaledResourceInvariant_tendsto
end OQ7.CoreConstruction
