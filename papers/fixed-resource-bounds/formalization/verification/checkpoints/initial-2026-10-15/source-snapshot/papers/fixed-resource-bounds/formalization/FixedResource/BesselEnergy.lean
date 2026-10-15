import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The fixed-angular-order ODE step of the linear radiation bound. Actual
spherical Bessel functions, harmonic completeness and spectral identification
are not defined or certified here. These remaining bridges are explicit. -/
noncomputable section
namespace FixedResource.BesselEnergy
open Set Filter

def energy (L : ℝ) (u v : ℝ → ℝ) (z : ℝ) : ℝ :=
  (v z) ^ 2 + (1 - L / z ^ 2) * (u z) ^ 2

theorem energy_derivative {L z : ℝ} {u v : ℝ → ℝ} (hz : z ≠ 0)
    (hu : HasDerivAt u (v z) z)
    (hv : HasDerivAt v (-(1 - L / z ^ 2) * u z) z) :
    HasDerivAt (energy L u v) (2 * L * u z ^ 2 / z ^ 3) z := by
  have hcoef := (hasDerivAt_const z (1 : ℝ)).sub
    ((hasDerivAt_const z L).div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz))
  have h := (hv.pow 2).add (hcoef.mul (hu.pow 2))
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, id_eq]
    field_simp
    ring

theorem energy_monotone {L : ℝ} (hL : 0 ≤ L) {u v : ℝ → ℝ}
    (hu : ∀ z, 0 < z → HasDerivAt u (v z) z)
    (hv : ∀ z, 0 < z → HasDerivAt v (-(1 - L / z ^ 2) * u z) z) :
    MonotoneOn (energy L u v) (Ioi 0) := by
  have hd (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) := energy_derivative (ne_of_gt hz) (hu z hz) (hv z hz)
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(hd z (interior_subset hz)).deriv]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg _))
      (pow_nonneg (le_of_lt (interior_subset hz)) _)

theorem energy_upper {L : ℝ} (hL : 0 ≤ L) {u v : ℝ → ℝ}
    (hu : ∀ z, 0 < z → HasDerivAt u (v z) z)
    (hv : ∀ z, 0 < z → HasDerivAt v (-(1 - L / z ^ 2) * u z) z)
    (hlim : Tendsto (energy L u v) atTop (nhds 1)) {z : ℝ} (hz : 0 < z) :
    energy L u v z ≤ 1 := by
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop z] with t ht
  exact energy_monotone hL hu hv hz (lt_of_lt_of_le hz ht) ht

theorem eigenvalue_pair_bound {z E m n : ℝ} (hz : 0 ≤ z) (hE : E ≤ 1)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hsum : m + n = z * E) : m ≤ z ∧ n ≤ z := by
  have h := mul_le_mul_of_nonneg_left hE hz
  constructor <;> nlinarith

end FixedResource.BesselEnergy
