import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section
namespace OQ7Mission
open Filter Asymptotics
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An imaginary-part coercivity inequality implies a lower norm estimate.
This is Hilbert-space algebra, not a proof of coercivity for a Maxwell operator. -/
theorem norm_lower_bound_of_imaginary_coercivity (L : E → E) {c : ℝ}
    (hcoercive : ∀ u : E, c * ‖u‖ ^ 2 ≤ -(inner ℂ u (L u)).im) (u : E) :
    c * ‖u‖ ≤ ‖L u‖ := by
  have hup : c * ‖u‖ ^ 2 ≤ ‖u‖ * ‖L u‖ :=
    (hcoercive u).trans ((neg_le_abs _).trans
      ((RCLike.abs_im_le_norm (inner ℂ u (L u))).trans (norm_inner_le_norm u (L u))))
  by_cases hz : ‖u‖ = 0
  · simp [hz]
  · have hu : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz)
    have hh : ‖u‖ * (c * ‖u‖) ≤ ‖u‖ * ‖L u‖ := by
      simpa only [pow_two, mul_left_comm] using hup
    exact le_of_mul_le_mul_left hh hu

/-- Errors between two currents are controlled by the residual for the same
linear operator. No existence or surjectivity conclusion is asserted. -/
theorem current_error_le_residual (L : E →L[ℂ] E) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u : E, c * ‖u‖ ^ 2 ≤ -(inner ℂ u (L u)).im) (u v : E) :
    ‖u - v‖ ≤ ‖L u - L v‖ / c := by
  apply (le_div_iff₀ hc).mpr
  simpa only [map_sub, mul_comm] using
    norm_lower_bound_of_imaginary_coercivity L hcoercive (u - v)

/-- A uniform positive coercivity constant transfers a small residual to a
small current error, even when the bounded linear operator varies with the index.
The uniform constant and the residual estimate are explicit unproved premises
in any future physical application. -/
theorem current_error_isLittleO_of_uniform_coercivity {ι : Type*} {l : Filter ι}
    (L : ι → E →L[ℂ] E) (u v : ι → E) (scale : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ i u, c * ‖u‖ ^ 2 ≤ -(inner ℂ u (L i u)).im)
    (hresidual : (fun i => L i (u i) - L i (v i)) =o[l] scale) :
    (fun i => u i - v i) =o[l] scale := by
  have hb : (fun i => u i - v i) =O[l] (fun i => L i (u i) - L i (v i)) :=
    Asymptotics.IsBigO.of_bound (1 / c) (Eventually.of_forall fun i => by
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
        current_error_le_residual (L i) hc (hcoercive i) (u i) (v i))
  exact hb.trans_isLittleO hresidual

#print axioms norm_lower_bound_of_imaginary_coercivity
#print axioms current_error_le_residual
#print axioms current_error_isLittleO_of_uniform_coercivity
end OQ7Mission
