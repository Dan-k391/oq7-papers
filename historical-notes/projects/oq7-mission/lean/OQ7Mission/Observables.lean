import OQ7Mission.Coercivity
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace OQ7Mission
open Filter Asymptotics
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Real bounded quadratic work. Identifying it with physical absorption and
proving positivity for the actual material operator remain separate obligations. -/
def quadraticWork (A : E →L[ℂ] E) (u : E) : ℝ := (inner ℂ u (A u)).re

/-- Imaginary incident-current work. It is not a cross section until the physical
normalization and extinction identity have been separately established. -/
def incidentWork (b u : E) : ℝ := (inner ℂ b u).im

/-- The continuity estimate for a bounded quadratic form does not require
self-adjointness or positivity. In particular it applies to a bounded positive
absorption operator after its physical interpretation is proved. -/
theorem quadraticWork_difference_bound (A : E →L[ℂ] E) (u v : E) :
    |quadraticWork A u - quadraticWork A v| ≤
      ‖A‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have he : inner ℂ u (A u) - inner ℂ v (A v) =
      inner ℂ (u - v) (A u) + inner ℂ v (A (u - v)) := by
    simp only [inner_sub_left, map_sub, inner_sub_right]
    abel
  have hb : ‖inner ℂ u (A u) - inner ℂ v (A v)‖ ≤
      ‖A‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by
    rw [he]
    calc
      ‖inner ℂ (u - v) (A u) + inner ℂ v (A (u - v))‖ ≤
          ‖inner ℂ (u - v) (A u)‖ + ‖inner ℂ v (A (u - v))‖ := norm_add_le _ _
      _ ≤ ‖u - v‖ * ‖A u‖ + ‖v‖ * ‖A (u - v)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖u - v‖ * (‖A‖ * ‖u‖) + ‖v‖ * (‖A‖ * ‖u - v‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm u) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (A.le_opNorm (u - v)) (norm_nonneg _))
      _ = _ := by ring
  exact (show |quadraticWork A u - quadraticWork A v| ≤
      ‖inner ℂ u (A u) - inner ℂ v (A v)‖ by
    simpa only [quadraticWork, RCLike.re_to_complex, Complex.sub_re] using
      RCLike.abs_re_le_norm (inner ℂ u (A u) - inner ℂ v (A v))).trans hb

theorem incidentWork_difference_bound (b u v : E) :
    |incidentWork b u - incidentWork b v| ≤ ‖b‖ * ‖u - v‖ := by
  have h := (RCLike.abs_im_le_norm (inner ℂ b (u - v))).trans
    (norm_inner_le_norm b (u - v))
  simpa only [incidentWork, inner_sub_right, RCLike.im_to_complex, Complex.sub_im] using h

/-- Current errors `o(scale)` give quadratic work errors `o(scale^2)`, for
uniformly bounded operators and currents whose norms are `O(scale)`.
No Maxwell Green operator or material observable is assumed to be constructed. -/
theorem quadraticWork_difference_isLittleO_square {ι : Type*} {l : Filter ι}
    (A : ι → E →L[ℂ] E) (u v : ι → E) (scale : ι → ℝ)
    (hA : A =O[l] (fun _ => (1 : ℝ)))
    (he : (fun i => u i - v i) =o[l] scale)
    (hu : u =O[l] scale) (hv : v =O[l] scale) :
    (fun i => quadraticWork (A i) (u i) - quadraticWork (A i) (v i))
      =o[l] (fun i => scale i ^ 2) := by
  have hm := he.norm_left.mul_isBigO (hu.norm_left.add hv.norm_left)
  have hm' := hA.norm_left.mul_isLittleO hm
  have hb : (fun i => quadraticWork (A i) (u i) - quadraticWork (A i) (v i))
      =O[l] (fun i => ‖A i‖ * (‖u i - v i‖ * (‖u i‖ + ‖v i‖))) :=
    Asymptotics.isBigO_of_le l fun i => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ ‖A i‖ * (‖u i - v i‖ * (‖u i‖ + ‖v i‖))), mul_assoc] using
          quadraticWork_difference_bound (A i) (u i) (v i)
  simpa only [one_mul, pow_two] using hb.trans_isLittleO hm'

/-- The analogous extinction-work estimate needs the incident field norm to be
`O(scale)`. It does not require a far-field operator norm estimate. -/
theorem incidentWork_difference_isLittleO_square {ι : Type*} {l : Filter ι}
    (b u v : ι → E) (scale : ι → ℝ)
    (hb : b =O[l] scale) (he : (fun i => u i - v i) =o[l] scale) :
    (fun i => incidentWork (b i) (u i) - incidentWork (b i) (v i))
      =o[l] (fun i => scale i ^ 2) := by
  have hm := hb.norm_left.mul_isLittleO he.norm_left
  have hbound : (fun i => incidentWork (b i) (u i) - incidentWork (b i) (v i))
      =O[l] (fun i => ‖b i‖ * ‖u i - v i‖) :=
    Asymptotics.isBigO_of_le l fun i => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using
        incidentWork_difference_bound (b i) (u i) (v i)
  simpa only [pow_two] using hbound.trans_isLittleO hm

/-- Explicit normalized observable convergence, including the work difference
that an independently proved optical theorem may later identify with scattering.
This theorem itself makes no radiation or cross-section assertion. -/
theorem area_normalized_work_errors_tendsto_zero {ι : Type*} {l : Filter ι}
    (A : ι → E →L[ℂ] E) (b u v : ι → E) (scale : ι → ℝ)
    (hA : A =O[l] (fun _ => (1 : ℝ)))
    (he : (fun i => u i - v i) =o[l] scale)
    (hu : u =O[l] scale) (hv : v =O[l] scale) (hb : b =O[l] scale) :
    Tendsto (fun i => (quadraticWork (A i) (u i) - quadraticWork (A i) (v i)) /
      scale i ^ 2) l (𝓝 0) ∧
    Tendsto (fun i => (incidentWork (b i) (u i) - incidentWork (b i) (v i)) /
      scale i ^ 2) l (𝓝 0) ∧
    Tendsto (fun i => ((incidentWork (b i) (u i) - quadraticWork (A i) (u i)) -
      (incidentWork (b i) (v i) - quadraticWork (A i) (v i))) / scale i ^ 2) l (𝓝 0) := by
  have hq := (quadraticWork_difference_isLittleO_square A u v scale hA he hu hv).tendsto_div_nhds_zero
  have hx := (incidentWork_difference_isLittleO_square b u v scale hb he).tendsto_div_nhds_zero
  refine ⟨hq, hx, ?_⟩
  convert hx.sub hq using 1
  · funext i
    ring
  · simp

#print axioms quadraticWork_difference_bound
#print axioms incidentWork_difference_bound
#print axioms quadraticWork_difference_isLittleO_square
#print axioms incidentWork_difference_isLittleO_square
#print axioms area_normalized_work_errors_tendsto_zero
end OQ7Mission
