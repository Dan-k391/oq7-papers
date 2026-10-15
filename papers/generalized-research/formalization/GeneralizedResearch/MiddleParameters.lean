import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Parameters of the prescribed-overlap channel envelope

These are the literal rational functions in original Theorem 7.1 (arXiv
revision, `eq:middle-parameters`). No extremality statement is assumed in the
parameter hypotheses. -/

noncomputable section
namespace GeneralizedResearch

structure MiddleParameters where
  rho : ℝ
  c : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  c_pos : 0 < c
  c_lt_rho : c < rho

namespace MiddleParameters

def denominator (p : MiddleParameters) : ℝ := 2 - p.rho * p.c - p.c ^ 2
def lambda (p : MiddleParameters) : ℝ := p.c * (p.rho - p.c) / p.denominator
def s (p : MiddleParameters) : ℝ := Real.sqrt (1 - p.c ^ 2)
def r (p : MiddleParameters) : ℝ :=
  (p.rho + p.c - 2 * p.rho * p.c ^ 2) / p.denominator
def h (p : MiddleParameters) : ℝ := (1 - p.lambda ^ 2) * p.s / 2

theorem c_lt_one (p : MiddleParameters) : p.c < 1 := p.c_lt_rho.trans p.rho_lt_one

theorem c_sq_lt_one (p : MiddleParameters) : p.c ^ 2 < 1 := by
  nlinarith [p.c_pos, p.c_lt_one]

theorem rho_mul_c_lt_one (p : MiddleParameters) : p.rho * p.c < 1 := by
  have ht : p.rho * p.c < p.c := by
    simpa using mul_lt_mul_of_pos_right p.rho_lt_one p.c_pos
  exact ht.trans p.c_lt_one

theorem denominator_pos (p : MiddleParameters) : 0 < p.denominator := by
  dsimp [denominator]
  linarith [p.c_sq_lt_one, p.rho_mul_c_lt_one]

theorem lambda_pos (p : MiddleParameters) : 0 < p.lambda := by
  exact div_pos (mul_pos p.c_pos (sub_pos.mpr p.c_lt_rho)) p.denominator_pos

theorem lambda_lt_one (p : MiddleParameters) : p.lambda < 1 := by
  rw [lambda, div_lt_one p.denominator_pos]
  dsimp [denominator]
  nlinarith [p.rho_mul_c_lt_one]

theorem s_pos (p : MiddleParameters) : 0 < p.s := by
  exact Real.sqrt_pos.mpr (sub_pos.mpr p.c_sq_lt_one)

theorem s_sq (p : MiddleParameters) : p.s ^ 2 = 1 - p.c ^ 2 := by
  exact Real.sq_sqrt (sub_nonneg.mpr p.c_sq_lt_one.le)

theorem stationarity (p : MiddleParameters) :
    (p.rho - p.c) * (1 + p.lambda) * p.c =
      2 * p.lambda * (1 - p.c ^ 2) := by
  unfold lambda
  field_simp [p.denominator_pos.ne']
  dsimp [denominator]
  ring

theorem weighted_trace_value (p : MiddleParameters) :
    (p.rho + p.c) / 2 + (p.rho - p.c) / 2 * p.lambda = p.r := by
  unfold lambda r
  field_simp [p.denominator_pos.ne']
  dsimp [denominator]
  ring

theorem r_gt_half_rho (p : MiddleParameters) : p.rho / 2 < p.r := by
  rw [r, lt_div_iff₀ p.denominator_pos]
  dsimp [denominator]
  have hr : 0 < 1 - p.rho ^ 2 := by nlinarith [p.rho_pos, p.rho_lt_one]
  have hc : 0 < p.c * (1 - p.rho ^ 2) := mul_pos p.c_pos hr
  have hsmall : p.c * (p.rho - p.c) > 0 := mul_pos p.c_pos (sub_pos.mpr p.c_lt_rho)
  have hterm : 0 ≤ 3 * p.rho * (p.c * (p.rho - p.c)) := by
    exact mul_nonneg (by linarith [p.rho_pos]) hsmall.le
  nlinarith

theorem r_lt_rho (p : MiddleParameters) : p.r < p.rho := by
  rw [r, div_lt_iff₀ p.denominator_pos]
  dsimp [denominator]
  have hp : 0 < (p.rho - p.c) * (1 - p.rho * p.c) :=
    mul_pos (sub_pos.mpr p.c_lt_rho) (sub_pos.mpr p.rho_mul_c_lt_one)
  nlinarith

end MiddleParameters

/-- The derivative numerator used in the original proof is uniformly positive
throughout the closed parameter strip, including both transitions. -/
theorem derivative_numerator_pos {rho c : ℝ} (hr0 : 0 < rho) (hr1 : rho < 1)
    (hc0 : 0 ≤ c) (hcr : c ≤ rho) :
    0 < 2 + rho ^ 2 - 6 * rho * c + (1 + 2 * rho ^ 2) * c ^ 2 := by
  have hbase : 0 < 2 * (1 - rho ^ 2) ^ 2 := by
    have : 0 < 1 - rho ^ 2 := by nlinarith
    positivity
  have hcoeff : 0 ≤ 6 * rho - (1 + 2 * rho ^ 2) * (rho + c) := by
    have hr2 : rho ^ 2 < 1 := by nlinarith
    have hprod : (1 + 2 * rho ^ 2) * (rho + c) ≤
        (1 + 2 * rho ^ 2) * (2 * rho) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity
    nlinarith
  have hdiff : 0 ≤ (rho - c) *
      (6 * rho - (1 + 2 * rho ^ 2) * (rho + c)) :=
    mul_nonneg (sub_nonneg.mpr hcr) hcoeff
  nlinarith

def middleR (rho c : ℝ) : ℝ :=
  (rho + c - 2 * rho * c ^ 2) / (2 - rho * c - c ^ 2)

theorem closed_denominator_pos {rho c : ℝ} (hr0 : 0 < rho) (hr1 : rho < 1)
    (hc0 : 0 ≤ c) (hcr : c ≤ rho) : 0 < 2 - rho * c - c ^ 2 := by
  have hc1 : c < 1 := hcr.trans_lt hr1
  have hcs : c ^ 2 < 1 := by nlinarith
  have hrc : rho * c < 1 := by
    have hle : rho * c ≤ c := by
      simpa using mul_le_mul_of_nonneg_right hr1.le hc0
    linarith
  linarith

theorem middleR_zero {rho : ℝ} : middleR rho 0 = rho / 2 := by
  simp [middleR]

theorem middleR_rho {rho : ℝ} (hr0 : 0 < rho) (hr1 : rho < 1) :
    middleR rho rho = rho := by
  have hD : 2 - rho * rho - rho ^ 2 ≠ 0 :=
    (closed_denominator_pos hr0 hr1 hr0.le le_rfl).ne'
  dsimp [middleR]
  apply (div_eq_iff hD).mpr
  ring

/-- Strict monotonicity is proved by an exact divided-difference identity,
without assuming the derivative or parameter uniqueness as input. -/
theorem middleR_strictMonoOn {rho : ℝ} (hr0 : 0 < rho) (hr1 : rho < 1) :
    StrictMonoOn (middleR rho) (Set.Icc 0 rho) := by
  intro x hx y hy hxy
  have hr2 : 0 < 1 - rho ^ 2 := by nlinarith
  have hcy : 0 ≤ 3 * rho - (1 + 2 * rho ^ 2) * y := by
    have hle : (1 + 2 * rho ^ 2) * y ≤ (1 + 2 * rho ^ 2) * rho :=
      mul_le_mul_of_nonneg_left hy.2 (by positivity)
    have hp := mul_pos hr0 hr2
    nlinarith
  have hcr : 0 ≤ 3 * rho - (1 + 2 * rho ^ 2) * rho := by
    have hp := mul_pos hr0 hr2
    nlinarith
  have hbase : 0 < 2 * (1 - rho ^ 2) ^ 2 := by positivity
  have hdiff1 := mul_nonneg (sub_nonneg.mpr hx.2) hcy
  have hdiff2 := mul_nonneg (sub_nonneg.mpr hy.2) hcr
  have hcoef : 0 < 2 + rho ^ 2 - 3 * rho * (x + y) +
      (1 + 2 * rho ^ 2) * x * y := by nlinarith
  have hprod := mul_pos (sub_pos.mpr hxy) hcoef
  have hid : (rho + y - 2 * rho * y ^ 2) * (2 - rho * x - x ^ 2) -
      (rho + x - 2 * rho * x ^ 2) * (2 - rho * y - y ^ 2) =
      (y - x) * (2 + rho ^ 2 - 3 * rho * (x + y) +
        (1 + 2 * rho ^ 2) * x * y) := by ring
  dsimp [middleR]
  apply (div_lt_div_iff₀ (closed_denominator_pos hr0 hr1 hx.1 hx.2)
    (closed_denominator_pos hr0 hr1 hy.1 hy.2)).mpr
  nlinarith

#print axioms middleR_strictMonoOn

theorem middleR_continuousOn {rho : ℝ} (hr0 : 0 < rho) (hr1 : rho < 1) :
    ContinuousOn (middleR rho) (Set.Icc 0 rho) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro c hc
    exact (closed_denominator_pos hr0 hr1 hc.1 hc.2).ne'

/-- Every extinction in the open middle strip has exactly one parameter.
This proves both existence and uniqueness, rather than assuming a selected
root as part of the optimization class. -/
theorem middle_parameter_exists_unique {rho r : ℝ} (hr0 : 0 < rho)
    (hr1 : rho < 1) (hlo : rho / 2 < r) (hhi : r < rho) :
    ∃! c : ℝ, 0 < c ∧ c < rho ∧ middleR rho c = r := by
  have hcont := middleR_continuousOn hr0 hr1
  have hmem : r ∈ Set.Icc (middleR rho 0) (middleR rho rho) := by
    rw [middleR_zero, middleR_rho hr0 hr1]
    exact ⟨hlo.le, hhi.le⟩
  obtain ⟨c, hc, hvalue⟩ := intermediate_value_Icc hr0.le hcont hmem
  have hc0 : 0 < c := by
    by_contra hn
    have hzero : c = 0 := by linarith [hc.1]
    subst c
    rw [middleR_zero] at hvalue
    linarith
  have hcr : c < rho := by
    by_contra hn
    have heq : c = rho := by linarith [hc.2]
    subst c
    rw [middleR_rho hr0 hr1] at hvalue
    linarith
  refine ⟨c, ⟨hc0, hcr, hvalue⟩, ?_⟩
  intro d hd
  exact (middleR_strictMonoOn hr0 hr1).injOn
    ⟨hd.1.le, hd.2.1.le⟩ hc (hd.2.2.trans hvalue.symm)

#print axioms middleR_continuousOn
#print axioms middle_parameter_exists_unique

#print axioms MiddleParameters.denominator_pos
#print axioms MiddleParameters.stationarity
#print axioms MiddleParameters.weighted_trace_value
#print axioms MiddleParameters.r_gt_half_rho
#print axioms MiddleParameters.r_lt_rho
#print axioms derivative_numerator_pos

end GeneralizedResearch
