import GeneralizedResearch.CanonicalParabola
import GeneralizedResearch.OuterBound

/-! # Complete three-branch canonical envelope

The middle parameter is selected only after its existence and uniqueness have
been proved. Every upper-bound hypothesis is an actual PSD/symmetry/target
constraint on competing matrices. -/
noncomputable section
open scoped Matrix
namespace GeneralizedResearch

structure OverlapParameters where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1

namespace OverlapParameters

def d (p : OverlapParameters) : ℝ := Real.sqrt (1 - p.rho ^ 2)
def inputP (p : OverlapParameters) : ℝ := Real.sqrt ((1 + p.rho) / 2)
def inputQ (p : OverlapParameters) : ℝ := Real.sqrt ((1 - p.rho) / 2)
def W (p : OverlapParameters) : Mat2 :=
  !![(1 + p.rho) / 2, 0; 0, -(1 - p.rho) / 2]

theorem d_pos (p : OverlapParameters) : 0 < p.d := by
  apply Real.sqrt_pos.mpr
  nlinarith [p.rho_pos, p.rho_lt_one]
theorem d_sq (p : OverlapParameters) : p.d ^ 2 = 1 - p.rho ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [p.rho_pos, p.rho_lt_one]
theorem inputP_pos (p : OverlapParameters) : 0 < p.inputP := by
  apply Real.sqrt_pos.mpr
  linarith [p.rho_pos]
theorem inputQ_pos (p : OverlapParameters) : 0 < p.inputQ := by
  apply Real.sqrt_pos.mpr
  linarith [p.rho_lt_one]
theorem inputP_sq (p : OverlapParameters) : p.inputP ^ 2 = (1 + p.rho) / 2 :=
  Real.sq_sqrt (by linarith [p.rho_pos])
theorem inputQ_sq (p : OverlapParameters) : p.inputQ ^ 2 = (1 - p.rho) / 2 :=
  Real.sq_sqrt (by linarith [p.rho_lt_one])
theorem input_unit (p : OverlapParameters) : p.inputP ^ 2 + p.inputQ ^ 2 = 1 := by
  rw [p.inputP_sq, p.inputQ_sq]
  ring
theorem input_product (p : OverlapParameters) : 2 * p.inputP * p.inputQ = p.d := by
  have h1 := congrArg (fun z : ℝ => z * p.inputP ^ 2) p.inputQ_sq
  have h2 := congrArg (fun z : ℝ => z * ((1 - p.rho) / 2)) p.inputP_sq
  have hs : (2 * p.inputP * p.inputQ) ^ 2 = p.d ^ 2 := by
    nlinarith [p.d_sq, h1, h2]
  have hn : 0 < 2 * p.inputP * p.inputQ := by
    have hp := p.inputP_pos
    have hq := p.inputQ_pos
    positivity
  nlinarith [p.d_pos]

def middle (p : OverlapParameters) (r : ℝ) (h : p.rho / 2 < r ∧ r < p.rho) :
    MiddleParameters where
  rho := p.rho
  c := Classical.choose (middle_parameter_exists_unique p.rho_pos p.rho_lt_one h.1 h.2)
  rho_pos := p.rho_pos
  rho_lt_one := p.rho_lt_one
  c_pos := (Classical.choose_spec
    (middle_parameter_exists_unique p.rho_pos p.rho_lt_one h.1 h.2)).1.1
  c_lt_rho := (Classical.choose_spec
    (middle_parameter_exists_unique p.rho_pos p.rho_lt_one h.1 h.2)).1.2.1

theorem middle_r (p : OverlapParameters) (r : ℝ) (h : p.rho / 2 < r ∧ r < p.rho) :
    (p.middle r h).r = r := by
  exact (Classical.choose_spec
    (middle_parameter_exists_unique p.rho_pos p.rho_lt_one h.1 h.2)).1.2.2

def envelope (p : OverlapParameters) (r : ℝ) : ℝ :=
  if h₁ : r ≤ p.rho / 2 then p.d
  else if h₂ : r < p.rho then
    2 * p.d * (p.middle r ⟨lt_of_not_ge h₁, h₂⟩).h
  else 1 - r ^ 2

theorem middle_abs_target_bound (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : |(p.canonicalW * A).trace| = p.r) : |Q 0 1| ≤ p.h := by
  by_cases hpos : 0 ≤ (p.canonicalW * A).trace
  · rw [abs_of_nonneg hpos] at htarget
    exact p.canonical_middle_abs_bound A Q hA hQ hrelax hcontract htarget
  · have hneg : (p.canonicalW * A).trace < 0 := lt_of_not_ge hpos
    rw [abs_of_neg hneg] at htarget
    have hnegA : (-A).IsHermitian := hA.neg
    have hnegR : (Q - (-A) ^ 2).PosSemidef := by simpa using hrelax
    have hnegT : (p.canonicalW * (-A)).trace = p.r := by
      simpa using htarget
    exact p.canonical_middle_abs_bound (-A) Q hnegA hQ hnegR hcontract hnegT

theorem canonical_parabola_bound (p : OverlapParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (r : ℝ) (htarget : |(p.W * A).trace| = r) :
    2 * p.d * |Q 0 1| ≤ 1 - r ^ 2 := by
  have hW : (p.W * A).trace = p.inputP ^ 2 * A 0 0 - p.inputQ ^ 2 * A 1 1 := by
    rw [p.inputP_sq, p.inputQ_sq]
    simp [W, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  have hb := CanonicalParabola.canonical_parabola A Q hA hQ hrelax hcontract
    p.inputP p.inputQ (p.W * A).trace p.input_unit hW.symm
  have hscaled : 4 * p.inputP * p.inputQ * Q 0 1 = (2 * p.d) * Q 0 1 := by
    calc
      _ = 2 * (2 * p.inputP * p.inputQ) * Q 0 1 := by ring
      _ = _ := by rw [p.input_product]
  rw [hscaled, abs_mul, abs_of_pos (mul_pos (by norm_num) p.d_pos)] at hb
  have hsq : (p.W * A).trace ^ 2 = r ^ 2 := by
    have h := congrArg (fun z : ℝ => z ^ 2) htarget
    simpa using h
  rwa [hsq] at hb

/-- All three branches, including both endpoints and both sign choices of
the extinction overlap, for the literal canonical matrix relaxation. -/
theorem all_branches_upper_bound (p : OverlapParameters) (r : ℝ)
    (A Q : Mat2) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : |(p.W * A).trace| = r) :
    2 * p.d * |Q 0 1| ≤ p.envelope r := by
  unfold envelope
  split_ifs with h₁ h₂
  · have hAsq : (A ^ 2).PosSemidef := by
      simpa only [pow_two, hA.eq] using Matrix.posSemidef_conjTranspose_mul_self A
    have hQpos : Q.PosSemidef := by
      have hsum := hAsq.add hrelax
      have hid : A ^ 2 + (Q - A ^ 2) = Q := by abel
      rwa [hid] at hsum
    have hhalf := OuterBound.abs_offdiag_le_half Q hQpos hcontract
    nlinarith [p.d_pos]
  · let m := p.middle r ⟨lt_of_not_ge h₁, h₂⟩
    have htargetm : |(m.canonicalW * A).trace| = m.r := by
      rw [p.middle_r]
      exact htarget
    have hbound := middle_abs_target_bound m A Q hA hQ hrelax hcontract htargetm
    exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by norm_num) p.d_pos.le)
  · exact p.canonical_parabola_bound A Q hA hQ hrelax hcontract r htarget

theorem envelope_at_zero (p : OverlapParameters) : p.envelope 0 = p.d := by
  have h0 : 0 ≤ p.rho / 2 := by linarith [p.rho_pos]
  simp [envelope, h0]

theorem envelope_at_first_transition (p : OverlapParameters) :
    p.envelope (p.rho / 2) = p.d := by simp [envelope]

theorem envelope_at_second_transition (p : OverlapParameters) :
    p.envelope p.rho = 1 - p.rho ^ 2 := by
  have hnot : ¬p.rho ≤ p.rho / 2 := by linarith [p.rho_pos]
  simp [envelope, hnot]

theorem envelope_at_one (p : OverlapParameters) : p.envelope 1 = 0 := by
  have hnot : ¬(1 : ℝ) ≤ p.rho / 2 := by linarith [p.rho_lt_one]
  have hnot2 : ¬(1 : ℝ) < p.rho := not_lt.mpr p.rho_lt_one.le
  simp [envelope, hnot, hnot2]

def middleCurve (p : OverlapParameters) (c : ℝ) : ℝ :=
  p.d * (1 - (c * (p.rho - c) / (2 - p.rho * c - c ^ 2)) ^ 2) *
    Real.sqrt (1 - c ^ 2)

theorem middleCurve_continuousOn (p : OverlapParameters) :
    ContinuousOn p.middleCurve (Set.Icc 0 p.rho) := by
  have hl : ContinuousOn
      (fun c : ℝ => c * (p.rho - c) / (2 - p.rho * c - c ^ 2))
      (Set.Icc 0 p.rho) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro c hc
      exact (closed_denominator_pos p.rho_pos p.rho_lt_one hc.1 hc.2).ne'
  have hs : ContinuousOn (fun c : ℝ => Real.sqrt (1 - c ^ 2)) (Set.Icc 0 p.rho) := by
    fun_prop
  exact (continuousOn_const.mul (continuousOn_const.sub (hl.pow 2))).mul hs

theorem middleCurve_first_transition (p : OverlapParameters) :
    p.middleCurve 0 = p.d := by simp [middleCurve]

theorem middleCurve_second_transition (p : OverlapParameters) :
    p.middleCurve p.rho = 1 - p.rho ^ 2 := by
  simpa [middleCurve, d, pow_two] using p.d_sq

theorem middleCurve_matches_middle (p : OverlapParameters) (r : ℝ)
    (h : p.rho / 2 < r ∧ r < p.rho) :
    p.middleCurve (p.middle r h).c = 2 * p.d * (p.middle r h).h := by
  simp [middleCurve, MiddleParameters.h, MiddleParameters.lambda,
    MiddleParameters.denominator, MiddleParameters.s, middle]
  ring

#print axioms middle_r
#print axioms all_branches_upper_bound
#print axioms middleCurve_continuousOn

end OverlapParameters
end GeneralizedResearch
