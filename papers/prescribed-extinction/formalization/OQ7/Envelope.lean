import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OQ7.ScalarEnvelope

noncomputable section

/-- The strict active branch in Theorem 5.1 of the supplied paper. -/
structure ActiveTarget (T a : ℝ) : Prop where
  transmission_pos : 0 < T
  transmission_lt_one : T < 1
  absorptance_pos : 0 < a
  absorptance_lt : a < (1 - T ^ 2) / 2

def b (T a : ℝ) : ℝ := 1 - T - a
def s (a : ℝ) : ℝ := Real.sqrt (1 - 2 * a)
def y0 (T a : ℝ) : ℝ := s a - T
def x0 (T a : ℝ) : ℝ := Real.sqrt ((b T a) ^ 2 - (y0 T a) ^ 2)
def D0 (T a : ℝ) : ℝ := 2 * x0 T a
def alpha (T a : ℝ) : ℝ := T * y0 T a / (s a * x0 T a)

/-- Positivity and strict inequalities for the paper's exact active-branch parameters. -/
theorem active_target_properties {T a : ℝ} (h : ActiveTarget T a) :
    0 < s a ∧ 0 < y0 T a ∧ y0 T a < b T a ∧
    0 < x0 T a ∧ x0 T a < b T a ∧ x0 T a < a ∧
    0 < D0 T a ∧ 0 < alpha T a := by
  have hT := h.transmission_pos
  have hTl := h.transmission_lt_one
  have ha := h.absorptance_pos
  have hal := h.absorptance_lt
  have hrad : 0 < 1 - 2 * a := by nlinarith [sq_nonneg T]
  have hs : 0 < s a := Real.sqrt_pos.2 hrad
  have hsq : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hrad.le
  have hy : 0 < y0 T a := by
    dsimp [y0]
    nlinarith
  have ha1 : a < 1 := by nlinarith [sq_nonneg T]
  have hgap : 0 < 1 - a - s a := by
    by_contra hn
    have hg : 0 ≤ s a - (1 - a) := by linarith
    have hm := mul_nonneg hg (show 0 ≤ s a + (1 - a) by linarith)
    nlinarith [sq_pos_of_pos ha]
  have hyb : y0 T a < b T a := by dsimp [b, y0]; linarith
  have hb : 0 < b T a := lt_trans hy hyb
  have hxrad : 0 < (b T a) ^ 2 - (y0 T a) ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hyb) (show 0 < b T a + y0 T a by linarith)]
  have hx : 0 < x0 T a := Real.sqrt_pos.2 hxrad
  have hxsq : (x0 T a) ^ 2 = (b T a) ^ 2 - (y0 T a) ^ 2 :=
    Real.sq_sqrt hxrad.le
  have hxb : x0 T a < b T a := by
    apply (Real.sqrt_lt hxrad.le hb.le).2
    nlinarith [sq_pos_of_pos hy]
  have hxa : x0 T a < a := by
    apply (Real.sqrt_lt hxrad.le ha.le).2
    dsimp [b, y0]
    nlinarith [mul_pos hT hgap]
  refine ⟨hs, hy, hyb, hx, hxb, hxa, ?_, ?_⟩
  · dsimp [D0]; linarith
  · exact div_pos (mul_pos hT hy) (mul_pos hs hx)

#print axioms active_target_properties

def F (T a x : ℝ) : ℝ := (Real.sqrt ((b T a) ^ 2 - x ^ 2) + T) ^ 2 - (1 - 2 * a)

/-- The target square root satisfies the exact radicand identity. -/
theorem x0_sq {T a : ℝ} (h : ActiveTarget T a) :
    (x0 T a) ^ 2 = (b T a) ^ 2 - (y0 T a) ^ 2 := by
  have hp := active_target_properties h
  have hrad : 0 ≤ (b T a) ^ 2 - (y0 T a) ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hp.2.2.1)
      (show 0 < b T a + y0 T a by linarith [hp.2.1])]
  exact Real.sq_sqrt hrad

/-- A point between zero and the target lies in the real square-root domain. -/
theorem radicand_nonneg {T a x : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxx : x ≤ x0 T a) :
    0 ≤ (b T a) ^ 2 - x ^ 2 := by
  have hp := active_target_properties h
  have hsquare := x0_sq h
  nlinarith [sq_nonneg (y0 T a),
    mul_nonneg (show 0 ≤ x0 T a - x by linarith)
      (show 0 ≤ x0 T a + x by linarith [hp.2.2.2.1])]

/-- The active-branch target is a zero of the scalar envelope. -/
theorem F_at_target {T a : ℝ} (h : ActiveTarget T a) : F T a (x0 T a) = 0 := by
  have hp := active_target_properties h
  have hsquare := x0_sq h
  have hsrad : 0 ≤ 1 - 2 * a := by nlinarith [sq_nonneg T, h.absorptance_lt]
  have hssq : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hsrad
  have hroot : Real.sqrt ((b T a) ^ 2 - (x0 T a) ^ 2) = y0 T a := by
    rw [show (b T a) ^ 2 - (x0 T a) ^ 2 = (y0 T a) ^ 2 by linarith,
      Real.sqrt_sq hp.2.1.le]
  dsimp [F]
  rw [hroot]
  dsimp [y0]
  nlinarith

/-- Exact nonnegative remainder behind the paper's scalar supporting tangent.
This is an algebraic scalar statement, not the physical Theorem 5.1. -/
theorem tangent_remainder {T a x : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxx : x ≤ x0 T a) :
    2 * s a * x0 T a * (x0 T a - x) - y0 T a * F T a x =
      y0 T a * (x0 T a - x) ^ 2 +
      T * ((x0 T a - x) ^ 2 +
        (Real.sqrt ((b T a) ^ 2 - x ^ 2) - y0 T a) ^ 2) := by
  have hysq := Real.sq_sqrt (radicand_nonneg h hx hxx)
  have hxsq := x0_sq h
  have hsrad : 0 ≤ 1 - 2 * a := by nlinarith [sq_nonneg T, h.absorptance_lt]
  have hssq : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hsrad
  dsimp [F]
  have hsy : s a = y0 T a + T := by dsimp [y0]; ring
  rw [hsy] at hssq ⊢
  have hysqmul := congrArg (fun z : ℝ => (y0 T a + T) * z) hysq
  have hxsqmul := congrArg (fun z : ℝ => (y0 T a + T) * z) hxsq
  have hssqmul := congrArg (fun z : ℝ => y0 T a * z) hssq
  nlinarith only [hysqmul, hxsqmul, hssqmul]

/-- Global scalar envelope bound on the whole active interval. -/
theorem supporting_tangent {T a x : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxx : x ≤ x0 T a) :
    y0 T a * F T a x ≤ 2 * s a * x0 T a * (x0 T a - x) := by
  have hp := active_target_properties h
  have hr := tangent_remainder h hx hxx
  have hterm1 := mul_nonneg hp.2.1.le (sq_nonneg (x0 T a - x))
  have hterm2 := mul_nonneg h.transmission_pos.le
    (add_nonneg (sq_nonneg (x0 T a - x))
      (sq_nonneg (Real.sqrt ((b T a) ^ 2 - x ^ 2) - y0 T a)))
  linarith

/-- The paper's global scalar deficit inequality (33), conditional on its
determinant-envelope bound. No physical realizability or Maxwell fact is assumed
as an axiom, and this theorem does not claim the physical Theorem 5.1. -/
theorem scalar_deficit {T a x c : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxx : x ≤ x0 T a) (_hc : 0 ≤ c)
    (hcF : T * c ≤ F T a x) :
    alpha T a * c ≤ D0 T a - 2 * x := by
  have hp := active_target_properties h
  have hden : 0 < s a * x0 T a := mul_pos hp.1 hp.2.2.2.1
  have hbound := supporting_tangent h hx hxx
  have hmul := mul_le_mul_of_nonneg_left hcF hp.2.1.le
  dsimp [alpha, D0]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Positive scalar determinant deficit forces a strict asymmetry gap. -/
theorem scalar_strict_gap {T a x c : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxx : x ≤ x0 T a) (hc : 0 < c)
    (hcF : T * c ≤ F T a x) :
    2 * x < D0 T a := by
  have hp := active_target_properties h
  have hdef := scalar_deficit h hx hxx hc.le hcF
  have hprod := mul_pos hp.2.2.2.2.2.2.2 hc
  linarith

/-- Equivalent scalar formula used in the paper's Section 5.1. -/
theorem F_alternative {T a x : ℝ} (hrad : 0 ≤ (b T a) ^ 2 - x ^ 2) :
    F T a x = a ^ 2 - x ^ 2 -
      2 * T * (b T a - Real.sqrt ((b T a) ^ 2 - x ^ 2)) := by
  have hysq := Real.sq_sqrt hrad
  dsimp [F]
  dsimp [b] at hysq ⊢
  nlinarith only [hysq]

/-- The symmetric point has scalar envelope equal to the squared mean absorption. -/
theorem F_at_zero {T a : ℝ} (h : ActiveTarget T a) : F T a 0 = a ^ 2 := by
  have hp := active_target_properties h
  have hb : 0 ≤ b T a := (lt_trans hp.2.1 hp.2.2.1).le
  have hroot : Real.sqrt ((b T a) ^ 2 - 0 ^ 2) = b T a := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using Real.sqrt_sq hb
  dsimp [F]
  rw [hroot]
  dsimp [b]
  ring

/-- Nonnegative scalar envelope forces membership in the active interval.
The initial bound `x ≤ b` is the elementary reflection-power domain. -/
theorem active_interval_of_envelope {T a x : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxb : x ≤ b T a) (hF : 0 ≤ F T a x) :
    x ≤ x0 T a := by
  have hp := active_target_properties h
  have hb : 0 < b T a := lt_trans hp.2.1 hp.2.2.1
  have hrad : 0 ≤ (b T a) ^ 2 - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxb)
      (show 0 ≤ b T a + x by linarith)]
  have hy := Real.sqrt_nonneg ((b T a) ^ 2 - x ^ 2)
  have hysq := Real.sq_sqrt hrad
  have hxsq := x0_sq h
  have hsrad : 0 ≤ 1 - 2 * a := by nlinarith [sq_nonneg T, h.absorptance_lt]
  have hssq : (s a) ^ 2 = 1 - 2 * a := Real.sq_sqrt hsrad
  have hys : s a ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) + T := by
    by_contra hn
    have hdiff : 0 < s a - (Real.sqrt ((b T a) ^ 2 - x ^ 2) + T) := by
      linarith
    have hsum : 0 < s a + (Real.sqrt ((b T a) ^ 2 - x ^ 2) + T) := by
      linarith [hp.1, h.transmission_pos]
    have hm := mul_pos hdiff hsum
    dsimp [F] at hF
    nlinarith
  have hyy : y0 T a ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) := by
    dsimp [y0]; linarith
  have hm := mul_nonneg (sub_nonneg.2 hyy)
    (show 0 ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) + y0 T a by linarith [hp.2.1])
  have hsquares : x ^ 2 ≤ (x0 T a) ^ 2 := by nlinarith
  by_contra hn
  have hm2 := mul_pos (show 0 < x - x0 T a by linarith)
    (show 0 < x + x0 T a by linarith [hp.2.2.2.1])
  nlinarith

/-- Scalar determinant bound with the active interval deduced from the envelope. -/
theorem scalar_deficit_of_envelope {T a x c : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxb : x ≤ b T a) (hc : 0 ≤ c)
    (hcF : T * c ≤ F T a x) :
    alpha T a * c ≤ D0 T a - 2 * x := by
  have hF : 0 ≤ F T a x := le_trans (mul_nonneg h.transmission_pos.le hc) hcF
  exact scalar_deficit h hx (active_interval_of_envelope h hx hxb hF) hc hcF

/-- Scalar absorption-budget feasibility needed for the paper's finite bound. -/
theorem absorption_budget {T a x beta : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxb : x ≤ b T a) (hbudget : T * beta ≤ F T a x) :
    T * beta ≤ a ^ 2 := by
  have hp := active_target_properties h
  have hb : 0 < b T a := lt_trans hp.2.1 hp.2.2.1
  have hrad : 0 ≤ (b T a) ^ 2 - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxb)
      (show 0 ≤ b T a + x by linarith)]
  have hyb : Real.sqrt ((b T a) ^ 2 - x ^ 2) ≤ b T a :=
    (Real.sqrt_le_left hb.le).2 (by nlinarith [sq_nonneg x])
  rw [F_alternative hrad] at hbudget
  have hm := mul_nonneg h.transmission_pos.le (sub_nonneg.2 hyb)
  nlinarith [sq_nonneg x]

/-- The determinant-constrained scalar bound (34) of the paper.
The input `beta` is any nonnegative scalar floor; no Maxwell floor is asserted here. -/
theorem determinant_budget_bound {T a x beta : ℝ} (h : ActiveTarget T a)
    (hx : 0 ≤ x) (hxb : x ≤ b T a) (hbeta : 0 ≤ beta)
    (hbudget : T * beta ≤ F T a x) :
    2 * x ≤ 2 * Real.sqrt ((b T a) ^ 2 -
      (Real.sqrt (1 - 2 * a + T * beta) - T) ^ 2) := by
  have hp := active_target_properties h
  have hb : 0 < b T a := lt_trans hp.2.1 hp.2.2.1
  have hrad : 0 ≤ (b T a) ^ 2 - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxb)
      (show 0 ≤ b T a + x by linarith)]
  have hy := Real.sqrt_nonneg ((b T a) ^ 2 - x ^ 2)
  have hysq := Real.sq_sqrt hrad
  have hsrad : 0 < 1 - 2 * a := by nlinarith [sq_nonneg T, h.absorptance_lt]
  have htbeta := mul_nonneg h.transmission_pos.le hbeta
  have hurad : 0 ≤ 1 - 2 * a + T * beta := by linarith
  have hu := Real.sqrt_nonneg (1 - 2 * a + T * beta)
  have husq := Real.sq_sqrt hurad
  have hsu : s a ≤ Real.sqrt (1 - 2 * a + T * beta) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hupos : 0 < Real.sqrt (1 - 2 * a + T * beta) - T := by
    dsimp [y0] at hp
    linarith [hp.2.1]
  have huy : Real.sqrt (1 - 2 * a + T * beta) ≤
      Real.sqrt ((b T a) ^ 2 - x ^ 2) + T := by
    apply (Real.sqrt_le_left (show 0 ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) + T
      by linarith [h.transmission_pos])).2
    dsimp [F] at hbudget
    linarith
  have hm := mul_nonneg
    (show 0 ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) -
      (Real.sqrt (1 - 2 * a + T * beta) - T) by linarith)
    (show 0 ≤ Real.sqrt ((b T a) ^ 2 - x ^ 2) +
      (Real.sqrt (1 - 2 * a + T * beta) - T) by linarith)
  have hxbound : x ^ 2 ≤ (b T a) ^ 2 -
      (Real.sqrt (1 - 2 * a + T * beta) - T) ^ 2 := by nlinarith
  have hxroot := Real.le_sqrt_of_sq_le hxbound
  linarith

#print axioms x0_sq
#print axioms radicand_nonneg
#print axioms F_at_target
#print axioms tangent_remainder
#print axioms supporting_tangent
#print axioms scalar_deficit
#print axioms scalar_strict_gap
#print axioms F_alternative
#print axioms F_at_zero
#print axioms active_interval_of_envelope
#print axioms scalar_deficit_of_envelope
#print axioms absorption_budget
#print axioms determinant_budget_bound

end
end OQ7.ScalarEnvelope
