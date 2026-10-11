import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace OQ7

/-- The exact sum of single insertions, expressed recursively without any commutativity. -/
def firstInsertion {A : Type*} [Ring A] (a w : A) : ℕ → A
  | 0 => 0
  | n + 1 => a * firstInsertion a w n + w * a ^ n

def insertionError {A : Type*} [Ring A] (a w : A) (n : ℕ) : A :=
  (a + w) ^ n - a ^ n - firstInsertion a w n

theorem insertionError_zero {A : Type*} [Ring A] (a w : A) : insertionError a w 0 = 0 := by
  simp [insertionError, firstInsertion]

theorem insertionError_succ {A : Type*} [Ring A] (a w : A) (n : ℕ) :
    insertionError a w (n + 1) =
      (a + w) * insertionError a w n + w * firstInsertion a w n := by
  simp only [insertionError, firstInsertion, pow_succ']
  noncomm_ring

theorem norm_firstInsertion_le {A : Type*} [NormedRing A] [NormOneClass A]
    (a w : A) {R : ℝ} (hR : 1 ≤ R) (ha : ‖a‖ ≤ R) (n : ℕ) :
    ‖firstInsertion a w n‖ ≤ (n : ℝ) * ‖w‖ * R ^ n := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  induction n with
  | zero => simp [firstInsertion]
  | succ n ih =>
    have hpow : ‖a ^ n‖ ≤ R ^ n := (norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) ha n)
    calc
      ‖firstInsertion a w (n + 1)‖ ≤ ‖a‖ * ‖firstInsertion a w n‖ + ‖w‖ * ‖a ^ n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ R * ((n : ℝ) * ‖w‖ * R ^ n) + ‖w‖ * R ^ n := by gcongr
      _ ≤ (n + 1 : ℝ) * ‖w‖ * R ^ (n + 1) := by
        rw [pow_succ R n]
        have hb := mul_le_mul_of_nonneg_right hR (mul_nonneg (norm_nonneg w) (pow_nonneg hR0 n))
        nlinarith
      _ = ((n + 1 : ℕ) : ℝ) * ‖w‖ * R ^ (n + 1) := by simp

/-- A quadratic double-insertion remainder; `R^n` is harmless when `R=1+C/n`.
The loose `n^2/2` coefficient preserves the fourth-order repeated-cell remainder. -/
theorem norm_insertionError_le {A : Type*} [NormedRing A] [NormOneClass A]
    (a w : A) {R : ℝ} (hR : 1 ≤ R) (ha : ‖a‖ ≤ R) (had : ‖a + w‖ ≤ R) (n : ℕ) :
    ‖insertionError a w n‖ ≤ (n : ℝ) ^ 2 / 2 * ‖w‖ ^ 2 * R ^ n := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  induction n with
  | zero => simp [insertionError_zero]
  | succ n ih =>
    rw [insertionError_succ]
    calc
      ‖(a + w) * insertionError a w n + w * firstInsertion a w n‖ ≤
          ‖a + w‖ * ‖insertionError a w n‖ + ‖w‖ * ‖firstInsertion a w n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ R * ((n : ℝ) ^ 2 / 2 * ‖w‖ ^ 2 * R ^ n) +
          ‖w‖ * ((n : ℝ) * ‖w‖ * R ^ n) := by
        gcongr
        exact norm_firstInsertion_le a w hR ha n
      _ ≤ ((n : ℝ) + 1) ^ 2 / 2 * ‖w‖ ^ 2 * R ^ (n + 1) := by
        rw [pow_succ R n]
        have hb := mul_le_mul_of_nonneg_right hR
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg ‖w‖)) (pow_nonneg hR0 n))
        have hz := mul_nonneg (mul_nonneg (sq_nonneg ‖w‖) (pow_nonneg hR0 n)) hR0
        nlinarith
      _ = (((n + 1 : ℕ) : ℝ)) ^ 2 / 2 * ‖w‖ ^ 2 * R ^ (n + 1) := by simp

#print axioms insertionError_zero

theorem one_add_div_pow_le_exp {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n) :
    (1 + C / (n : ℝ)) ^ n ≤ Real.exp C := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnonneg : 0 ≤ 1 + C / (n : ℝ) := by positivity
  have hex : 1 + C / (n : ℝ) ≤ Real.exp (C / (n : ℝ)) := by
    simpa only [add_comm] using Real.add_one_le_exp (C / (n : ℝ))
  have hb := pow_le_pow_left₀ hnonneg hex n
  have he : (Real.exp (C / (n : ℝ))) ^ n = Real.exp C := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  simpa only [add_comm, he] using hb

theorem norm_insertionError_le_exp {A : Type*} [NormedRing A] [NormOneClass A]
    (a w : A) {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n)
    (ha : ‖a‖ ≤ 1 + C / (n : ℝ)) (had : ‖a + w‖ ≤ 1 + C / (n : ℝ)) :
    ‖insertionError a w n‖ ≤ (n : ℝ) ^ 2 / 2 * ‖w‖ ^ 2 * Real.exp C := by
  have hR : 1 ≤ 1 + C / (n : ℝ) := le_add_of_nonneg_right (div_nonneg hC (Nat.cast_nonneg n))
  exact (norm_insertionError_le a w hR ha had n).trans
    (mul_le_mul_of_nonneg_left (one_add_div_pow_le_exp hC hn) (by positivity))

theorem norm_insertionError_quartic {A : Type*} [NormedRing A] [NormOneClass A]
    (a w : A) {C Cw : ℝ} (hC : 0 ≤ C) (hCw : 0 ≤ Cw) {n : ℕ} (hn : 0 < n)
    (ha : ‖a‖ ≤ 1 + C / (n : ℝ)) (had : ‖a + w‖ ≤ 1 + C / (n : ℝ))
    (hw : ‖w‖ ≤ Cw / (n : ℝ) ^ 3) :
    ‖insertionError a w n‖ ≤ (Cw ^ 2 * Real.exp C / 2) / (n : ℝ) ^ 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb := norm_insertionError_le_exp a w hC hn ha had
  have hs := sq_le_sq₀ (norm_nonneg w) (show 0 ≤ Cw / (n : ℝ) ^ 3 by positivity)
  have hsq := hs.mpr hw
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (show 0 ≤ (n : ℝ) ^ 2 / 2 by positivity))
    (Real.exp_pos C).le
  apply hb.trans
  convert hm using 1
  field_simp

#print axioms one_add_div_pow_le_exp
#print axioms norm_insertionError_le_exp
#print axioms norm_insertionError_quartic
#print axioms insertionError_succ
#print axioms norm_firstInsertion_le
#print axioms norm_insertionError_le
end OQ7
