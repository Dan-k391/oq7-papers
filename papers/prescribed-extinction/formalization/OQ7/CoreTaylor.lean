import OQ7.CoreAlgebra
import OQ7.CellRemainder

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace OQ7.CoreConstruction
open Finset
open scoped Matrix Matrix.Norms.Operator

def tripleTaylorTerm {A : Type*} [Ring A] [Algebra ℝ A]
    (X Y Z : A) (a b c : ℕ) (t : ℝ) : A :=
  (t ^ (a + b + c) / ((a.factorial : ℝ) * b.factorial * c.factorial)) •
    (X ^ a * Y ^ b * Z ^ c)

def tripleTaylorLow {A : Type*} [Ring A] [Algebra ℝ A]
    (X Y Z : A) (t : ℝ) : A :=
  ∑ c ∈ range 5, ∑ b ∈ range 5, ∑ a ∈ range 5,
    if a + b + c < 5 then tripleTaylorTerm X Y Z a b c t else 0

def tripleTaylorTail {A : Type*} [Ring A] [Algebra ℝ A]
    (X Y Z : A) (t : ℝ) : A :=
  ∑ c ∈ range 5, ∑ b ∈ range 5, ∑ a ∈ range 5,
    if 5 ≤ a + b + c then
      (t ^ (a + b + c - 5) / ((a.factorial : ℝ) * b.factorial * c.factorial)) •
        (X ^ a * Y ^ b * Z ^ c)
    else 0

theorem tripleTaylor_product {A : Type*} [Ring A] [Algebra ℝ A]
    (X Y Z : A) (t : ℝ) :
    algebraExpTaylor X 5 t * algebraExpTaylor Y 5 t * algebraExpTaylor Z 5 t =
      ∑ c ∈ range 5, ∑ b ∈ range 5, ∑ a ∈ range 5,
        tripleTaylorTerm X Y Z a b c t := by
  simp only [algebraExpTaylor, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  simp only [tripleTaylorTerm, smul_mul_assoc, mul_smul_comm, smul_smul,
    pow_add, div_eq_mul_inv, mul_inv_rev]
  congr 1
  ring

theorem tripleTaylor_low_tail {A : Type*} [Ring A] [Algebra ℝ A]
    (X Y Z : A) (t : ℝ) :
    algebraExpTaylor X 5 t * algebraExpTaylor Y 5 t * algebraExpTaylor Z 5 t =
      tripleTaylorLow X Y Z t + t ^ 5 • tripleTaylorTail X Y Z t := by
  rw [tripleTaylor_product]
  simp only [tripleTaylorLow, tripleTaylorTail, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : 5 ≤ a + b + c
  · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h), zero_add, smul_smul, tripleTaylorTerm]
    congr 1
    rw [← mul_div_assoc, ← pow_add, Nat.add_sub_of_le h]
  · simp [h, lt_of_not_ge h]

def cellFourthCoefficient (P Q : ℝ) : Mat2 :=
  (1 / 2 : ℝ) • (lossGenerator Q * cubicCoefficient P Q +
    cubicCoefficient P Q * lossGenerator Q)

def cellTaylorPolynomial (P Q t : ℝ) : Mat2 :=
  1 + t • lossGenerator Q + t ^ 3 • cubicCoefficient P Q +
    t ^ 4 • cellFourthCoefficient P Q

def cellTaylorTail (P Q t : ℝ) : Mat2 :=
  tripleTaylorTail ((-1 / 2 : ℝ) • realGenerator P)
    (realGenerator P + lossGenerator Q) ((-1 / 2 : ℝ) • realGenerator P) t

theorem concrete_cellTaylorLow (P Q t : ℝ) :
    tripleTaylorLow ((-1 / 2 : ℝ) • realGenerator P)
      (realGenerator P + lossGenerator Q) ((-1 / 2 : ℝ) • realGenerator P) t =
        cellTaylorPolynomial P Q t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleTaylorLow, tripleTaylorTerm, Finset.sum_range_succ,
      cellTaylorPolynomial, cellFourthCoefficient, realGenerator, lossGenerator,
      cubicCoefficient, matrixUnit21, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Complex.real_smul]
  all_goals (ring_nf; simp [Complex.I_sq]; ring)

theorem concrete_cellTaylor_product (P Q t : ℝ) :
    algebraExpTaylor ((-1 / 2 : ℝ) • realGenerator P) 5 t *
      algebraExpTaylor (realGenerator P + lossGenerator Q) 5 t *
        algebraExpTaylor ((-1 / 2 : ℝ) • realGenerator P) 5 t =
      cellTaylorPolynomial P Q t + t ^ 5 • cellTaylorTail P Q t := by
  rw [tripleTaylor_low_tail, concrete_cellTaylorLow]
  rfl

#print axioms tripleTaylor_product
#print axioms tripleTaylor_low_tail
#print axioms concrete_cellTaylorLow
#print axioms concrete_cellTaylor_product
end OQ7.CoreConstruction
