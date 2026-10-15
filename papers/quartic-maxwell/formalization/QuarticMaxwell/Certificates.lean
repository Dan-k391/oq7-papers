/-
Kernel-checked arithmetic for the 10 October 2026 quartic manuscript
(OQ7_quartic_Maxwell_2026-10-10.pdf, SHA-256
576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62).

Scope.  This module checks (i) the final real-algebra step of Theorem 1.1, with the
analytic operator estimates of Lemmas 3.1-3.3 and eq. (22) taken as explicit
hypotheses, and (ii) the rational and surd constants of the two-sphere certificate
(Section 5) and the homogeneous-sphere certificate (Section 6).  It does not define
Maxwell operators, prove the operator estimates, or prove Theorems 1.1-1.3.
Moments are in units of pi a^3, as in the manuscript's own bookkeeping.

Pins: Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (the same
pins as the prescribed-extinction formalization, whose build environment is used).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace OQ7Quartic

open Complex

/-! ### Theorem 1.1: the final algebraic chain, conditional on the stated estimates -/

/-- With `sV = √V`, `hX = √(ρX/k)`, the passivity bounds `‖p±‖ ≤ hX`, eq. (23)
`√V ≤ L_k hX`, eq. (22) `‖p₊-p₋‖ ≤ 2ρkR√V`, and the radiation-norm estimate in (24),
the scattering difference obeys eq. (24): `|S₊-S₋| ≤ (2/(3π)) ρ² L_k k⁴ R V X`. -/
theorem quartic_chain {k R V X ρ Lk hX np nm dp dS sV : ℝ}
    (hk : 0 < k) (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (hsV0 : 0 ≤ sV) (hsV : sV ^ 2 = V) (hh0 : 0 ≤ hX) (hh : hX ^ 2 = ρ * X / k)
    (hnp0 : 0 ≤ np) (hnm0 : 0 ≤ nm) (hnp : np ≤ hX) (hnm : nm ≤ hX)
    (hnorm : sV ≤ Lk * hX) (_hdp0 : 0 ≤ dp) (hdp : dp ≤ 2 * ρ * k * R * sV)
    (hS : |dS| ≤ k ^ 4 * V / (6 * Real.pi) * dp * (np + nm)) :
    |dS| ≤ 2 / (3 * Real.pi) * ρ ^ 2 * Lk * k ^ 4 * R * V * X := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hV0 : 0 ≤ V := by rw [← hsV]; positivity
  have hc : 0 ≤ k ^ 4 * V / (6 * Real.pi) := by positivity
  have h1 : dp * (np + nm) ≤ (2 * ρ * k * R * sV) * (2 * hX) :=
    mul_le_mul hdp (by linarith) (by positivity) (by positivity)
  have h2 : sV * hX ≤ (Lk * hX) * hX := mul_le_mul_of_nonneg_right hnorm hh0
  calc |dS| ≤ k ^ 4 * V / (6 * Real.pi) * dp * (np + nm) := hS
    _ = k ^ 4 * V / (6 * Real.pi) * (dp * (np + nm)) := by ring
    _ ≤ k ^ 4 * V / (6 * Real.pi) * ((2 * ρ * k * R * sV) * (2 * hX)) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = (2 / (3 * Real.pi) * ρ * k ^ 5 * R * V) * (sV * hX) := by field_simp; ring
    _ ≤ (2 / (3 * Real.pi) * ρ * k ^ 5 * R * V) * ((Lk * hX) * hX) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 / (3 * Real.pi) * ρ * k ^ 5 * R * V * Lk * hX ^ 2 := by ring
    _ = 2 / (3 * Real.pi) * ρ ^ 2 * Lk * k ^ 4 * R * V * X := by
        rw [hh]; field_simp

/-- Eq. (6): with `V ≤ 4πR³/3`, the coefficient `2/(3π)` becomes `8/9`. -/
theorem quartic_coefficient_ball : 2 / (3 * Real.pi) * (4 * Real.pi / 3) = (8 / 9 : ℝ) := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-! ### Section 5: the heterogeneous two-sphere certificate -/

/-- Isolated-sphere response factors `β = 3χ/(3+χ)` for `χ = i` and `χ = 2i`. -/
theorem beta_one : (3 / 10 : ℂ) * (1 + 3 * I) * (3 + I) = 3 * I := by
  linear_combination (9 / 10 : ℂ) * Complex.I_sq

theorem beta_two : (6 / 13 : ℂ) * (2 + 3 * I) * (3 + 2 * I) = 3 * (2 * I) := by
  linear_combination (36 / 13 : ℂ) * Complex.I_sq

/-- Isolated polarizabilities in units of `π a³` (eq. (39)). -/
noncomputable def α₁ : ℂ := ⟨2 / 5, 6 / 5⟩
noncomputable def α₂ : ℂ := ⟨128 / 13, 192 / 13⟩

theorem alpha_one_eq : α₁ = (4 / 3 : ℂ) * ((3 / 10 : ℂ) * (1 + 3 * I)) := by
  apply Complex.ext <;> simp [α₁] <;> norm_num

theorem alpha_two_eq : α₂ = (32 / 3 : ℂ) * ((6 / 13 : ℂ) * (2 + 3 * I)) := by
  apply Complex.ext <;> simp [α₂] <;> norm_num

/-- Eq. (41), with `w = 12` in these units: `I_b = -(8/195) w²`, `D_b = (173/130) w`. -/
theorem block_moment_imag :
    ((starRingEnd ℂ) (α₁ + α₂) * ((1 / 2 : ℂ) * (α₂ - α₁))).im = -(8 / 195) * 12 ^ 2 := by
  simp [α₁, α₂, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  norm_num

theorem block_extinction : (α₁ + α₂).im = (173 / 130) * 12 := by
  simp [α₁, α₂]
  norm_num

/-- Eq. (36): the interaction constant `c = 4√2/14739` is below `1/2500`. -/
theorem coupling_lt : 4 * Real.sqrt 2 / 14739 < (1 / 2500 : ℝ) := by
  have h : Real.sqrt 2 < 14739 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-- The squared form of `c`, from `|Ω₁||Ω₂| = (4π/3)² 8a⁶` and gap `17/20`. -/
theorem coupling_sq :
    (16 / 9 : ℝ) * 8 * (1 / 20) ^ 6 / (4 * (17 / 20) ^ 6) = (4 * Real.sqrt 2 / 14739) ^ 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (4 * Real.sqrt 2 / 14739) ^ 2 = (32 : ℝ) / 14739 ^ 2 := by
    rw [div_pow, mul_pow, h]; norm_num
  rw [h2]; norm_num

/-- Eq. (37): `δ ≤ 4c/(1-2c) < 1/600` for every `0 ≤ c < 1/2500`. -/
theorem delta_lt {c : ℝ} (_h0 : 0 ≤ c) (h : c < 1 / 2500) : 4 * c / (1 - 2 * c) < 1 / 600 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- Eq. (43): the relative interaction error is the rational `0.097540625 < 1/10`. -/
theorem relative_error :
    (3 / 5 : ℝ) * (4 * (1 / 600) + (1 / 600) ^ 2) / (8 / 195) = 1404585 / 14400000 ∧
      (1404585 / 14400000 : ℝ) < 1 / 10 := by
  constructor <;> norm_num

/-- Eqs. (44)-(45) and (7): the certified coefficient interval at `a = 1/20`. -/
theorem coefficient_interval :
    2 * (12 / 325 : ℝ) * 12 * (7800 / 10393) / 3 = 2304 / 10393 ∧
      2 * (44 / 975 : ℝ) * 12 * (7800 / 10367) / 3 = 2816 / 10367 ∧
      (2304 / 10393 : ℝ) * (1 / 20) ^ 3 = 36 / 1299125 ∧
      (2816 / 10367 : ℝ) * (1 / 20) ^ 3 = 44 / 1295875 ∧
      (36 / 1299125 : ℝ) < 128 / 519 * (1 / 20) ^ 3 ∧
      (128 / 519 : ℝ) * (1 / 20) ^ 3 < 44 / 1295875 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Eqs. (47)-(51): explicit remainder constants and the quartic lower bound. -/
theorem remainder_constants :
    (3 / 5 : ℝ) ^ 2 + 72 / 25 = 81 / 25 ∧
      2 * (3 / 5 : ℝ) ^ 3 / 6 + 72 / 25 * (3 / 5) = 9 / 5 ∧
      (54 / 125 : ℝ) + 81 / 125 + 3 / 5 = 42 / 25 ∧
      ((3 / 5 : ℝ) ^ 2 + 81 / 25) + 2 * (3 / 5) ^ 2 = 108 / 25 ∧
      (1 : ℝ) ≤ 10367 / 7800 - 108 / 25 / 16 ∧
      (168 / 25 : ℝ) + 88 / 2925 * (108 / 25) = 55656 / 8125 ∧
      (55656 / 8125 : ℝ) < 7 ∧
      (7 : ℝ) * (12 / 8000) = 21 / 2000 ∧
      (21 / 2000 : ℝ) * (1 / 40) ^ 2 < 1 / 4 * (36 / 1299125) ∧
      (3 / 4 : ℝ) * (36 / 1299125) = 27 / 1299125 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ### Section 6: homogeneous unequal spheres -/

/-- Eq. (61): `L = -g₀ v₁v₂(v₂-v₁)|β|² Im β` with `v = 4πa³/3`, `v₂ = 8v`, coefficient 2688. -/
theorem first_interaction_coefficient : (1 / 4 : ℝ) * 56 * (64 / 27) * 81 = 2688 := by norm_num

/-- Eq. (62) at `h = 4/5`: `48√3/(7h⁴) < 30`. -/
theorem first_interaction_error : 48 * Real.sqrt 3 / (7 * (4 / 5) ^ 4) < (30 : ℝ) := by
  have h : Real.sqrt 3 < 1792 / 1000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [div_lt_iff₀ (by norm_num)]
  nlinarith

/-- Eq. (54): `√2/(3h³) ≤ 1` at `h = 4/5`, so `‖C_o‖ ≤ 4a³`. -/
theorem coupling_homogeneous : Real.sqrt 2 / (3 * (4 / 5) ^ 3) ≤ (1 : ℝ) := by
  have h : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- Eqs. (64)-(66) and the `μ = 1, a = 1/100` example. -/
theorem homogeneous_constants :
    (9 / 5 : ℝ) * 16 * 144 / 2688 = 54 / 35 ∧
      (30 : ℝ) / 120 + 54 / 35 * (35 / 216) = 1 / 2 ∧
      (2688 : ℝ) / 36 = 224 / 3 ∧
      (30 : ℝ) * 10 * (1 / 100) ^ 2 + 54 / 35 * 100 * (1 / 100) ^ 3 = 5277 / 175000 ∧
      (5277 / 175000 : ℝ) < 31 / 1000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end OQ7Quartic

#print axioms OQ7Quartic.quartic_chain
#print axioms OQ7Quartic.quartic_coefficient_ball
#print axioms OQ7Quartic.beta_one
#print axioms OQ7Quartic.beta_two
#print axioms OQ7Quartic.alpha_one_eq
#print axioms OQ7Quartic.alpha_two_eq
#print axioms OQ7Quartic.block_moment_imag
#print axioms OQ7Quartic.block_extinction
#print axioms OQ7Quartic.coupling_lt
#print axioms OQ7Quartic.coupling_sq
#print axioms OQ7Quartic.delta_lt
#print axioms OQ7Quartic.relative_error
#print axioms OQ7Quartic.coefficient_interval
#print axioms OQ7Quartic.remainder_constants
#print axioms OQ7Quartic.first_interaction_coefficient
#print axioms OQ7Quartic.first_interaction_error
#print axioms OQ7Quartic.coupling_homogeneous
#print axioms OQ7Quartic.homogeneous_constants
