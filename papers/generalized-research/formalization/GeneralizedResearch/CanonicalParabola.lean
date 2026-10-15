import GeneralizedResearch.CanonicalMiddle

/-! The third-branch upper bound for the literal canonical SDP, including
the original two unit input quadratic forms. -/
noncomputable section
open scoped Matrix
namespace GeneralizedResearch
namespace CanonicalParabola

theorem projection_lower {n : Type*} [Fintype n] (x y : n → ℝ) (hy : y ⬝ᵥ y = 1) :
    (y ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  have h := dotProduct_star_self_nonneg (x - (y ⬝ᵥ x) • y)
  have hsym : x ⬝ᵥ y = y ⬝ᵥ x := dotProduct_comm _ _
  simp [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    hy, hsym] at h
  nlinarith

theorem unit_quadratic_bounds (A Q : Mat2) (hA : A.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (a b : Fin 2 → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) :
    (b ⬝ᵥ (A *ᵥ a)) ^ 2 ≤ a ⬝ᵥ (Q *ᵥ a) ∧ a ⬝ᵥ (Q *ᵥ a) ≤ 1 := by
  have hnorm : (A *ᵥ a) ⬝ᵥ (A *ᵥ a) = a ⬝ᵥ ((A ^ 2) *ᵥ a) := by
    have ht : A.transpose = A := by simpa using hA.eq
    calc
      _ = (a ᵥ* A.transpose) ⬝ᵥ (A *ᵥ a) := by rw [Matrix.vecMul_transpose]
      _ = a ⬝ᵥ (A.transpose *ᵥ (A *ᵥ a)) :=
        (Matrix.dotProduct_mulVec a A.transpose (A *ᵥ a)).symm
      _ = _ := by rw [Matrix.mulVec_mulVec, ht, pow_two]
  have hl := projection_lower (A *ᵥ a) b hb
  rw [hnorm] at hl
  have hr := hrelax.dotProduct_mulVec_nonneg a
  have hc := hcontract.dotProduct_mulVec_nonneg a
  change 0 ≤ a ⬝ᵥ ((Q - A ^ 2) *ᵥ a) at hr
  change 0 ≤ a ⬝ᵥ (((1 : Mat2) - Q) *ᵥ a) at hc
  rw [Matrix.sub_mulVec, dotProduct_sub] at hr
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ha] at hc
  exact ⟨by linarith, by linarith⟩

/-- For every symmetric feasible pair and its literal two unit inputs, the
universal extinction parabola is an upper bound for the full canonical SDP. -/
theorem canonical_parabola (A Q : Mat2) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (p q r : ℝ) (hpq : p ^ 2 + q ^ 2 = 1)
    (htarget : p ^ 2 * A 0 0 - q ^ 2 * A 1 1 = r) :
    |4 * p * q * Q 0 1| ≤ 1 - r ^ 2 := by
  let a : Fin 2 → ℝ := ![p, q]
  let b : Fin 2 → ℝ := ![p, -q]
  have ha : a ⬝ᵥ a = 1 := by simpa [a, dotProduct, Fin.sum_univ_two, pow_two] using hpq
  have hb : b ⬝ᵥ b = 1 := by simpa [b, dotProduct, Fin.sum_univ_two, pow_two] using hpq
  have hAoff : A 1 0 = A 0 1 := by simpa using hA.apply 0 1
  have hQoff : Q 1 0 = Q 0 1 := by simpa using hQ.apply 0 1
  have hfa : b ⬝ᵥ (A *ᵥ a) = r := by
    simp [a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hAoff]
    nlinarith [htarget]
  have hfb : a ⬝ᵥ (A *ᵥ b) = r := by
    simp [a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hAoff]
    nlinarith [htarget]
  obtain ⟨hal, hau⟩ := unit_quadratic_bounds A Q hA hrelax hcontract a b ha hb
  obtain ⟨hbl, hbu⟩ := unit_quadratic_bounds A Q hA hrelax hcontract b a hb ha
  rw [hfa] at hal
  rw [hfb] at hbl
  have hdiff : a ⬝ᵥ (Q *ᵥ a) - b ⬝ᵥ (Q *ᵥ b) = 4 * p * q * Q 0 1 := by
    simp [a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hQoff]
    ring
  rw [← hdiff, abs_le]
  constructor <;> linarith

#print axioms canonical_parabola
end CanonicalParabola
end GeneralizedResearch
