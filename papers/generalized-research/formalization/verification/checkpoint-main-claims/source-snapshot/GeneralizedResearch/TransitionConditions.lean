import GeneralizedResearch.CanonicalEnvelope

/-! Necessary equality transitions for the two outer bounds. -/
noncomputable section
open scoped Matrix
namespace GeneralizedResearch
namespace TransitionConditions

theorem first_branch_effect_unique (Q : Mat2) (hQ : Q.PosSemidef)
    (hI : ((1 : Mat2) - Q).PosSemidef) (hoff : Q 0 1 = 1 / 2) :
    Q = OuterBound.P := by
  have hsym : Q 1 0 = Q 0 1 := by simpa using hQ.1.apply 0 1
  have hm := hQ.dotProduct_mulVec_nonneg ![1, -1]
  have hp := hI.dotProduct_mulVec_nonneg ![1, 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym, hoff] at hm hp
  have htr : Q 0 0 + Q 1 1 = 1 := by linarith
  have hzero : star ![1, -1] ⬝ᵥ (Q *ᵥ ![1, -1]) = 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym, hoff]
    linarith
  have hker := hQ.dotProduct_mulVec_zero_iff.mp hzero
  have h00 : Q 0 0 = 1 / 2 := by
    have h := congrFun hker 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hoff] at h
    linarith
  have h11 : Q 1 1 = 1 / 2 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [OuterBound.P, h00, h11, hsym, hoff]

theorem first_branch_extinction_necessary {rho : ℝ} (hrho : 0 < rho)
    (A Q : Mat2) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hI : ((1 : Mat2) - Q).PosSemidef) (hoff : Q 0 1 = 1 / 2) :
    |(OuterBound.W rho * A).trace| ≤ rho / 2 := by
  have hQP := first_branch_effect_unique Q hQ hI hoff
  have hker : OuterBound.P *ᵥ ![1, -1] = 0 := by
    ext i
    fin_cases i <;> norm_num [OuterBound.P, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hAnorm : (A *ᵥ ![1, -1]) ⬝ᵥ (A *ᵥ ![1, -1]) =
      ![1, -1] ⬝ᵥ ((A ^ 2) *ᵥ ![1, -1]) := by
    have ht : A.transpose = A := by simpa using hA.eq
    calc
      _ = (![1, -1] ᵥ* A.transpose) ⬝ᵥ (A *ᵥ ![1, -1]) := by rw [Matrix.vecMul_transpose]
      _ = ![1, -1] ⬝ᵥ (A.transpose *ᵥ (A *ᵥ ![1, -1])) :=
        (Matrix.dotProduct_mulVec _ _ _).symm
      _ = _ := by rw [Matrix.mulVec_mulVec, ht, pow_two]
  have hr := hrelax.dotProduct_mulVec_nonneg ![1, -1]
  rw [hQP, Matrix.sub_mulVec, hker] at hr
  have hn : 0 ≤ (A *ᵥ ![1, -1]) ⬝ᵥ (A *ᵥ ![1, -1]) := by
    simpa using dotProduct_star_self_nonneg (A *ᵥ ![1, -1])
  have hn0 : (A *ᵥ ![1, -1]) ⬝ᵥ (A *ᵥ ![1, -1]) = 0 := by
    rw [hAnorm]
    simp only [sub_zero, zero_sub, dotProduct_neg, star_trivial] at hr
    linarith [hAnorm]
  have hAv : A *ᵥ ![1, -1] = 0 := dotProduct_self_eq_zero.mp hn0
  have hsym : A 1 0 = A 0 1 := by simpa using hA.apply 0 1
  have h01 : A 0 1 = A 0 0 := by
    have h := congrFun hAv 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    linarith
  have h11 : A 1 1 = A 0 0 := by
    have h := congrFun hAv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym, h01] at h
    linarith
  have hv := hrelax.dotProduct_mulVec_nonneg ![1, 1]
  rw [hQP] at hv
  simp [OuterBound.P, pow_two, Matrix.mulVec, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two, hsym, h01, h11] at hv
  have habs : |A 0 0| ≤ 1 / 2 := by rw [abs_le]; constructor <;> nlinarith
  have htrace : (OuterBound.W rho * A).trace = rho * A 0 0 := by
    simp [OuterBound.W, Matrix.trace_fin_two, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, h11]
    ring
  rw [htrace, abs_mul, abs_of_pos hrho]
  nlinarith

theorem first_branch_abs_extinction_necessary {rho : ℝ} (hrho : 0 < rho)
    (A Q : Mat2) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hI : ((1 : Mat2) - Q).PosSemidef) (hoff : |Q 0 1| = 1 / 2) :
    |(OuterBound.W rho * A).trace| ≤ rho / 2 := by
  by_cases hpos : 0 ≤ Q 0 1
  · rw [abs_of_nonneg hpos] at hoff
    exact first_branch_extinction_necessary hrho A Q hA hQ hrelax hI hoff
  · have hneg : Q 0 1 < 0 := lt_of_not_ge hpos
    rw [abs_of_neg hneg] at hoff
    let A' := MiddleParameters.flip A
    let Q' := MiddleParameters.flip Q
    have hR : (Q' - A' ^ 2).PosSemidef := by
      dsimp [A', Q']
      rw [MiddleParameters.flip_square, ← MiddleParameters.flip_sub]
      exact MiddleParameters.flip_posSemidef hrelax
    have hC : ((1 : Mat2) - Q').PosSemidef := by
      dsimp [Q']
      rw [← MiddleParameters.flip_one, ← MiddleParameters.flip_sub]
      exact MiddleParameters.flip_posSemidef hI
    have hO : Q' 0 1 = 1 / 2 := by
      dsimp [Q']
      rwa [MiddleParameters.flip_offdiag]
    have hb := first_branch_extinction_necessary hrho A' Q'
      (MiddleParameters.flip_hermitian A hA)
      (MiddleParameters.flip_posSemidef hQ) hR hC hO
    have hT : (OuterBound.W rho * A').trace = (OuterBound.W rho * A).trace := by
      simp [A', OuterBound.W, MiddleParameters.flip, MiddleParameters.J,
        Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rwa [hT] at hb

/-- If an effect saturates one unit-input output and another output has power
`r²`, positivity already forces the overlap threshold `rho≤r`. -/
theorem parabola_transition_necessary {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Q.PosSemidef)
    (hI : ((1 : Matrix n n ℝ) - Q).PosSemidef)
    (a b : n → ℝ) (ha : a ⬝ᵥ a = 1)
    (rho r : ℝ) (hrho : 0 ≤ rho) (hr : 0 ≤ r)
    (hoverlap : a ⬝ᵥ b = rho) (hqa : a ⬝ᵥ (Q *ᵥ a) = 1)
    (hqb : b ⬝ᵥ (Q *ᵥ b) = r ^ 2) : rho ≤ r := by
  have hzero : star a ⬝ᵥ (((1 : Matrix n n ℝ) - Q) *ᵥ a) = 0 := by
    change a ⬝ᵥ (((1 : Matrix n n ℝ) - Q) *ᵥ a) = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ha, hqa]
    ring
  have hker := hI.dotProduct_mulVec_zero_iff.mp hzero
  have hQa : Q *ᵥ a = a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hker
    exact (sub_eq_zero.mp hker).symm
  have hab : a ⬝ᵥ (Q *ᵥ b) = rho := by
    have h := hQ.1.star_dotProduct_mulVec_comm a b
    simpa [hQa, dotProduct_comm, hoverlap] using h
  have hba : b ⬝ᵥ (Q *ᵥ a) = rho := by rw [hQa, dotProduct_comm, hoverlap]
  have hpos := hQ.dotProduct_mulVec_nonneg (b - rho • a)
  simp [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, hqa, hqb, hab, hba] at hpos
  nlinarith

theorem parabola_equality_threshold {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Q.PosSemidef)
    (hI : ((1 : Matrix n n ℝ) - Q).PosSemidef)
    (a b : n → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (rho r : ℝ) (hrho : 0 ≤ rho) (hr : 0 ≤ r)
    (hoverlap : a ⬝ᵥ b = rho)
    (hqaL : r ^ 2 ≤ a ⬝ᵥ (Q *ᵥ a)) (hqaU : a ⬝ᵥ (Q *ᵥ a) ≤ 1)
    (hqbL : r ^ 2 ≤ b ⬝ᵥ (Q *ᵥ b)) (hqbU : b ⬝ᵥ (Q *ᵥ b) ≤ 1)
    (heq : |a ⬝ᵥ (Q *ᵥ a) - b ⬝ᵥ (Q *ᵥ b)| = 1 - r ^ 2) : rho ≤ r := by
  by_cases hpos : 0 ≤ a ⬝ᵥ (Q *ᵥ a) - b ⬝ᵥ (Q *ᵥ b)
  · rw [abs_of_nonneg hpos] at heq
    have hqa : a ⬝ᵥ (Q *ᵥ a) = 1 := by linarith
    have hqb : b ⬝ᵥ (Q *ᵥ b) = r ^ 2 := by linarith
    exact parabola_transition_necessary Q hQ hI a b ha rho r hrho hr hoverlap hqa hqb
  · rw [abs_of_neg (lt_of_not_ge hpos)] at heq
    have hqa : a ⬝ᵥ (Q *ᵥ a) = r ^ 2 := by linarith
    have hqb : b ⬝ᵥ (Q *ᵥ b) = 1 := by linarith
    have hoverlap' : b ⬝ᵥ a = rho := by rw [dotProduct_comm, hoverlap]
    exact parabola_transition_necessary Q hQ hI b a hb rho r hrho hr hoverlap' hqb hqa

#print axioms first_branch_effect_unique
#print axioms first_branch_extinction_necessary
#print axioms parabola_transition_necessary
end TransitionConditions
end GeneralizedResearch
