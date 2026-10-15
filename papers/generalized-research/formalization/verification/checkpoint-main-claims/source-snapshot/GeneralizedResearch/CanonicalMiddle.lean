import GeneralizedResearch.MiddleCertificate
import GeneralizedResearch.RealCompression

/-! # The full middle branch in the manuscript's canonical input coordinates

The orthogonal rotation is explicitly constructed from the unique middle
parameter. This connects the diagonal-basis certificate to the actual
canonical complex-channel compression, including arbitrary finite auxiliary
channels and its equality consequences. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace GeneralizedResearch
namespace MiddleParameters

def rotU (p : MiddleParameters) : ℝ := Real.sqrt ((1 + p.c) / 2)
def rotV (p : MiddleParameters) : ℝ := p.s / (2 * p.rotU)
def O (p : MiddleParameters) : Mat2 := !![p.rotU, -p.rotV; p.rotV, p.rotU]
def canonicalW (p : MiddleParameters) : Mat2 :=
  !![(1 + p.rho) / 2, 0; 0, -(1 - p.rho) / 2]
def canonicalE : Mat2 := !![0, 1 / 2; 1 / 2, 0]

theorem rotU_pos (p : MiddleParameters) : 0 < p.rotU := by
  apply Real.sqrt_pos.mpr
  linarith [p.c_pos]

theorem rotU_sq (p : MiddleParameters) : p.rotU ^ 2 = (1 + p.c) / 2 := by
  exact Real.sq_sqrt (by linarith [p.c_pos])

theorem rot_product (p : MiddleParameters) : 2 * p.rotU * p.rotV = p.s := by
  dsimp [rotV]
  field_simp [p.rotU_pos.ne']

theorem rotV_sq (p : MiddleParameters) : p.rotV ^ 2 = (1 - p.c) / 2 := by
  have hu : 1 + p.c ≠ 0 := by linarith [p.c_pos]
  unfold rotV
  rw [div_pow, mul_pow, p.rotU_sq]
  field_simp [hu]
  nlinarith [p.s_sq]

theorem O_transpose_mul (p : MiddleParameters) : p.O.transpose * p.O = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [O, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [p.rotU_sq, p.rotV_sq]

theorem O_mul_transpose (p : MiddleParameters) : p.O * p.O.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [O, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [p.rotU_sq, p.rotV_sq]

theorem rotated_W (p : MiddleParameters) :
    p.O.transpose * p.canonicalW * p.O = p.W := by
  have hur := congrArg (fun z : ℝ => z * p.rho) p.rotU_sq
  have hvr := congrArg (fun z : ℝ => z * p.rho) p.rotV_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [O, canonicalW, W, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [p.rotU_sq, p.rotV_sq, p.rot_product, hur, hvr]

theorem rotated_E (p : MiddleParameters) :
    p.O.transpose * canonicalE * p.O = p.E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [O, canonicalE, E, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [p.rotU_sq, p.rotV_sq, p.rot_product]

theorem rotated_square (p : MiddleParameters) (A : Mat2) :
    (p.O.transpose * A * p.O) ^ 2 = p.O.transpose * A ^ 2 * p.O := by
  simp only [pow_two]
  calc
    (p.O.transpose * A * p.O) * (p.O.transpose * A * p.O) =
        p.O.transpose * A * (p.O * p.O.transpose) * A * p.O := by
          simp [Matrix.mul_assoc]
    _ = p.O.transpose * (A * A) * p.O := by
      rw [p.O_mul_transpose]
      simp [Matrix.mul_assoc]

theorem trace_rotation (p : MiddleParameters) (C M : Mat2) :
    ((p.O.transpose * C * p.O) * (p.O.transpose * M * p.O)).trace =
      (C * M).trace := by
  have hid : (p.O.transpose * C * p.O) * (p.O.transpose * M * p.O) =
      p.O.transpose * (C * M) * p.O := by
    calc
      _ = p.O.transpose * C * (p.O * p.O.transpose) * M * p.O := by
        simp [Matrix.mul_assoc]
      _ = _ := by rw [p.O_mul_transpose]; simp [Matrix.mul_assoc]
  rw [hid, Matrix.trace_mul_comm]
  simp [← Matrix.mul_assoc, p.O_mul_transpose]

theorem canonical_objective (Q : Mat2) (hQ : Q.IsHermitian) :
    (canonicalE * Q).trace = Q 0 1 := by
  have hoff : Q 1 0 = Q 0 1 := by simpa using hQ.apply 0 1
  simp [canonicalE, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, hoff]
  ring

/-- The bound now applies to the canonical real matrices, with their actual
weighted diagonal extinction and off-diagonal absorption objective. -/
theorem canonical_middle_upper_bound (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (p.canonicalW * A).trace = p.r) : Q 0 1 ≤ p.h := by
  let A' := p.O.transpose * A * p.O
  let Q' := p.O.transpose * Q * p.O
  have hA' : A'.IsHermitian := by
    simpa [A'] using Matrix.isHermitian_conjTranspose_mul_mul p.O hA
  have hQ' : Q'.IsHermitian := by
    simpa [Q'] using Matrix.isHermitian_conjTranspose_mul_mul p.O hQ
  have hR := hrelax.conjTranspose_mul_mul_same p.O
  have hR' : (Q' - A' ^ 2).PosSemidef := by
    simpa [A', Q', Matrix.mul_sub, Matrix.sub_mul, p.rotated_square] using hR
  have hI := hcontract.conjTranspose_mul_mul_same p.O
  have hI' : ((1 : Mat2) - Q').PosSemidef := by
    simpa [Q', Matrix.mul_sub, Matrix.sub_mul, p.O_transpose_mul] using hI
  have ht' : (p.W * A').trace = p.r := by
    rw [← p.rotated_W]
    exact (p.trace_rotation p.canonicalW A).trans htarget
  have hb := p.middle_SDP_upper_bound A' Q' hA' hQ' hR' hI' ht'
  have hobj : (p.E * Q').trace = Q 0 1 := by
    rw [← p.rotated_E]
    exact (p.trace_rotation canonicalE Q).trans (canonical_objective Q hQ)
  rwa [hobj] at hb

def J : Mat2 := !![1, 0; 0, -1]
def flip (A : Mat2) : Mat2 := J * A * J

theorem J_square : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_hermitian : J.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.conjTranspose_apply]

theorem flip_square (A : Mat2) : (flip A) ^ 2 = flip (A ^ 2) := by
  simp only [flip, pow_two]
  calc
    (J * A * J) * (J * A * J) = J * A * (J * J) * A * J := by
      simp [Matrix.mul_assoc]
    _ = J * (A * A) * J := by rw [J_square]; simp [Matrix.mul_assoc]

theorem flip_hermitian (A : Mat2) (hA : A.IsHermitian) : (flip A).IsHermitian := by
  have ht : J.transpose = J := by simpa using J_hermitian.eq
  simpa [flip, ht] using Matrix.isHermitian_conjTranspose_mul_mul J hA

theorem flip_posSemidef {A : Mat2} (hA : A.PosSemidef) : (flip A).PosSemidef := by
  have ht : J.transpose = J := by simpa using J_hermitian.eq
  simpa [flip, ht] using hA.conjTranspose_mul_mul_same J

theorem flip_sub (A B : Mat2) : flip (A - B) = flip A - flip B := by
  simp [flip, Matrix.mul_sub, Matrix.sub_mul]

theorem flip_one : flip (1 : Mat2) = 1 := by simp [flip, J_square]

theorem flip_offdiag (Q : Mat2) : flip Q 0 1 = -Q 0 1 := by
  simp [flip, J, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem flip_extinction (p : MiddleParameters) (A : Mat2) :
    (p.canonicalW * flip A).trace = (p.canonicalW * A).trace := by
  simp [canonicalW, flip, J, Matrix.trace_fin_two, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem canonical_middle_abs_bound (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (p.canonicalW * A).trace = p.r) : |Q 0 1| ≤ p.h := by
  have hupper := p.canonical_middle_upper_bound A Q hA hQ hrelax hcontract htarget
  have hrelax' : (flip Q - (flip A) ^ 2).PosSemidef := by
    rw [flip_square, ← flip_sub]
    exact flip_posSemidef hrelax
  have hcontract' : ((1 : Mat2) - flip Q).PosSemidef := by
    rw [← flip_one, ← flip_sub]
    exact flip_posSemidef hcontract
  have htarget' : (p.canonicalW * flip A).trace = p.r :=
    (p.flip_extinction A).trans htarget
  have hlower := p.canonical_middle_upper_bound (flip A) (flip Q)
    (flip_hermitian A hA) (flip_hermitian Q hQ) hrelax' hcontract' htarget'
  rw [flip_offdiag] at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem rotation_injective (p : MiddleParameters) :
    Function.Injective (fun A : Mat2 => p.O.transpose * A * p.O) := by
  intro A D h
  have h' := congrArg (fun M : Mat2 => p.O * M * p.O.transpose) h
  have hinflate (M : Mat2) : p.O * (p.O.transpose * M * p.O) * p.O.transpose = M := by
    calc
      _ = (p.O * p.O.transpose) * M * (p.O * p.O.transpose) := by
        simp [Matrix.mul_assoc]
      _ = M := by rw [p.O_mul_transpose]; simp
  simpa only [hinflate] using h'

/-- The complete canonical compressed equality pair in the middle branch,
after the sign changes explicitly described in the manuscript. -/
theorem canonical_middle_equality (p : MiddleParameters) (A Q : Mat2)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (hrelax : (Q - A ^ 2).PosSemidef)
    (hcontract : ((1 : Mat2) - Q).PosSemidef)
    (htarget : (p.canonicalW * A).trace = p.r) (hobj : Q 0 1 = p.h) :
    p.O.transpose * A * p.O = p.B ∧ Q = A ^ 2 := by
  let A' := p.O.transpose * A * p.O
  let Q' := p.O.transpose * Q * p.O
  have hA' : A'.IsHermitian := by
    simpa [A'] using Matrix.isHermitian_conjTranspose_mul_mul p.O hA
  have hQ' : Q'.IsHermitian := by
    simpa [Q'] using Matrix.isHermitian_conjTranspose_mul_mul p.O hQ
  have hR' : (Q' - A' ^ 2).PosSemidef := by
    simpa [A', Q', Matrix.mul_sub, Matrix.sub_mul, p.rotated_square] using
      hrelax.conjTranspose_mul_mul_same p.O
  have hI' : ((1 : Mat2) - Q').PosSemidef := by
    simpa [Q', Matrix.mul_sub, Matrix.sub_mul, p.O_transpose_mul] using
      hcontract.conjTranspose_mul_mul_same p.O
  have ht' : (p.W * A').trace = p.r := by
    rw [← p.rotated_W]
    exact (p.trace_rotation p.canonicalW A).trans htarget
  have ho' : (p.E * Q').trace = p.h := by
    rw [← p.rotated_E]
    exact (p.trace_rotation canonicalE Q).trans ((canonical_objective Q hQ).trans hobj)
  obtain ⟨hAe, hQe⟩ := p.middle_SDP_equality A' Q' hA' hQ' hR' hI' ht' ho'
  refine ⟨hAe, p.rotation_injective ?_⟩
  change p.O.transpose * Q * p.O = p.O.transpose * A ^ 2 * p.O
  rw [← p.rotated_square]
  exact hQe.trans (congrArg (fun M : Mat2 => M ^ 2) hAe.symm)

variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]

/-- The continuously parameterized middle bound for actual reciprocal
passive finite complex channel matrices, with arbitrary auxiliary channels. -/
theorem finite_complex_middle_upper_bound (p : MiddleParameters)
    (S : Matrix (Sum (Fin 2) ι) (Sum (Fin 2) ι) ℂ)
    (hS : S.transpose = S)
    (hpass : ((1 : Matrix (Sum (Fin 2) ι) (Sum (Fin 2) ι) ℂ) -
      S.conjTranspose * S).PosSemidef)
    (htarget : (p.canonicalW * RealCompression.B S).trace = p.r) :
    RealCompression.Q S 0 1 ≤ p.h := by
  obtain ⟨hB, hQ, hrelax, hcontract⟩ :=
    RealCompression.canonical_PSD_relaxation S hS hpass
  exact p.canonical_middle_upper_bound (RealCompression.B S)
    (RealCompression.Q S) hB hQ hrelax hcontract htarget

theorem finite_complex_middle_abs_bound (p : MiddleParameters)
    (S : Matrix (Sum (Fin 2) ι) (Sum (Fin 2) ι) ℂ)
    (hS : S.transpose = S)
    (hpass : ((1 : Matrix (Sum (Fin 2) ι) (Sum (Fin 2) ι) ℂ) -
      S.conjTranspose * S).PosSemidef)
    (htarget : (p.canonicalW * RealCompression.B S).trace = p.r) :
    |RealCompression.Q S 0 1| ≤ p.h := by
  obtain ⟨hB, hQ, hrelax, hcontract⟩ :=
    RealCompression.canonical_PSD_relaxation S hS hpass
  exact p.canonical_middle_abs_bound (RealCompression.B S)
    (RealCompression.Q S) hB hQ hrelax hcontract htarget

theorem finite_complex_middle_equality (p : MiddleParameters)
    (S : Matrix (Sum (Fin 2) ι) (Sum (Fin 2) ι) ℂ)
    (hS : S.transpose = S)
    (hpass : ((1 : Matrix (Sum (Fin 2) ι) (Sum (Fin 2) ι) ℂ) -
      S.conjTranspose * S).PosSemidef)
    (htarget : (p.canonicalW * RealCompression.B S).trace = p.r)
    (hobj : RealCompression.Q S 0 1 = p.h) :
    p.O.transpose * RealCompression.B S * p.O = p.B ∧
      RealCompression.imagPart (RealCompression.block S) = 0 ∧
      RealCompression.auxiliary S = 0 ∧ S.submatrix Sum.inl Sum.inr = 0 := by
  obtain ⟨hB, hQ, hrelax, hcontract⟩ :=
    RealCompression.canonical_PSD_relaxation S hS hpass
  obtain ⟨hpair, hQeq⟩ := p.canonical_middle_equality (RealCompression.B S)
    (RealCompression.Q S) hB hQ hrelax hcontract htarget hobj
  obtain ⟨him, haux⟩ := RealCompression.no_auxiliary_at_equality S hS hQeq
  exact ⟨hpair, him, haux, RealCompression.reverse_auxiliary_vanishes S hS hQeq⟩

#print axioms rotated_W
#print axioms rotated_E
#print axioms canonical_middle_upper_bound
#print axioms finite_complex_middle_upper_bound

end MiddleParameters
end GeneralizedResearch
