import PrescribedExtinction.Basic

/-! Exact finite-dimensional constitutive calculations; these do not assume a
Maxwell solution, an optical theorem, or the aperture limit. -/
noncomputable section
namespace OQ7Prescribed

def axisCoupling (u : Position) (v : Vector) : ℂ := ∑ i, (u i : ℂ) * v i

theorem axisCoupling_eq_inner (u : Position) (v : Vector) :
    axisCoupling u v = inner ℂ (complexify u) v := by
  simp [axisCoupling, PiLp.inner_apply, complexify, RCLike.inner_apply, mul_comm]

theorem complexify_norm_sq (u : Position) : ‖complexify u‖ ^ 2 = ‖u‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, complexify]

theorem axisCoupling_bound (u : Position) (v : Vector) (hu : ‖u‖ ^ 2 = 1) :
    Complex.normSq (axisCoupling u v) ≤ squareNorm v := by
  have hc : ‖complexify u‖ = 1 := by
    have h := complexify_norm_sq u
    have hn := norm_nonneg (complexify u)
    nlinarith
  have hb := norm_inner_le_norm (𝕜 := ℂ) (complexify u) v
  rw [← axisCoupling_eq_inner, hc, one_mul] at hb
  rw [Complex.normSq_eq_norm_sq, squareNorm_eq_norm_sq]
  nlinarith [norm_nonneg (axisCoupling u v), norm_nonneg v]

theorem tensorApply_rankOne (u : Position) (v : Vector) :
    tensorApply (rankOne u) v = axisCoupling u v • complexify u := by
  ext i
  simp [tensorApply, rankOne, axisCoupling, complexify, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_comm, mul_assoc]

theorem quadratic_layer (a b ν : ℝ) (u : Position) (v : Vector) :
    quadratic (layerPermittivity a b ν u) v =
      (1 + Complex.I * (ν : ℂ)) * (squareNorm v : ℂ) +
      ((a : ℂ) + Complex.I * (b : ℂ)) * (Complex.normSq (axisCoupling u v) : ℂ) := by
  simp [quadratic, pairing, tensorApply, layerPermittivity, rankOne,
    axisCoupling, squareNorm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Complex.normSq_eq_conj_mul_self, map_add, map_mul]
  ring

theorem quadratic_layer_re (a b ν : ℝ) (u : Position) (v : Vector) :
    (quadratic (layerPermittivity a b ν u) v).re =
      squareNorm v + a * Complex.normSq (axisCoupling u v) := by
  rw [quadratic_layer]
  simp

theorem quadratic_layer_im (a b ν : ℝ) (u : Position) (v : Vector) :
    (quadratic (layerPermittivity a b ν u) v).im =
      ν * squareNorm v + b * Complex.normSq (axisCoupling u v) := by
  rw [quadratic_layer]
  simp

/-- Actual tensor caps, including strict loss in all three directions. -/
theorem layerPermittivity_admissible (P Q a b ν : ℝ) (u : Position)
    (hu : ‖u‖ ^ 2 = 1) (ha : 0 ≤ a) (hap : 1 + a ≤ P)
    (hb : 0 ≤ b) (hν : 0 < ν) (hbq : b + ν ≤ Q) :
    MaterialAdmissible P Q (layerPermittivity a b ν u) := by
  refine ⟨layerPermittivity_reciprocal a b ν u, ?_, ?_, ?_⟩
  · intro v
    rw [quadratic_layer_re]
    have hn := squareNorm_nonneg v
    have hc := Complex.normSq_nonneg (axisCoupling u v)
    have hd := axisCoupling_bound u v hu
    constructor <;> nlinarith
  · intro v hv
    rw [quadratic_layer_im]
    have hn := squareNorm_pos hv
    have hc := Complex.normSq_nonneg (axisCoupling u v)
    nlinarith
  · intro v
    rw [quadratic_layer_im]
    have hn := squareNorm_nonneg v
    have hd := axisCoupling_bound u v hu
    nlinarith

end OQ7Prescribed
