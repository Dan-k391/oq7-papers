import work.SphericalCoordinates
import PrescribedExtinction.FarFieldRadial

noncomputable section
namespace OQ7Prescribed
open Set MeasureTheory

def sphericalDomain : Set (Fin 3 → ℝ) :=
  {p | 0 < p 0 ∧ 0 < p 1 ∧ p 1 < Real.pi ∧ -Real.pi < p 2 ∧ p 2 < Real.pi}

theorem sphericalPoint_toLp (p : Fin 3 → ℝ) :
    WithLp.toLp 2 (sphericalPoint p) = p 0 • sphereDirection (p 1) (p 2) := by
  ext i
  fin_cases i <;> simp [sphericalPoint, sphereDirection, PiLp.smul_apply, mul_assoc]

theorem sphericalPoint_norm (p : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (sphericalPoint p)‖ = |p 0| := by
  rw [sphericalPoint_toLp, norm_smul, Real.norm_eq_abs]
  have hn : ‖sphereDirection (p 1) (p 2)‖ = 1 := by
    nlinarith [sphereDirection_unit (p 1) (p 2), norm_nonneg (sphereDirection (p 1) (p 2))]
  rw [hn, mul_one]

theorem sphericalPoint_injOn : InjOn sphericalPoint sphericalDomain := by
  intro p hp q hq he
  have hr : p 0 = q 0 := by
    have h := congrArg (fun x : Fin 3 → ℝ => ‖WithLp.toLp 2 x‖) he
    rw [sphericalPoint_norm, sphericalPoint_norm, abs_of_pos hp.1, abs_of_pos hq.1] at h
    exact h
  have ht : p 1 = q 1 := by
    apply Real.strictAntiOn_cos.injOn ⟨hp.2.1.le, hp.2.2.1.le⟩ ⟨hq.2.1.le, hq.2.2.1.le⟩
    have h := congrFun he 2
    simp only [sphericalPoint, Matrix.cons_val_two] at h
    rw [← hr] at h
    exact (mul_left_cancel₀ hp.1.ne' h)
  have hwidth : 0 < p 0 * Real.sin (p 1) :=
    mul_pos hp.1 (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1)
  have hpolar : polarCoord.symm (p 0 * Real.sin (p 1), p 2) =
      polarCoord.symm (p 0 * Real.sin (p 1), q 2) := by
    ext
    · have h := congrFun he 0
      simpa only [sphericalPoint, Matrix.cons_val_zero, polarCoord_symm_apply, hr, ht] using h
    · have h := congrFun he 1
      simpa only [sphericalPoint, Matrix.cons_val_one, Matrix.cons_val_zero, polarCoord_symm_apply, hr, ht] using h
  have hpPol : (p 0 * Real.sin (p 1), p 2) ∈ polarCoord.target := by
    change 0 < p 0 * Real.sin (p 1) ∧ -Real.pi < p 2 ∧ p 2 < Real.pi
    exact ⟨hwidth, hp.2.2.2⟩
  have hqPol : (p 0 * Real.sin (p 1), q 2) ∈ polarCoord.target := by
    change 0 < p 0 * Real.sin (p 1) ∧ -Real.pi < q 2 ∧ q 2 < Real.pi
    exact ⟨hwidth, hq.2.2.2⟩
  have hφ := congrArg Prod.snd (polarCoord.symm.injOn hpPol hqPol hpolar)
  ext i
  fin_cases i
  · exact hr
  · exact ht
  · exact hφ

theorem sphericalPoint_image_of_second_ne_zero (x : Fin 3 → ℝ) (hx : x 1 ≠ 0) :
    x ∈ sphericalPoint '' sphericalDomain := by
  let r := ‖WithLp.toLp 2 x‖
  let z : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I
  let θ := Real.arccos (x 2 / r)
  let φ := Complex.arg z
  have hz : z ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    simp [z] at h
    exact hx h
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzs : ‖z‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [z, Complex.normSq_apply]
    ring
  have hrs : r ^ 2 = ‖z‖ ^ 2 + (x 2) ^ 2 := by
    dsimp [r]
    rw [EuclideanSpace.real_norm_sq_eq, hzs]
    simp [Fin.sum_univ_three]
  have hr : 0 < r := by have hn : 0 ≤ r := norm_nonneg _; nlinarith [sq_pos_of_pos hρ]
  have hx2 : |x 2| < r := by nlinarith [sq_pos_of_pos hρ, sq_abs (x 2)]
  have hratio : -1 < x 2 / r ∧ x 2 / r < 1 := by
    constructor
    · apply (lt_div_iff₀ hr).mpr
      linarith [(abs_lt.mp hx2).1]
    · apply (div_lt_one hr).mpr
      exact (abs_lt.mp hx2).2
  have hθ : 0 < θ ∧ θ < Real.pi := ⟨Real.arccos_pos.mpr hratio.2, Real.arccos_lt_pi.mpr hratio.1⟩
  have hcos : r * Real.cos θ = x 2 := by
    rw [Real.cos_arccos hratio.1.le hratio.2.le]
    field_simp
  have hsin : r * Real.sin θ = ‖z‖ := by
    have hs : (r * Real.sin θ) ^ 2 + (r * Real.cos θ) ^ 2 = r ^ 2 := by
      calc
        _ = r ^ 2 * ((Real.sin θ) ^ 2 + (Real.cos θ) ^ 2) := by ring
        _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
    rw [hcos] at hs
    exact (sq_eq_sq₀ (mul_nonneg hr.le (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le) hρ.le).mp (by linarith)
  have hφ : -Real.pi < φ ∧ φ < Real.pi :=
    ⟨Complex.neg_pi_lt_arg z, Complex.arg_lt_pi_iff.mpr (Or.inr (by simpa [z] using hx))⟩
  refine ⟨![r, θ, φ], ⟨hr, hθ.1, hθ.2, hφ.1, hφ.2⟩, ?_⟩
  ext i
  fin_cases i
  · change r * Real.sin θ * Real.cos φ = x 0
    rw [hsin]
    simpa [z, φ] using Complex.norm_mul_cos_arg z
  · change r * Real.sin θ * Real.sin φ = x 1
    rw [hsin]
    simpa [z, φ] using Complex.norm_mul_sin_arg z
  · exact hcos

end OQ7Prescribed
