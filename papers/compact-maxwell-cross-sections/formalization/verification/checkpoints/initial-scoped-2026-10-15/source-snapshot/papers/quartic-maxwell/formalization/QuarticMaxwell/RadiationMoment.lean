import QuarticMaxwell.ProjectionKernel
import PrescribedExtinction.SphereMoments

/-! Exact complete-sphere transverse-projection moment. This uses the actual
Euclidean unit sphere and its area measure, retaining all vector polarizations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

def angularProjection (n : UnitSphere) : Vector →L[ℂ] Vector :=
  ContinuousLinearMap.id ℂ Vector - InnerProductSpace.rankOne ℂ (complexify n) (complexify n)

theorem sphere_inner_norm_sq (v : Vector) :
    (∫ n : UnitSphere, ‖inner ℂ (complexify n) v‖ ^ 2 ∂sphereArea) =
      4 * Real.pi / 3 * ‖v‖ ^ 2 := by
  have hpoint (n : UnitSphere) : ‖inner ℂ (complexify n) v‖ ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, (n : Position) i * (n : Position) j *
        ((v i).re * (v j).re + (v i).im * (v j).im) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [PiLp.inner_apply, RCLike.inner_apply, complexify, Fin.sum_univ_three,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hi (i j : Fin 3) : Integrable (fun n : UnitSphere =>
      (n : Position) i * (n : Position) j *
        ((v i).re * (v j).re + (v i).im * (v j).im)) sphereArea :=
    (sphere_coordinate_mul_integrable i j).mul_const _
  calc
    _ = ∫ n : UnitSphere, ∑ i : Fin 3, ∑ j : Fin 3,
        (n : Position) i * (n : Position) j *
          ((v i).re * (v j).re + (v i).im * (v j).im) ∂sphereArea :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = ∑ i : Fin 3, ∫ n : UnitSphere, ∑ j : Fin 3,
        (n : Position) i * (n : Position) j *
          ((v i).re * (v j).re + (v i).im * (v j).im) ∂sphereArea := by
      apply integral_finsetSum
      intro i _
      exact integrable_finsetSum _ (fun j _ => hi i j)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ n : UnitSphere,
        (n : Position) i * (n : Position) j *
          ((v i).re * (v j).re + (v i).im * (v j).im) ∂sphereArea := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hi i j)
    _ = _ := by
      simp only [integral_mul_const, sphere_second_moment]
      rw [← squareNorm_eq_norm_sq]
      simp [Fin.sum_univ_three, squareNorm, Complex.normSq_apply, pow_two]
      ring

theorem angularProjection_pythagoras (n : UnitSphere) (v : Vector) :
    ‖angularProjection n v‖ ^ 2 + ‖inner ℂ (complexify n) v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hne : (n : Position) ≠ 0 := norm_ne_zero_iff.mp (by rw [unitSphere_norm]; norm_num)
  have hcnnorm : ‖complexify (n : Position)‖ = 1 := by
    have hsq := complexify_norm_sq (n : Position)
    rw [unitSphere_norm, one_pow] at hsq
    nlinarith [norm_nonneg (complexify (n : Position))]
  have horth := radialProjection_orthogonal (n : Position) hne v
  simp only [radialProjection, unitSphere_norm, one_pow, inv_one, Complex.ofReal_one,
    one_smul] at horth
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((InnerProductSpace.rankOne ℂ (complexify n) (complexify n)) v)
    (v - (InnerProductSpace.rankOne ℂ (complexify n) (complexify n)) v) horth
  have hsum : (InnerProductSpace.rankOne ℂ (complexify n) (complexify n)) v +
      (v - (InnerProductSpace.rankOne ℂ (complexify n) (complexify n)) v) = v := by abel
  rw [hsum] at h
  simpa [angularProjection, InnerProductSpace.rankOne_apply, norm_smul,
    hcnnorm, unitSphere_norm, add_comm, pow_two] using h.symm

theorem angularProjection_square_integrable (v : Vector) :
    Integrable (fun n : UnitSphere => ‖angularProjection n v‖ ^ 2) sphereArea := by
  have hc : Continuous (fun n : UnitSphere => ‖angularProjection n v‖ ^ 2) := by
    have hcn : Continuous (fun n : UnitSphere => complexify (n : Position)) :=
      complexify_continuous.comp continuous_subtype_val
    unfold angularProjection
    simp only [sub_apply, ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply]
    fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem angularProjection_integral (v : Vector) :
    (∫ n : UnitSphere, ‖angularProjection n v‖ ^ 2 ∂sphereArea) =
      8 * Real.pi / 3 * ‖v‖ ^ 2 := by
  have hint : Integrable (fun n : UnitSphere => ‖inner ℂ (complexify n) v‖ ^ 2) sphereArea := by
    have hc : Continuous (fun n : UnitSphere => ‖inner ℂ (complexify n) v‖ ^ 2) := by
      have hcn := complexify_continuous.comp (continuous_subtype_val : Continuous (fun n : UnitSphere => (n : Position)))
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h : (∫ n : UnitSphere, ‖angularProjection n v‖ ^ 2 ∂sphereArea) +
      (∫ n : UnitSphere, ‖inner ℂ (complexify n) v‖ ^ 2 ∂sphereArea) =
      4 * Real.pi * ‖v‖ ^ 2 := by
    rw [← integral_add (angularProjection_square_integrable v) hint]
    simp only [angularProjection_pythagoras, integral_const, smul_eq_mul, sphereArea_real_univ]
  rw [sphere_inner_norm_sq] at h
  linarith

end QuarticMaxwell
