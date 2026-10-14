import PrescribedExtinction.SphereMeasure

/-! Exact second moments for Mathlib's actual Euclidean unit-sphere measure.
These fix the normalization needed for the Newtonian Dirac boundary term. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set

def coordinateSwap (i j : Fin 3) : Position ≃ₗᵢ[ℝ] Position :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

def coordinateReflect (i : Fin 3) : Position ≃ₗᵢ[ℝ] Position :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

theorem coordinateSwap_apply (i j a : Fin 3) (x : Position) :
    coordinateSwap i j x a = x (Equiv.swap i j a) := by
  simp [coordinateSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem coordinateReflect_apply (i j : Fin 3) (x : Position) :
    coordinateReflect i x j = if j = i then -x j else x j := by
  simp [coordinateReflect, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> simp

theorem sphere_coordinate_mul_integrable (i j : Fin 3) :
    Integrable (fun n : UnitSphere => (n : Position) i * (n : Position) j) sphereArea := by
  have hc : Continuous (fun n : UnitSphere => (n : Position) i * (n : Position) j) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sphere_coordinate_cross_zero (i j : Fin 3) (hij : i ≠ j) :
    (∫ n : UnitSphere, (n : Position) i * (n : Position) j ∂sphereArea) = 0 := by
  have h := sphere_integral_orthogonal (coordinateReflect i)
    (fun n : UnitSphere => (n : Position) i * (n : Position) j)
  change (∫ n : UnitSphere, coordinateReflect i n i * coordinateReflect i n j ∂sphereArea) = _ at h
  simp [coordinateReflect_apply, hij.symm, integral_neg] at h
  linarith

theorem sphere_coordinate_sq_equal (i j : Fin 3) :
    (∫ n : UnitSphere, (n : Position) i ^ 2 ∂sphereArea) =
      ∫ n : UnitSphere, (n : Position) j ^ 2 ∂sphereArea := by
  have h := sphere_integral_orthogonal (coordinateSwap i j)
    (fun n : UnitSphere => (n : Position) j ^ 2)
  change (∫ n : UnitSphere, coordinateSwap i j n j ^ 2 ∂sphereArea) = _ at h
  simpa only [coordinateSwap_apply, Equiv.swap_apply_right] using h

theorem unitSphere_sum_sq (n : UnitSphere) : ∑ i : Fin 3, (n : Position) i ^ 2 = 1 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (n : Position)
  simpa only [unitSphere_norm, one_pow, Real.norm_eq_abs, sq_abs] using h.symm

theorem sphere_coordinate_sq_integral (i : Fin 3) :
    (∫ n : UnitSphere, (n : Position) i ^ 2 ∂sphereArea) = (4 * Real.pi) / 3 := by
  have hs : (∑ j : Fin 3, ∫ n : UnitSphere, (n : Position) j ^ 2 ∂sphereArea) = 4 * Real.pi := by
    rw [← integral_finsetSum]
    · simp only [unitSphere_sum_sq, integral_const, smul_eq_mul, mul_one, sphereArea_real_univ]
    · intro j _
      simpa only [sq] using sphere_coordinate_mul_integrable j j
  have he : (∑ j : Fin 3, ∫ n : UnitSphere, (n : Position) j ^ 2 ∂sphereArea) =
      3 * (∫ n : UnitSphere, (n : Position) i ^ 2 ∂sphereArea) := by
    simp_rw [sphere_coordinate_sq_equal _ i]
    simp
  rw [he] at hs
  linarith

theorem sphere_second_moment (i j : Fin 3) :
    (∫ n : UnitSphere, (n : Position) i * (n : Position) j ∂sphereArea) =
      if i = j then (4 * Real.pi) / 3 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [← sq] using sphere_coordinate_sq_integral i
  · simpa [hij] using sphere_coordinate_cross_zero i j hij

theorem sphere_newton_angular_cancellation (i j : Fin 3) :
    (∫ n : UnitSphere, (3 * (n : Position) i * (n : Position) j -
      (if i = j then 1 else 0)) ∂sphereArea) = 0 := by
  rw [integral_sub]
  · simp only [mul_assoc, integral_const_mul, sphere_second_moment, integral_const,
      smul_eq_mul, sphereArea_real_univ]
    split_ifs <;> ring
  · simpa only [mul_assoc] using (sphere_coordinate_mul_integrable i j).const_mul 3
  · exact integrable_const _

end OQ7Prescribed
