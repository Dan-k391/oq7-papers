import PrescribedExtinction.GreenCancellation
import PrescribedExtinction.StaticFourier

/-! The actual classical dyadic kernel and its dynamic-minus-static cancellation
off the origin. Equality with the full distributional operator, including the
Newtonian contact term, remains a separate obligation. -/
noncomputable section
namespace OQ7Prescribed

def classicalDyadic (k : ℝ) (x : Position) : Vector →L[ℂ] Vector :=
  (((k ^ 2 : ℝ) : ℂ) * outgoingRadial k ‖x‖ +
    outgoingRadialFirst k ‖x‖ / (‖x‖ : ℂ)) • ContinuousLinearMap.id ℂ Vector +
  (outgoingRadialSecond k ‖x‖ / (‖x‖ : ℂ) ^ 2 -
    outgoingRadialFirst k ‖x‖ / (‖x‖ : ℂ) ^ 3) •
      InnerProductSpace.rankOne ℂ (complexify x) (complexify x)

def dyadicRemainder (k : ℝ) (x : Position) : Vector →L[ℂ] Vector :=
  classicalDyadic k x - classicalDyadic 0 x

theorem classicalDyadic_coordinate (k : ℝ) (x : Position) (hx : x ≠ 0) (i j : Fin 3) :
    classicalDyadic k x (basisC j) i =
      (if i = j then ((k ^ 2 : ℝ) : ℂ) * outgoingGreen k x else 0) +
        lineDeriv ℝ (fun y : Position => lineDeriv ℝ (outgoingGreen k) y (basisR j))
          x (basisR i) := by
  rw [outgoing_classical_hessian k x hx i j, outgoingGreen_eq_radial]
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  simp only [classicalDyadic, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.rankOne_apply]
  simp [basisC, complexify, PiLp.inner_apply, RCLike.inner_apply, Complex.real_smul]
  split_ifs with hij <;> simp [hij] <;> field_simp <;> ring

theorem dyadicRemainder_cancel (k : ℝ) (x : Position) :
    dyadicRemainder k x =
      (((k ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) /
          ((((4 * Real.pi : ℝ) : ℂ)) * (‖x‖ : ℂ)) +
        (Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) *
          (Complex.I * (k : ℂ) * (‖x‖ : ℂ) - 1) + 1) /
            ((((4 * Real.pi : ℝ) : ℂ)) * (‖x‖ : ℂ) ^ 3)) •
              ContinuousLinearMap.id ℂ Vector +
      ((Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) *
          ((Complex.I * (k : ℂ) * (‖x‖ : ℂ)) ^ 2 -
            3 * (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) + 3) - 3) /
          ((((4 * Real.pi : ℝ) : ℂ)) * (‖x‖ : ℂ) ^ 5)) •
            InnerProductSpace.rankOne ℂ (complexify x) (complexify x) := by
  by_cases hx : x = 0
  · subst x
    simp [dyadicRemainder, classicalDyadic, outgoingRadial,
      outgoingRadialFirst, outgoingRadialSecond]
    exact (zero_smul ℂ (ContinuousLinearMap.id ℂ Vector)).symm
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hc : (((4 * Real.pi : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  ext v i
  simp [dyadicRemainder, classicalDyadic, outgoingRadial, outgoingRadialFirst,
    outgoingRadialSecond, Complex.ofReal_pow]
  field_simp
  ring

def greenCancellationEnvelope (s : ℝ) : ℝ :=
  4 + s + (s ^ 2 + 4 * s + 4) * Real.exp s

theorem greenCancellationEnvelope_nonneg (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ greenCancellationEnvelope s := by
  unfold greenCancellationEnvelope
  positivity

theorem greenCancellationEnvelope_mono (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    greenCancellationEnvelope s ≤ greenCancellationEnvelope t := by
  unfold greenCancellationEnvelope
  have ht : 0 ≤ t := hs.trans hst
  gcongr

theorem dyadicRemainder_norm_le (k : ℝ) (x : Position) :
    ‖dyadicRemainder k x‖ ≤
      (k ^ 2 / (4 * Real.pi)) * greenCancellationEnvelope (|k| * ‖x‖) * ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp [dyadicRemainder, classicalDyadic, outgoingRadial,
      outgoingRadialFirst, outgoingRadialSecond]
  let r : ℝ := ‖x‖
  let c : ℝ := 4 * Real.pi
  let z : ℂ := Complex.I * (k : ℂ) * (r : ℂ)
  let s : ℝ := |k| * r
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hc : 0 < c := by dsimp [c]; positivity
  have hz : ‖z‖ = s := by simp [z, s, abs_of_pos hr]
  have he : ‖Complex.exp z‖ = 1 := by simp [z, Complex.norm_exp]
  have hA := green_first_cancel_norm z
  have hB := green_second_cancel_norm z
  rw [hz] at hA hB
  have hRank : ‖InnerProductSpace.rankOne ℂ (complexify x) (complexify x)‖ = r ^ 2 := by
    rw [InnerProductSpace.norm_rankOne, ← sq, complexify_norm_sq]
  rw [dyadicRemainder_cancel]
  change ‖(((k ^ 2 : ℝ) : ℂ) * Complex.exp z / ((c : ℂ) * (r : ℂ)) +
      (Complex.exp z * (z - 1) + 1) / ((c : ℂ) * (r : ℂ) ^ 3)) •
        ContinuousLinearMap.id ℂ Vector +
    ((Complex.exp z * (z ^ 2 - 3 * z + 3) - 3) / ((c : ℂ) * (r : ℂ) ^ 5)) •
      InnerProductSpace.rankOne ℂ (complexify x) (complexify x)‖ ≤ _
  calc
    _ ≤ ‖(((k ^ 2 : ℝ) : ℂ) * Complex.exp z / ((c : ℂ) * (r : ℂ)) +
        (Complex.exp z * (z - 1) + 1) / ((c : ℂ) * (r : ℂ) ^ 3)) •
          ContinuousLinearMap.id ℂ Vector‖ +
      ‖((Complex.exp z * (z ^ 2 - 3 * z + 3) - 3) / ((c : ℂ) * (r : ℂ) ^ 5)) •
        InnerProductSpace.rankOne ℂ (complexify x) (complexify x)‖ := norm_add_le _ _
    _ = ‖((k ^ 2 : ℝ) : ℂ) * Complex.exp z / ((c : ℂ) * (r : ℂ)) +
        (Complex.exp z * (z - 1) + 1) / ((c : ℂ) * (r : ℂ) ^ 3)‖ +
      ‖(Complex.exp z * (z ^ 2 - 3 * z + 3) - 3) / ((c : ℂ) * (r : ℂ) ^ 5)‖ * r ^ 2 := by
        simp only [norm_smul, ContinuousLinearMap.norm_id, mul_one, hRank]
    _ ≤ (‖((k ^ 2 : ℝ) : ℂ) * Complex.exp z / ((c : ℂ) * (r : ℂ))‖ +
        ‖(Complex.exp z * (z - 1) + 1) / ((c : ℂ) * (r : ℂ) ^ 3)‖) +
      ‖(Complex.exp z * (z ^ 2 - 3 * z + 3) - 3) / ((c : ℂ) * (r : ℂ) ^ 5)‖ * r ^ 2 := by
        gcongr
        exact norm_add_le _ _
    _ = (k ^ 2 / (c * r) + ‖Complex.exp z * (z - 1) + 1‖ / (c * r ^ 3)) +
      (‖Complex.exp z * (z ^ 2 - 3 * z + 3) - 3‖ / (c * r ^ 5)) * r ^ 2 := by
        simp [norm_pow, he, abs_of_pos hc, abs_of_pos hr]
    _ ≤ (k ^ 2 / (c * r) + (s ^ 2 * (1 + (s + 1) * Real.exp s)) / (c * r ^ 3)) +
      ((s ^ 2 * (s + 2 + (s ^ 2 + 3 * s + 3) * Real.exp s)) / (c * r ^ 5)) * r ^ 2 := by
        gcongr
    _ = _ := by
        change _ = (k ^ 2 / c) * greenCancellationEnvelope s * r⁻¹
        unfold greenCancellationEnvelope
        dsimp [s]
        simp only [mul_pow, sq_abs]
        field_simp
        ring

theorem dyadicRemainder_norm_le_on_ball (k R : ℝ) (x : Position) (hx : ‖x‖ ≤ R) :
    ‖dyadicRemainder k x‖ ≤
      (k ^ 2 / (4 * Real.pi)) * greenCancellationEnvelope (|k| * R) * ‖x‖⁻¹ := by
  apply (dyadicRemainder_norm_le k x).trans
  gcongr
  exact greenCancellationEnvelope_mono _ _ (by positivity)
    (mul_le_mul_of_nonneg_left hx (abs_nonneg k))

theorem rankOne_complexify_continuous :
    Continuous (fun x : Position => InnerProductSpace.rankOne ℂ (complexify x) (complexify x)) := by
  have hi : Continuous (fun x : Position => innerSL ℂ (complexify x)) :=
    (innerSL ℂ).continuous.comp complexify_continuous
  have hs : Continuous (fun x : Position => ContinuousLinearMap.toSpanSingleton ℂ (complexify x)) := by
    change Continuous (fun x : Position =>
      ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] Vector →L[ℂ] Vector).flip) (complexify x))
    exact ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] Vector →L[ℂ] Vector).flip).continuous.comp
      complexify_continuous
  simpa only [InnerProductSpace.rankOne_def'] using hs.clm_comp hi

theorem classicalDyadic_measurable (k : ℝ) : Measurable (classicalDyadic k) := by
  have hr := rankOne_complexify_continuous.measurable
  unfold classicalDyadic outgoingRadial outgoingRadialFirst outgoingRadialSecond
  fun_prop

theorem dyadicRemainder_measurable (k : ℝ) : Measurable (dyadicRemainder k) :=
  (classicalDyadic_measurable k).sub (classicalDyadic_measurable 0)

end OQ7Prescribed
