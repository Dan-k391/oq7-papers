import PrescribedExtinction.RemainderConvolution
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Regularity of the actual outgoing-minus-static scalar Green kernel.
The formulas below are proved derivatives away from the origin.  Their
boundedness at the puncture is the input for a separate removable-point
distributional integration-by-parts argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

local instance : NormedAddCommGroup (Vector →L[ℂ] Vector) := inferInstance
local instance : NormedSpace ℂ (Vector →L[ℂ] Vector) := inferInstance
local instance : NormedAddCommGroup ((Vector →L[ℂ] Vector) →L[ℂ] Vector) := inferInstance
local instance : NormedSpace ℂ ((Vector →L[ℂ] Vector) →L[ℂ] Vector) := inferInstance

def dynamicScalarRemainder (k : ℝ) (x : Position) : ℂ :=
  outgoingGreen k x - outgoingGreen 0 x

def dynamicGradientRemainder (k : ℝ) (j : Fin 3) (x : Position) : ℂ :=
  (x j / ‖x‖) • (outgoingRadialFirst k ‖x‖ - outgoingRadialFirst 0 ‖x‖)

def dynamicHessianRemainder (k : ℝ) (i j : Fin 3) (x : Position) : ℂ :=
  dyadicRemainder k x (basisC j) i -
    (if i = j then ((k ^ 2 : ℝ) : ℂ) * outgoingGreen k x else 0)

theorem outgoingRadial_contDiffAt (k r : ℝ) (hr : r ≠ 0) :
    ContDiffAt ℝ 1 (outgoingRadial k) r := by
  change ContDiffAt ℝ 1
    (fun y : ℝ => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) /
      (((4 * Real.pi : ℝ) : ℂ)) / (y : ℂ)) r
  have hc : ContDiffAt ℝ 1 (fun y : ℝ => (y : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hz : ContDiffAt ℝ 1 (fun y : ℝ => Complex.I * (k : ℂ) * (y : ℂ)) r :=
    contDiffAt_const.mul hc
  convert! (((hz.cexp).div_const
    (((4 * Real.pi : ℝ) : ℂ))).mul (hc.inv (Complex.ofReal_ne_zero.mpr hr))) using 1

theorem outgoingRadialFirst_contDiffAt (k r : ℝ) (hr : r ≠ 0) :
    ContDiffAt ℝ 1 (outgoingRadialFirst k) r := by
  change ContDiffAt ℝ 1
    (fun y : ℝ => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
      (Complex.I * (k : ℂ) * (y : ℂ) - 1) /
        (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ) ^ 2)) r
  have hc : ContDiffAt ℝ 1 (fun y : ℝ => (y : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hz : ContDiffAt ℝ 1 (fun y : ℝ => Complex.I * (k : ℂ) * (y : ℂ)) r :=
    contDiffAt_const.mul hc
  have hden : ContDiffAt ℝ 1
      (fun y : ℝ => (((4 * Real.pi : ℝ) : ℂ)) * (y : ℂ) ^ 2) r :=
    contDiffAt_const.mul (hc.pow 2)
  convert!
    (hz.cexp.mul (hz.sub (show ContDiffAt ℝ 1 (fun _ : ℝ => (1 : ℂ)) r from
      contDiffAt_const))).mul
      (hden.inv
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
          (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr)))) using 1

theorem dynamicScalarRemainder_contDiffAt (k : ℝ) (x : Position) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (dynamicScalarRemainder k) x := by
  have hn : ContDiffAt ℝ 1 (fun y : Position => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have he : dynamicScalarRemainder k =
      fun y : Position => outgoingRadial k ‖y‖ - outgoingRadial 0 ‖y‖ := by
    funext y
    simp only [dynamicScalarRemainder, outgoingGreen_eq_radial]
  rw [he]
  exact ((outgoingRadial_contDiffAt k ‖x‖ hr).comp x hn).sub
      ((outgoingRadial_contDiffAt 0 ‖x‖ hr).comp x hn)

theorem dynamicGradientRemainder_contDiffAt (k : ℝ) (j : Fin 3)
    (x : Position) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (dynamicGradientRemainder k j) x := by
  have hn : ContDiffAt ℝ 1 (fun y : Position => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc : ContDiffAt ℝ 1 (fun y : Position => y j) x :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Position →L[ℝ] ℝ).contDiff.contDiffAt
  change ContDiffAt ℝ 1
    (fun y : Position => (y j / ‖y‖) •
      (outgoingRadialFirst k ‖y‖ - outgoingRadialFirst 0 ‖y‖)) x
  exact (hc.div hn hr).smul
    (((outgoingRadialFirst_contDiffAt k ‖x‖ hr).comp x hn).sub
      ((outgoingRadialFirst_contDiffAt 0 ‖x‖ hr).comp x hn))

theorem dynamicScalarRemainder_hasLineDerivAt (k : ℝ) (j : Fin 3)
    (x : Position) (hx : x ≠ 0) :
    HasLineDerivAt ℝ (dynamicScalarRemainder k)
      (dynamicGradientRemainder k j x) x (basisR j) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := ((outgoingRadial_hasDerivAt k ‖x‖ hr).sub
    (outgoingRadial_hasDerivAt 0 ‖x‖ hr)).hasFDerivAt.comp x
      (radialNorm_hasFDerivAt x hx)
  have he : dynamicScalarRemainder k =
      fun y : Position => (outgoingRadial k - outgoingRadial 0) ‖y‖ := by
    funext y
    simp only [dynamicScalarRemainder, outgoingGreen_eq_radial, Pi.sub_apply]
  rw [he]
  convert! h.hasLineDerivAt (basisR j) using 1
  simp [dynamicGradientRemainder, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_apply, innerSL_apply_apply,
    real_inner_basis, div_eq_mul_inv]
  ring

theorem dynamicHessianRemainder_eq_radial (k : ℝ) (i j : Fin 3)
    (x : Position) (hx : x ≠ 0) :
    dynamicHessianRemainder k i j x =
      (x i * x j / ‖x‖ ^ 2) •
        (outgoingRadialSecond k ‖x‖ - outgoingRadialSecond 0 ‖x‖) +
      ((if i = j then 1 else 0) / ‖x‖ - x i * x j / ‖x‖ ^ 3) •
        (outgoingRadialFirst k ‖x‖ - outgoingRadialFirst 0 ‖x‖) := by
  unfold dynamicHessianRemainder dyadicRemainder
  change (classicalDyadic k x (basisC j) i - classicalDyadic 0 x (basisC j) i) - _ = _
  rw [classicalDyadic_coordinate k x hx i j, classicalDyadic_coordinate 0 x hx i j,
    outgoing_classical_hessian k x hx i j, outgoing_classical_hessian 0 x hx i j]
  simp only [smul_sub]
  split_ifs <;> simp <;> abel

theorem dynamicGradientRemainder_hasLineDerivAt (k : ℝ) (i j : Fin 3)
    (x : Position) (hx : x ≠ 0) :
    HasLineDerivAt ℝ (dynamicGradientRemainder k j)
      (dynamicHessianRemainder k i j x) x (basisR i) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn := radialNorm_hasFDerivAt x hx
  have hi := (hasFDerivAt_inv hr.ne').comp x hn
  have hc := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Position →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hd := ((outgoingRadialFirst_hasDerivAt k ‖x‖ hr.ne').sub
    (outgoingRadialFirst_hasDerivAt 0 ‖x‖ hr.ne')).hasFDerivAt.comp x hn
  have hg := (hc.mul hi).smul hd
  rw [dynamicHessianRemainder_eq_radial k i j x hx]
  convert hg.hasLineDerivAt (basisR i) using 1
  · funext y
    rfl
  · simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]
    split_ifs with hij <;>
      simp [hij, basisR, PiLp.inner_apply, RCLike.inner_apply,
        Complex.real_smul, div_eq_mul_inv] <;> ring

theorem dynamicScalarRemainder_eq_cancel (k : ℝ) (x : Position) :
    dynamicScalarRemainder k x =
      (Complex.exp (Complex.I * (k : ℂ) * (‖x‖ : ℂ)) - 1) /
        (((4 * Real.pi : ℝ) : ℂ) * (‖x‖ : ℂ)) := by
  by_cases hx : x = 0
  · subst x
    simp [dynamicScalarRemainder, outgoingGreen]
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hc : (((4 * Real.pi : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [dynamicScalarRemainder, outgoingGreen_eq_radial, outgoingRadial,
    Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
  field_simp

theorem outgoingRadialFirst_sub_static (k r : ℝ) :
    outgoingRadialFirst k r - outgoingRadialFirst 0 r =
      (Complex.exp (Complex.I * (k : ℂ) * (r : ℂ)) *
        (Complex.I * (k : ℂ) * (r : ℂ) - 1) + 1) /
          (((4 * Real.pi : ℝ) : ℂ) * (r : ℂ) ^ 2) := by
  simp only [outgoingRadialFirst, Complex.ofReal_zero, mul_zero,
    zero_mul, Complex.exp_zero, zero_sub, one_mul, ← sub_div]
  congr 1
  ring

def dynamicScalarBound (k R : ℝ) : ℝ :=
  |k| / (4 * Real.pi) * (1 + |k| * R * Real.exp (|k| * R))

def dynamicGradientBound (k R : ℝ) : ℝ :=
  k ^ 2 / (4 * Real.pi) * (1 + (|k| * R + 1) * Real.exp (|k| * R))

theorem dynamicScalarBound_nonneg (k R : ℝ) (hR : 0 ≤ R) :
    0 ≤ dynamicScalarBound k R := by
  unfold dynamicScalarBound
  positivity

theorem dynamicGradientBound_nonneg (k R : ℝ) (hR : 0 ≤ R) :
    0 ≤ dynamicGradientBound k R := by
  unfold dynamicGradientBound
  positivity

theorem dynamicScalarRemainder_norm_le (k : ℝ) (x : Position) :
    ‖dynamicScalarRemainder k x‖ ≤ dynamicScalarBound k ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [dynamicScalarRemainder, outgoingGreen, dynamicScalarBound]
    positivity
  let r : ℝ := ‖x‖
  let c : ℝ := 4 * Real.pi
  let z : ℂ := Complex.I * (k : ℂ) * (r : ℂ)
  let s : ℝ := |k| * r
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hc : 0 < c := by dsimp [c]; positivity
  have hz : ‖z‖ = s := by simp [z, s, abs_of_pos hr]
  have he : ‖Complex.exp z - 1‖ ≤ s + s ^ 2 * Real.exp s := by
    calc
      _ = ‖z + (Complex.exp z - 1 - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖Complex.exp z - 1 - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ‖z‖ ^ 2 * Real.exp ‖z‖ := add_le_add_right (exp_remainder_two_norm z) _
      _ = _ := by rw [hz]
  rw [dynamicScalarRemainder_eq_cancel]
  change ‖(Complex.exp z - 1) / ((c : ℂ) * (r : ℂ))‖ ≤ _
  calc
    _ = ‖Complex.exp z - 1‖ / (c * r) := by simp [abs_of_pos hc, abs_of_pos hr]
    _ ≤ (s + s ^ 2 * Real.exp s) / (c * r) := div_le_div_of_nonneg_right he (by positivity)
    _ = dynamicScalarBound k ‖x‖ := by
      unfold dynamicScalarBound
      dsimp [s, c, r]
      field_simp

theorem dynamicScalarRemainder_norm_le_on_ball (k R : ℝ)
    (x : Position) (hx : ‖x‖ ≤ R) :
    ‖dynamicScalarRemainder k x‖ ≤ dynamicScalarBound k R := by
  apply (dynamicScalarRemainder_norm_le k x).trans
  unfold dynamicScalarBound
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  gcongr

theorem outgoingRadialFirst_sub_static_norm_le (k r : ℝ) (hr : 0 < r) :
    ‖outgoingRadialFirst k r - outgoingRadialFirst 0 r‖ ≤ dynamicGradientBound k r := by
  let c : ℝ := 4 * Real.pi
  let z : ℂ := Complex.I * (k : ℂ) * (r : ℂ)
  let s : ℝ := |k| * r
  have hc : 0 < c := by dsimp [c]; positivity
  have hz : ‖z‖ = s := by simp [z, s, abs_of_pos hr]
  have he := green_first_cancel_norm z
  rw [hz] at he
  rw [outgoingRadialFirst_sub_static]
  change ‖(Complex.exp z * (z - 1) + 1) / ((c : ℂ) * (r : ℂ) ^ 2)‖ ≤ _
  calc
    _ = ‖Complex.exp z * (z - 1) + 1‖ / (c * r ^ 2) := by
      simp [norm_pow, abs_of_pos hc, abs_of_pos hr]
    _ ≤ (s ^ 2 * (1 + (s + 1) * Real.exp s)) / (c * r ^ 2) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = dynamicGradientBound k r := by
      unfold dynamicGradientBound
      dsimp [s, c]
      simp only [mul_pow, sq_abs]
      field_simp

theorem dynamicGradientRemainder_norm_le (k : ℝ) (j : Fin 3) (x : Position) :
    ‖dynamicGradientRemainder k j x‖ ≤ dynamicGradientBound k ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [dynamicGradientRemainder, norm_zero, PiLp.zero_apply,
      zero_div, zero_smul, norm_zero, dynamicGradientBound]
    positivity
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcoord : ‖x j / ‖x‖‖ ≤ 1 := by
    rw [norm_div, Real.norm_of_nonneg (norm_nonneg x)]
    exact (div_le_one hr).mpr (PiLp.norm_apply_le x j)
  calc
    _ = ‖x j / ‖x‖‖ * ‖outgoingRadialFirst k ‖x‖ - outgoingRadialFirst 0 ‖x‖‖ := norm_smul _ _
    _ ≤ 1 * dynamicGradientBound k ‖x‖ :=
      mul_le_mul hcoord (outgoingRadialFirst_sub_static_norm_le k ‖x‖ hr)
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem dynamicGradientRemainder_norm_le_on_ball (k R : ℝ) (j : Fin 3)
    (x : Position) (hx : ‖x‖ ≤ R) :
    ‖dynamicGradientRemainder k j x‖ ≤ dynamicGradientBound k R := by
  apply (dynamicGradientRemainder_norm_le k j x).trans
  unfold dynamicGradientBound
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  gcongr

theorem dynamicScalarRemainder_locallyIntegrable (k : ℝ) :
    LocallyIntegrable (dynamicScalarRemainder k) volume :=
  (outgoingGreen_locallyIntegrable k).sub (outgoingGreen_locallyIntegrable 0)

theorem dynamicGradientRemainder_measurable (k : ℝ) (j : Fin 3) :
    Measurable (dynamicGradientRemainder k j) := by
  unfold dynamicGradientRemainder outgoingRadialFirst
  fun_prop

theorem dynamicGradientRemainder_locallyIntegrable (k : ℝ) (j : Fin 3) :
    LocallyIntegrable (dynamicGradientRemainder k j) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  apply Integrable.of_bound (dynamicGradientRemainder_measurable k j).aestronglyMeasurable.restrict
    (dynamicGradientBound k R)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact dynamicGradientRemainder_norm_le_on_ball k R j x (hKR x hx).le

theorem dyadicRemainder_memLp_on_compact (k : ℝ) (K : Set Position) (hK : IsCompact K) :
    MemLp (dyadicRemainder k) 2 (volume.restrict K) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  have he : cutoffDyadicRemainder k R =ᵐ[volume.restrict K] dyadicRemainder k := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simp only [cutoffDyadicRemainder, indicator_of_mem
      (show x ∈ Metric.closedBall 0 R from by simpa using (hKR x hx).le)]
  exact (memLp_congr_ae he).mp ((cutoffDyadicRemainder_memLp k R).restrict K)

theorem dynamicHessianRemainder_memLp_on_compact (k : ℝ) (i j : Fin 3)
    (K : Set Position) (hK : IsCompact K) :
    MemLp (dynamicHessianRemainder k i j) 2 (volume.restrict K) := by
  change MemLp (fun x => dyadicRemainder k x (basisC j) i -
    (if i = j then ((k ^ 2 : ℝ) : ℂ) * outgoingGreen k x else 0)) 2 (volume.restrict K)
  have hd := (dyadicRemainder_memLp_on_compact k K hK).continuousLinearMap_comp
    ((PiLp.proj 2 (fun _ : Fin 3 => ℂ) i).comp
      ((ContinuousLinearMap.apply ℂ Vector) (basisC j)))
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    change MemLp ((fun x => dyadicRemainder k x (basisC j) i) -
      (fun x => ((k ^ 2 : ℝ) : ℂ) * outgoingGreen k x)) 2 (volume.restrict K)
    exact hd.sub ((outgoingGreen_memLp_on_compact k K hK).const_mul ((k ^ 2 : ℝ) : ℂ))
  · simp only [ite_eq_right hij, sub_zero]
    exact hd

theorem dynamicHessianRemainder_locallyIntegrable (k : ℝ) (i j : Fin 3) :
    LocallyIntegrable (dynamicHessianRemainder k i j) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_one_iff_integrable.mp
    ((dynamicHessianRemainder_memLp_on_compact k i j K hK).mono_exponent (by norm_num))

end OQ7Prescribed
