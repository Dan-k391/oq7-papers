import PrescribedExtinction.OutgoingDynamicIdentity
import PrescribedExtinction.NewtonFundamental

/-! The actual outgoing scalar Green function satisfies the Helmholtz
fundamental-solution identity in the original distribution space. The
Newtonian Dirac contribution is inherited from the proved contact identity;
the dynamic Hessian remainder has the actual radial Helmholtz trace. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory

theorem outgoingRadial_helmholtz (k r : ℝ) :
    outgoingRadialSecond k r + (2 / r : ℝ) • outgoingRadialFirst k r =
      -((k ^ 2 : ℝ) : ℂ) * outgoingRadial k r := by
  by_cases hr : r = 0
  · subst r
    simp [outgoingRadial, outgoingRadialFirst, outgoingRadialSecond]
  have hc : (((4 * Real.pi : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  simp only [outgoingRadial, outgoingRadialFirst, outgoingRadialSecond,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem radialHessian_trace (x : Position) (hx : x ≠ 0) (A B : ℂ) :
    (∑ i : Fin 3, ((x i * x i / ‖x‖ ^ 2) • A +
      (1 / ‖x‖ - x i * x i / ‖x‖ ^ 3) • B)) = A + (2 / ‖x‖ : ℝ) • B := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : (∑ i : Fin 3, x i * x i) = ‖x‖ ^ 2 := by
    simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq x).symm
  have hA : (∑ i : Fin 3, x i * x i / ‖x‖ ^ 2) = 1 := by
    rw [← Finset.sum_div, hn, div_self (pow_ne_zero 2 hr)]
  have hB : (∑ i : Fin 3, (1 / ‖x‖ - x i * x i / ‖x‖ ^ 3)) = 2 / ‖x‖ := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, hn]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, hA, hB, one_smul]

theorem dynamicHessianRemainder_trace (k : ℝ) (x : Position) :
    (∑ i : Fin 3, dynamicHessianRemainder k i i x) =
      -((k ^ 2 : ℝ) : ℂ) * outgoingGreen k x := by
  by_cases hx : x = 0
  · subst x
    simp [dynamicHessianRemainder, dyadicRemainder, classicalDyadic, outgoingGreen,
      outgoingRadial, outgoingRadialFirst, outgoingRadialSecond]
  simp_rw [dynamicHessianRemainder_eq_radial k _ _ x hx, ite_true]
  rw [radialHessian_trace x hx]
  rw [smul_sub]
  have he : (outgoingRadialSecond k ‖x‖ - outgoingRadialSecond 0 ‖x‖) +
      (2 / ‖x‖ : ℝ) • outgoingRadialFirst k ‖x‖ -
        (2 / ‖x‖ : ℝ) • outgoingRadialFirst 0 ‖x‖ =
      (outgoingRadialSecond k ‖x‖ + (2 / ‖x‖ : ℝ) • outgoingRadialFirst k ‖x‖) -
        (outgoingRadialSecond 0 ‖x‖ + (2 / ‖x‖ : ℝ) • outgoingRadialFirst 0 ‖x‖) := by
    abel
  rw [← add_sub_assoc, he, outgoingRadial_helmholtz k, outgoingRadial_helmholtz 0]
  simp only [zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, neg_zero, zero_mul,
    sub_zero, outgoingGreen_eq_radial]

theorem dynamicHessianRemainder_trace_distribution (k : ℝ) :
    (∑ i : Fin 3, Distribution.ofFun ⊤ (dynamicHessianRemainder k i i) volume ⊤) =
      -(k ^ 2) • outgoingGreenDistribution k := by
  have h0 := (dynamicHessianRemainder_locallyIntegrable k 0 0).locallyIntegrableOn ⊤
  have h1 := (dynamicHessianRemainder_locallyIntegrable k 1 1).locallyIntegrableOn ⊤
  have h2 := (dynamicHessianRemainder_locallyIntegrable k 2 2).locallyIntegrableOn ⊤
  rw [Fin.sum_univ_three, ← Distribution.ofFun_add h0 h1,
    ← Distribution.ofFun_add (h0.add h1) h2]
  have he : (dynamicHessianRemainder k 0 0 + dynamicHessianRemainder k 1 1) +
      dynamicHessianRemainder k 2 2 = -(k ^ 2) • outgoingGreen k := by
    funext x
    simpa only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
      Complex.ofReal_neg] using dynamicHessianRemainder_trace k x
  rw [he, Distribution.ofFun_smul]
  rfl

/-- Exact scalar Helmholtz fundamental solution, including the original
Newtonian Dirac coefficient and with no radiation or Maxwell identity assumed. -/
theorem outgoing_helmholtz_fundamental_distribution (k : ℝ) :
    (∑ i : Fin 3, greenHessian k i i) + (k ^ 2) • outgoingGreenDistribution k =
      -newtonDirac := by
  have hs : (∑ i : Fin 3, greenHessian k i i) =
      (∑ i : Fin 3, greenHessian 0 i i) +
        (∑ i : Fin 3, Distribution.ofFun ⊤ (dynamicHessianRemainder k i i) volume ⊤) := by
    calc
      _ = ∑ i : Fin 3, (greenHessian 0 i i +
          Distribution.ofFun ⊤ (dynamicHessianRemainder k i i) volume ⊤) :=
        Finset.sum_congr rfl (fun i _ => greenHessian_eq_static_add_dynamic k i i)
      _ = _ := Finset.sum_add_distrib
  rw [hs, newton_hessian_trace_distribution,
    dynamicHessianRemainder_trace_distribution]
  ext φ
  simp only [add_apply, neg_apply, smul_apply, Complex.real_smul, Complex.ofReal_neg]
  ring

theorem outgoing_helmholtz_fundamental_apply (k : ℝ) (φ : ScalarTest) :
    outgoingGreenDistribution k (testLaplacian φ) +
      (k ^ 2) • outgoingGreenDistribution k φ = -(φ 0 : ℂ) := by
  have h := congrArg (fun T : ScalarDistribution => T φ)
    (outgoing_helmholtz_fundamental_distribution k)
  simpa [Fin.sum_univ_three, greenHessian_apply, newtonDirac_apply,
    testLaplacian_apply] using h

theorem outgoingGreen_helmholtz_test_integral (k : ℝ) (φ : ScalarTest) :
    (∫ x : Position, ((testLaplacian φ) x + k ^ 2 * φ x) • outgoingGreen k x) =
      -(φ 0 : ℂ) := by
  have h := outgoing_helmholtz_fundamental_apply k φ
  simp only [outgoingGreenDistribution_apply] at h
  have hli := (outgoingGreen_locallyIntegrable k).locallyIntegrableOn ⊤
  have h1 := (testLaplacian φ).integrable_smul hli
  have h2 : Integrable (fun x : Position => (k ^ 2) • (φ x • outgoingGreen k x)) volume := by
    simpa only [Complex.real_smul] using
      (φ.integrable_smul hli).const_mul ((k ^ 2 : ℝ) : ℂ)
  simp_rw [add_smul, mul_smul]
  rw [integral_add h1 h2, integral_smul]
  exact h

end OQ7Prescribed
