import PrescribedExtinction.PoyntingCutoff
import PrescribedExtinction.NewtonShell
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

theorem exteriorCutoff_contDiff_smooth (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (exteriorCutoff r t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds (by simpa using hr)] with y hy
    exact exteriorCutoff_zero ht y hy.le
  · exact (Real.smoothTransition.contDiffAt (n := (⊤ : ℕ∞))).comp x
      (((contDiffAt_norm ℝ hx).sub contDiffAt_const).div_const t)

def sourceEnergyCutoff (r : ℝ) (x : Position) : ℝ := 1 - exteriorCutoff r r x
def sourceEnergyWeight (r : ℝ) (x : Position) : ℝ :=
  transitionDerivative ((‖x‖ - r) / r) / r

theorem sourceEnergyCutoff_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceEnergyCutoff r) :=
  contDiff_const.sub (exteriorCutoff_contDiff_smooth r r hr hr)

theorem sourceEnergyCutoff_hasCompactSupport (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (sourceEnergyCutoff r) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) (2 * r))
  intro x hx
  have hn : r + r ≤ ‖x‖ := by
    have hh : 2 * r < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    linarith
  simp [sourceEnergyCutoff, exteriorCutoff_one hr x hn]

theorem sourceEnergyWeight_nonneg (r : ℝ) (hr : 0 < r) (x : Position) :
    0 ≤ sourceEnergyWeight r x :=
  div_nonneg Real.smoothTransition.monotone.deriv_nonneg hr.le

theorem sourceEnergyWeight_zero_inner (r : ℝ) (hr : 0 < r) (x : Position) (hx : ‖x‖ ≤ r) :
    sourceEnergyWeight r x = 0 := by
  unfold sourceEnergyWeight
  rw [transitionDerivative_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hr.le)]
  simp

theorem sourceEnergyWeight_zero_outer (r : ℝ) (hr : 0 < r) (x : Position) (hx : 2 * r ≤ ‖x‖) :
    sourceEnergyWeight r x = 0 := by
  unfold sourceEnergyWeight
  rw [transitionDerivative_zero_of_one_le ((le_div_iff₀ hr).mpr (by linarith))]
  simp

theorem sourceEnergyCutoff_gradient (r : ℝ) (hr : 0 < r) (x : Position) :
    scalarGradient (sourceEnergyCutoff r) x = -(sourceEnergyWeight r x) • radialDirection x := by
  ext j
  have hline := (exteriorCutoff_hasLineDerivAt r r hr hr j x).const_sub 1
  change HasLineDerivAt ℝ (sourceEnergyCutoff r) (-(exteriorCutoffPartial r r j x)) x (basisR j) at hline
  have hd := hline.lineDeriv.symm.trans
    (((sourceEnergyCutoff_contDiff r hr).differentiable (by simp) x).lineDeriv_eq_fderiv)
  change fderiv ℝ (sourceEnergyCutoff r) x (basisR j) = _
  rw [← hd]
  simp [sourceEnergyWeight, exteriorCutoffPartial, radialDirection, PiLp.smul_apply]
  ring

theorem sourceEnergyCutoff_current_work (p : CompactPolarization) (E : Field)
    (r : ℝ) (hr : 0 < r) (hpr : p.radius ≤ r) :
    (fun x : Position => (sourceEnergyCutoff r x : ℂ) * pairing (p.current x) (E x)) =
      (fun x => pairing (p.current x) (E x)) := by
  funext x
  by_cases hx : ‖x‖ ≤ r
  · simp [sourceEnergyCutoff, exteriorCutoff_zero hr x hx]
  · have hv := p.vanish x (hpr.trans_lt (lt_of_not_ge hx))
    simp [hv, pairing]

theorem cross_complexify_real_smul (H : Vector) (n : Position) (r : ℝ) :
    cross H (complexify (r • n)) = r • cross H (complexify n) := by
  ext i
  fin_cases i <;> simp [cross, complexify, PiLp.smul_apply, Complex.real_smul] <;> ring

theorem pairing_real_smul_right (E v : Vector) (r : ℝ) :
    pairing E (r • v) = (r : ℂ) * pairing E v := by
  simp [pairing, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum, mul_left_comm]

theorem smoothPhysicalSource_radial_energy (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (r : ℝ) (hr : 0 < r) (hpr : p.radius ≤ r) :
    k * (∫ x : Position, pairing (p.current x) (smoothElectricSource k p x)).im =
      ∫ x : Position, sourceEnergyWeight r x * (pairing (smoothElectricSource k p x)
        (cross (smoothMagneticSource k p x) (complexify (radialDirection x)))).re := by
  have h := smoothPhysicalSource_cutoff_energy k p hp (sourceEnergyCutoff r)
    (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  rw [sourceEnergyCutoff_current_work p _ r hr hpr] at h
  have heq : (fun x : Position => (pairing (smoothElectricSource k p x)
      (cross (smoothMagneticSource k p x) (complexify (scalarGradient (sourceEnergyCutoff r) x)))).re) =
      (fun x => -(sourceEnergyWeight r x * (pairing (smoothElectricSource k p x)
        (cross (smoothMagneticSource k p x) (complexify (radialDirection x)))).re)) := by
    funext x
    rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, pairing_real_smul_right]
    simp [Complex.mul_re]
  rw [heq, integral_neg, neg_neg] at h
  exact h

theorem sourceEnergyWeight_le (r M : ℝ) (hr : 0 < r)
    (hM : ∀ s : ℝ, transitionDerivative s ≤ M) (x : Position) :
    sourceEnergyWeight r x ≤ M / r :=
  div_le_div_of_nonneg_right (hM _) hr.le

theorem sourceEnergyWeight_continuous (r : ℝ) : Continuous (sourceEnergyWeight r) :=
  (transitionDerivative_continuous.comp ((continuous_norm.sub continuous_const).div_const r)).div_const r

theorem sourceEnergyWeight_hasCompactSupport (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (sourceEnergyWeight r) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) (2 * r))
  intro x hx
  apply sourceEnergyWeight_zero_outer r hr x
  exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).le

theorem smooth_cutoff_flux_integrable (k : ℝ) (E H : Field)
    (hE : ContDiff ℝ (⊤ : ℕ∞) E) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (he : curl E = fun x => (Complex.I * (k : ℂ)) • H x)
    (ψ : Position → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x : Position => (pairing (E x)
      (cross (H x) (complexify (scalarGradient ψ x)))).re) volume := by
  let φ : Field := ψ • (fun x => vectorConjugate (E x))
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.smul (vectorConjugate_contDiff E hE)
  have hsφ : HasCompactSupport φ := HasCompactSupport.smul_right
    (f' := fun x => vectorConjugate (E x)) hs
  have hi := compactField_bilinear_integrable H hH.continuous.locallyIntegrable
    (curl φ) (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  exact hi.re.congr (ae_of_all _ fun x => cutoff_curl_pairing_real ψ E H k hψ hE he x)

theorem smoothPhysicalSource_radial_flux_integrable (k : ℝ) (p : CompactPolarization)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p.current) (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : Position => sourceEnergyWeight r x * (pairing (smoothElectricSource k p x)
      (cross (smoothMagneticSource k p x) (complexify (radialDirection x)))).re) volume := by
  have hi := smooth_cutoff_flux_integrable k _ _ (smoothElectricSource_contDiff k p hp)
    (smoothMagneticSource_contDiff k p hp) (smoothElectricSource_curl k p hp)
    (sourceEnergyCutoff r) (sourceEnergyCutoff_contDiff r hr) (sourceEnergyCutoff_hasCompactSupport r hr)
  apply hi.neg.congr
  apply ae_of_all
  intro x
  change -(pairing (smoothElectricSource k p x)
    (cross (smoothMagneticSource k p x) (complexify (scalarGradient (sourceEnergyCutoff r) x)))).re = _
  rw [sourceEnergyCutoff_gradient r hr, cross_complexify_real_smul, pairing_real_smul_right]
  simp [Complex.mul_re]

end OQ7Prescribed
