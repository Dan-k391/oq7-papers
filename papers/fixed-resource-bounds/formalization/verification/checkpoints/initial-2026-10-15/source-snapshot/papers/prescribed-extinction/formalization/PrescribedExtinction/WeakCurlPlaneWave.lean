import PrescribedExtinction.WeakCurlProducts
import PrescribedExtinction.FarFieldCurrent
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory Filter
open scoped Topology

theorem currentPlanePhase_contDiff (k : ℝ) (n : Position) :
    ContDiff ℝ (⊤ : ℕ∞) (currentPlanePhase k n) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position => Complex.ofReal (inner ℝ n x)) :=
    (Complex.ofRealCLM.comp (innerSL ℝ n)).contDiff
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position =>
      Complex.exp ((-Complex.I * (k : ℂ)) * Complex.ofReal (inner ℝ n x))) :=
    (contDiff_const.mul h).cexp
  convert he using 1
  funext x
  simp [currentPlanePhase, realDot_eq_inner, mul_assoc]

theorem currentPlanePhase_hasFDerivAt (k : ℝ) (n x : Position) :
    HasFDerivAt (currentPlanePhase k n)
      ((-Complex.I * (k : ℂ) * currentPlanePhase k n x) •
        (Complex.ofRealCLM.comp (innerSL ℝ n))) x := by
  have h := (Complex.ofRealCLM.comp (innerSL ℝ n)).hasFDerivAt (x := x)
  have he := (h.const_mul (-Complex.I * (k : ℂ))).cexp
  convert he using 1
  · funext y
    simp [currentPlanePhase, realDot_eq_inner, mul_assoc]
  · ext y
    simp [currentPlanePhase, realDot_eq_inner, mul_assoc]
    ring

theorem planeWaveVector_curl (k : ℝ) (n : Position) (v : Vector) (x : Position) :
    curl (fun y => currentPlanePhase k n y • v) x =
      (-Complex.I * (k : ℂ) * currentPlanePhase k n x) • cross (complexify n) v := by
  have hd := ((currentPlanePhase_hasFDerivAt k n x).smul_const v).fderiv
  ext i
  fin_cases i <;> simp [curl, hd, ContinuousLinearMap.smulRight_apply, basisR, complexify,
    cross, PiLp.smul_apply, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_succ] <;> ring

theorem bump_scalarGradient_zero (η : ContDiffBump (0 : Position)) (x : Position)
    (hx : ‖x‖ < η.rIn) : scalarGradient η x = 0 := by
  have he : (η : Position → ℝ) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
    exact η.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hy.le)
  have hd : fderiv ℝ (η : Position → ℝ) x = fderiv ℝ (fun _ : Position => (1 : ℝ)) x := he.fderiv_eq
  ext j
  simp [scalarGradient, hd]

/-- Evaluation of a compactly supported weak curl on a genuine compact
plane-wave test. Both fields may be nonsmooth. -/
theorem weakCurl_compact_planeWave_pairing (F G : Field) (hcurl : HasWeakCurl F G)
    (R : ℝ) (hR : 0 ≤ R)
    (hF : ∀ x, R < ‖x‖ → F x = 0) (hG : ∀ x, R < ‖x‖ → G x = 0)
    (k : ℝ) (n : Position) (v : Vector) :
    (∫ x : Position, bilinear (F x)
      ((-Complex.I * (k : ℂ) * currentPlanePhase k n x) • cross (complexify n) v)) =
      ∫ x : Position, bilinear (G x) (currentPlanePhase k n x • v) := by
  let η : ContDiffBump (0 : Position) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ : Field := fun x => currentPlanePhase k n x • v
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := (currentPlanePhase_contDiff k n).smul contDiff_const
  have htest : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x • φ x) := η.contDiff.smul hφ
  have hsupport : HasCompactSupport (fun x => η x • φ x) := η.hasCompactSupport.smul_right (f' := φ)
  have he := hcurl (fun x => η x • φ x) htest hsupport
  have hcz (w : Vector) : cross (complexify (0 : Position)) w = 0 := by
    ext i
    fin_cases i <;> simp [cross, complexify]
  have hleft : (fun x : Position => bilinear (F x) (curl (fun y => η y • φ y) x)) =
      (fun x => bilinear (F x) ((-Complex.I * (k : ℂ) * currentPlanePhase k n x) • cross (complexify n) v)) := by
    funext x
    by_cases hx : ‖x‖ ≤ R
    · rw [curl_real_smul η φ η.contDiff hφ,
        bump_scalarGradient_zero η x (by dsimp [η]; linarith),
        η.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ R + 1 by linarith))]
      rw [hcz, one_smul, zero_add]
      change bilinear (F x) (curl (fun y => currentPlanePhase k n y • v) x) = _
      rw [planeWaveVector_curl]
    · simp [hF x (lt_of_not_ge hx), bilinear]
  have hright : (fun x : Position => bilinear (G x) (η x • φ x)) =
      (fun x => bilinear (G x) (currentPlanePhase k n x • v)) := by
    funext x
    by_cases hx : ‖x‖ ≤ R
    · rw [η.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ R + 1 by linarith)), one_smul]
    · simp [hG x (lt_of_not_ge hx), bilinear]
  rw [hleft, hright] at he
  exact he

end OQ7Prescribed
