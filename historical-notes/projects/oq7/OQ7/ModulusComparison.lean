import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.Compact

namespace OQ7.ModulusComparison
noncomputable section
open Set Filter
open scoped Topology

/-- Finite interfaces cannot produce a jump in a continuous primitive. -/
theorem le_of_hasDerivAt_nonneg_off_finset {a b : ℝ} (bad : Finset ℝ)
    {F F' : ℝ → ℝ} (hab : a ≤ b) (hcont : ContinuousOn F (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, x ∉ bad → HasDerivAt F (F' x) x ∧ 0 ≤ F' x) :
    F a ≤ F b := by
  classical
  induction bad using Finset.induction_on generalizing a b with
  | empty =>
      have hm : MonotoneOn F (Icc a b) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x hx (by simp)).1.differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hderiv x hx (by simp)).1.deriv]
          exact (hderiv x hx (by simp)).2
      exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  | @insert c bad hc ih =>
      have hsub (x y : ℝ) (hx : a ≤ x) (hy : y ≤ b) (hxy : x ≤ y)
          (hnotc : ∀ z ∈ Ioo x y, z ≠ c) : F x ≤ F y := by
        apply ih hxy (hcont.mono (Icc_subset_Icc hx hy))
        intro z hz hzb
        apply hderiv z ⟨hx.trans_lt hz.1, hz.2.trans_le hy⟩
        simp only [Finset.mem_insert, not_or]
        exact ⟨hnotc z hz, hzb⟩
      by_cases hca : c ≤ a
      · exact hsub a b le_rfl le_rfl hab (fun z hz => (hca.trans_lt hz.1).ne')
      · by_cases hbc : b ≤ c
        · exact hsub a b le_rfl le_rfl hab (fun z hz => (hz.2.trans_le hbc).ne)
        · have hac : a < c := lt_of_not_ge hca
          have hcb : c < b := lt_of_not_ge hbc
          exact (hsub a c le_rfl hcb.le hac.le (fun z hz => hz.2.ne)).trans
            (hsub c b hac.le le_rfl hcb.le (fun z hz => hz.1.ne'))

theorem monotoneOn_of_hasDerivAt_nonneg_off_finset {a b : ℝ} (bad : Finset ℝ)
    {F F' : ℝ → ℝ} (hcont : ContinuousOn F (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, x ∉ bad → HasDerivAt F (F' x) x ∧ 0 ≤ F' x) :
    MonotoneOn F (Icc a b) := by
  intro x hx y hy hxy
  apply le_of_hasDerivAt_nonneg_off_finset bad hxy
    (hcont.mono (Icc_subset_Icc hx.1 hy.2))
  intro z hz hzb
  exact hderiv z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩ hzb

def rho (s : ℝ → ℂ) (x : ℝ) : ℝ := Real.sqrt (Complex.normSq (s x))
def radialNumerator (s ds : ℝ → ℂ) (x : ℝ) : ℝ := (star (s x) * ds x).re
def angularNumerator (s ds : ℝ → ℂ) (x : ℝ) : ℝ := (star (s x) * ds x).im
def rhoSlope (s ds : ℝ → ℂ) (x : ℝ) : ℝ := radialNumerator s ds x / rho s x

theorem rho_eq_norm (s : ℝ → ℂ) (x : ℝ) : rho s x = ‖s x‖ := by
  rfl

theorem rho_nonneg (s : ℝ → ℂ) (x : ℝ) : 0 ≤ rho s x := Real.sqrt_nonneg _
theorem rho_pos {s : ℝ → ℂ} {x : ℝ} (hs : s x ≠ 0) : 0 < rho s x := by
  rw [rho_eq_norm]
  exact norm_pos_iff.mpr hs

theorem rho_sq (s : ℝ → ℂ) (x : ℝ) : rho s x ^ 2 = Complex.normSq (s x) :=
  Real.sq_sqrt (Complex.normSq_nonneg _)

theorem normSq_derivative_algebra (s ds : ℂ) :
    (star ds * s + star s * ds).re = 2 * (star s * ds).re := by
  simp [Complex.mul_re]
  ring

theorem normSq_hasDerivAt {s ds : ℝ → ℂ} {x : ℝ} (hs : HasDerivAt s (ds x) x) :
    HasDerivAt (fun y => Complex.normSq (s y)) (2 * radialNumerator s ds x) x := by
  have hp := hs.star.mul hs
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hp
  convert hr using 1
  · funext y
    simp [Complex.normSq_apply, Complex.mul_re]
  · exact (normSq_derivative_algebra (s x) (ds x)).symm

theorem rho_hasDerivAt {s ds : ℝ → ℂ} {x : ℝ} (hs : HasDerivAt s (ds x) x)
    (hz : s x ≠ 0) : HasDerivAt (rho s) (rhoSlope s ds x) x := by
  convert (normSq_hasDerivAt hs).sqrt (Complex.normSq_pos.mpr hz).ne' using 1
  · rfl
  · dsimp [rhoSlope, rho]
    ring

theorem radial_helmholtz_algebra (k p q : ℝ) (s ds : ℂ) :
    (star ds * ds + star s * (-(k : ℂ) ^ 2 *
      ((p : ℂ) + Complex.I * (q : ℂ)) * s)).re =
      Complex.normSq ds - k ^ 2 * p * Complex.normSq s := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, ← Complex.ofReal_pow]
  ring

theorem radialNumerator_hasDerivAt {s ds : ℝ → ℂ} {x k p q : ℝ}
    (hs : HasDerivAt s (ds x) x)
    (hds : HasDerivAt ds (-(k : ℂ) ^ 2 *
      ((p : ℂ) + Complex.I * (q : ℂ)) * s x) x) :
    HasDerivAt (radialNumerator s ds)
      (Complex.normSq (ds x) - k ^ 2 * p * Complex.normSq (s x)) x := by
  have hp := hs.star.mul hds
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hp
  convert hr using 1
  · rfl
  · exact (radial_helmholtz_algebra k p q (s x) (ds x)).symm

theorem radial_angular_identity (s ds : ℂ) :
    (star s * ds).re ^ 2 + (star s * ds).im ^ 2 =
      Complex.normSq s * Complex.normSq ds := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem rhoSlope_hasDerivAt {s ds : ℝ → ℂ} {x k p q : ℝ}
    (hs : HasDerivAt s (ds x) x)
    (hds : HasDerivAt ds (-(k : ℂ) ^ 2 *
      ((p : ℂ) + Complex.I * (q : ℂ)) * s x) x)
    (hz : s x ≠ 0) :
    HasDerivAt (rhoSlope s ds)
      (-k ^ 2 * p * rho s x + angularNumerator s ds x ^ 2 / rho s x ^ 3) x := by
  have hρ : rho s x ≠ 0 := (rho_pos hz).ne'
  convert (radialNumerator_hasDerivAt hs hds).div (rho_hasDerivAt hs hz) hρ using 1
  · rfl
  · dsimp [rhoSlope, angularNumerator]
    have hid := radial_angular_identity (s x) (ds x)
    have hsquare := rho_sq s x
    dsimp [radialNumerator]
    field_simp
    rw [← hsquare] at hid ⊢
    simpa only [starRingEnd_apply] using (by
      linear_combination hid
      : -(k ^ 2 * p * rho s x ^ 4) + (star (s x) * ds x).im ^ 2 =
          rho s x ^ 2 * (Complex.normSq (ds x) - k ^ 2 * p * rho s x ^ 2) -
            (star (s x) * ds x).re ^ 2)

/-- The nonnegative forcing term underlying the shifted variation-of-constants argument. -/
theorem modulus_forcing_nonneg {s ds : ℝ → ℂ} {x k p K : ℝ}
    (_hz : s x ≠ 0) (hcap : k ^ 2 * p ≤ K ^ 2) :
    0 ≤ (-k ^ 2 * p * rho s x + angularNumerator s ds x ^ 2 / rho s x ^ 3) +
      K ^ 2 * rho s x := by
  have hρ := rho_nonneg s x
  have hj : 0 ≤ angularNumerator s ds x ^ 2 / rho s x ^ 3 := by positivity
  have hc := mul_nonneg (sub_nonneg.mpr hcap) hρ
  nlinarith

def comparisonWronskian (K : ℝ) (ρ σ : ℝ → ℝ) (x : ℝ) : ℝ :=
  σ x * Real.sin (K * x) - K * ρ x * Real.cos (K * x)

theorem comparisonWronskian_hasDerivAt {K x R : ℝ} {ρ σ : ℝ → ℝ}
    (hρ : HasDerivAt ρ (σ x) x) (hσ : HasDerivAt σ R x) :
    HasDerivAt (comparisonWronskian K ρ σ)
      ((R + K ^ 2 * ρ x) * Real.sin (K * x)) x := by
  have hs := (Real.hasDerivAt_sin (K * x)).comp x ((hasDerivAt_id x).const_mul K)
  have hc := (Real.hasDerivAt_cos (K * x)).comp x ((hasDerivAt_id x).const_mul K)
  convert (hσ.mul hs).sub ((hρ.const_mul K).mul hc) using 1
  · rfl
  · dsimp
    ring

theorem comparisonWronskian_continuousOn {K : ℝ} {ρ σ : ℝ → ℝ} {J : Set ℝ}
    (hρ : ContinuousOn ρ J) (hσ : ContinuousOn σ J) :
    ContinuousOn (comparisonWronskian K ρ σ) J := by
  exact (hσ.mul (by fun_prop)).sub ((hρ.const_mul K).mul (by fun_prop))

def sineRatio (K : ℝ) (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ρ x / Real.sin (K * x)

theorem sineRatio_hasDerivAt {K x : ℝ} {ρ σ : ℝ → ℝ}
    (hρ : HasDerivAt ρ (σ x) x) (hs : Real.sin (K * x) ≠ 0) :
    HasDerivAt (sineRatio K ρ)
      (comparisonWronskian K ρ σ x / Real.sin (K * x) ^ 2) x := by
  have hsin := (Real.hasDerivAt_sin (K * x)).comp x ((hasDerivAt_id x).const_mul K)
  convert hρ.div hsin hs using 1
  · rfl
  · dsimp [comparisonWronskian]
    ring

/-- Differential Green's identity version of the checkpoint's nonnegative sine-kernel argument.
The finite exception set represents actual layer interfaces; continuity removes all jump terms. -/
theorem comparisonWronskian_nonneg {K H : ℝ} (hK : 0 < K) (hKH : K * H ≤ Real.pi)
    {ρ σ R : ℝ → ℝ} (bad : Finset ℝ)
    (hρcont : ContinuousOn ρ (Ioo 0 H)) (hσcont : ContinuousOn σ (Ioo 0 H))
    (hρderiv : ∀ x ∈ Ioo 0 H, HasDerivAt ρ (σ x) x)
    (hσderiv : ∀ x ∈ Ioo 0 H, x ∉ bad → HasDerivAt σ (R x) x)
    (hforcing : ∀ x ∈ Ioo 0 H, x ∉ bad → 0 ≤ R x + K ^ 2 * ρ x)
    (hρzero : Tendsto ρ (𝓝[>] 0) (𝓝 0))
    (hσzero : Tendsto σ (𝓝[>] 0) (𝓝 1))
    {h : ℝ} (hh : h ∈ Ioo 0 H) : 0 ≤ comparisonWronskian K ρ σ h := by
  have hsin0 : Tendsto (fun x : ℝ => Real.sin (K * x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show Continuous (fun x : ℝ => Real.sin (K * x)) by fun_prop).tendsto
      (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
  have hcos0 : Tendsto (fun x : ℝ => Real.cos (K * x)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (show Continuous (fun x : ℝ => Real.cos (K * x)) by fun_prop).tendsto
      (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
  have hWzero : Tendsto (comparisonWronskian K ρ σ) (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun x : ℝ => σ x * Real.sin (K * x) - K * ρ x * Real.cos (K * x))
      (𝓝[>] 0) (𝓝 0)
    simpa using (hσzero.mul hsin0).sub
      ((hρzero.const_mul K).mul hcos0)
  have hWcont := comparisonWronskian_continuousOn (K := K) hρcont hσcont
  have hWle (δ : ℝ) (hδ : δ ∈ Ioo 0 h) :
      comparisonWronskian K ρ σ δ ≤ comparisonWronskian K ρ σ h := by
    apply le_of_hasDerivAt_nonneg_off_finset bad hδ.2.le
      (hWcont.mono (fun x hx => ⟨hδ.1.trans_le hx.1, hx.2.trans_lt hh.2⟩))
    intro x hx hxb
    have hxH : x ∈ Ioo 0 H := ⟨hδ.1.trans hx.1, hx.2.trans hh.2⟩
    constructor
    · exact comparisonWronskian_hasDerivAt (hρderiv x hxH) (hσderiv x hxH hxb)
    · apply mul_nonneg (hforcing x hxH hxb)
      apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hK.le hxH.1.le)
      exact (mul_le_mul_of_nonneg_left hxH.2.le hK.le).trans hKH
  apply le_of_tendsto hWzero
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hh.1).filter_mono nhdsWithin_le_nhds] with δ hδ hδh
  exact hWle δ ⟨hδ, hδh⟩

/-- The sine comparison on an interval where the modulus has no zero. -/
theorem sine_comparison_of_nonvanishing {K H : ℝ} (hK : 0 < K) (hKH : K * H ≤ Real.pi)
    {ρ σ R : ℝ → ℝ} (bad : Finset ℝ)
    (hρcont : ContinuousOn ρ (Ioo 0 H)) (hσcont : ContinuousOn σ (Ioo 0 H))
    (hρderiv : ∀ x ∈ Ioo 0 H, HasDerivAt ρ (σ x) x)
    (hσderiv : ∀ x ∈ Ioo 0 H, x ∉ bad → HasDerivAt σ (R x) x)
    (hforcing : ∀ x ∈ Ioo 0 H, x ∉ bad → 0 ≤ R x + K ^ 2 * ρ x)
    (hρzero : Tendsto ρ (𝓝[>] 0) (𝓝 0))
    (hσzero : Tendsto σ (𝓝[>] 0) (𝓝 1))
    (hratiozero : Tendsto (sineRatio K ρ) (𝓝[>] 0) (𝓝 (1 / K)))
    {h : ℝ} (hh : h ∈ Ioo 0 H) : Real.sin (K * h) / K ≤ ρ h := by
  have hsin (x : ℝ) (hx : x ∈ Ioo 0 H) : 0 < Real.sin (K * x) := by
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hK hx.1)
    exact (mul_lt_mul_of_pos_left hx.2 hK).trans_le hKH
  have hW (x : ℝ) (hx : x ∈ Ioo 0 H) : 0 ≤ comparisonWronskian K ρ σ x :=
    comparisonWronskian_nonneg hK hKH bad hρcont hσcont hρderiv hσderiv hforcing
      hρzero hσzero hx
  have hQcont : ContinuousOn (sineRatio K ρ) (Ioo 0 H) :=
    hρcont.div (by fun_prop) (fun x hx => (hsin x hx).ne')
  have hQle (δ : ℝ) (hδ : δ ∈ Ioo 0 h) : sineRatio K ρ δ ≤ sineRatio K ρ h := by
    apply le_of_hasDerivAt_nonneg_off_finset (∅ : Finset ℝ) hδ.2.le
      (hQcont.mono (fun x hx => ⟨hδ.1.trans_le hx.1, hx.2.trans_lt hh.2⟩))
    intro x hx _
    have hxH : x ∈ Ioo 0 H := ⟨hδ.1.trans hx.1, hx.2.trans hh.2⟩
    exact ⟨sineRatio_hasDerivAt (hρderiv x hxH) (hsin x hxH).ne',
      div_nonneg (hW x hxH) (sq_nonneg _)⟩
  have hb : 1 / K ≤ sineRatio K ρ h := by
    apply le_of_tendsto hratiozero
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hh.1).filter_mono nhdsWithin_le_nhds] with δ hδ hδh
    exact hQle δ ⟨hδ, hδh⟩
  have hc := (le_div_iff₀ (hsin h hh)).mp hb
  convert hc using 1
  ring

theorem normalized_field_tendsto {s : ℝ → ℂ}
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0) :
    Tendsto (fun x : ℝ => x⁻¹ • s x) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  simpa [hs0] using hs.tendsto_slope_zero.mono_left hsub

theorem rho_div_tendsto {s : ℝ → ℂ}
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0) :
    Tendsto (fun x : ℝ => rho s x / x) (𝓝[>] 0) (𝓝 1) := by
  have hn : Tendsto (fun x : ℝ => ‖x⁻¹ • s x‖) (𝓝[>] 0) (𝓝 1) := by
    simpa using (normalized_field_tendsto hs hs0).norm
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (show 0 < x from hx), rho_eq_norm,
    div_eq_mul_inv]
  ring

theorem sine_div_tendsto (K : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (K * x) / x) (𝓝[>] 0) (𝓝 K) := by
  have hd : HasDerivAt (fun x : ℝ => Real.sin (K * x)) K 0 := by
    convert (Real.hasDerivAt_sin (K * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul K)
      using 1
    · rfl
    · simp
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero.mono_left hsub

theorem sineRatio_tendsto {s : ℝ → ℂ} {K : ℝ} (hK : K ≠ 0)
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0) :
    Tendsto (sineRatio K (rho s)) (𝓝[>] 0) (𝓝 (1 / K)) := by
  have ht := (rho_div_tendsto hs hs0).div (sine_div_tendsto K) hK
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact div_div_div_cancel_right₀ (ne_of_gt hx) _ _

theorem normalized_radial_identity (s ds : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    (star (x⁻¹ • s x) * ds x).re / ‖x⁻¹ • s x‖ = rhoSlope s ds x := by
  have hnum : (star (x⁻¹ • s x) * ds x).re = radialNumerator s ds x / x := by
    simp [radialNumerator, Complex.real_smul, Complex.mul_re, Complex.mul_im, div_eq_mul_inv]
    field_simp [hx.ne']
  have hden : ‖x⁻¹ • s x‖ = rho s x / x := by
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx, rho_eq_norm,
      div_eq_mul_inv]
    ring
  rw [hnum, hden]
  exact div_div_div_cancel_right₀ hx.ne' _ _

theorem rhoSlope_tendsto {s ds : ℝ → ℂ}
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0)
    (hds : ContinuousAt ds 0) (hds0 : ds 0 = 1) :
    Tendsto (rhoSlope s ds) (𝓝[>] 0) (𝓝 1) := by
  have hq := normalized_field_tendsto hs hs0
  have hd : Tendsto ds (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa only [hds0] using hds.tendsto.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun x : ℝ => (star (x⁻¹ • s x) * ds x).re) (𝓝[>] 0) (𝓝 1) := by
    convert (Complex.continuous_re.tendsto (star (1 : ℂ) * 1)).comp (hq.star.mul hd) using 1
    · rfl
    · norm_num
  have hnorm : Tendsto (fun x : ℝ => ‖x⁻¹ • s x‖) (𝓝[>] 0) (𝓝 1) := by
    simpa using hq.norm
  have ht := hn.div hnorm (by norm_num : (1 : ℝ) ≠ 0)
  have ht' : Tendsto (fun x : ℝ =>
      (star (x⁻¹ • s x) * ds x).re / ‖x⁻¹ • s x‖) (𝓝[>] 0) (𝓝 1) := by
    convert ht using 1 <;> first | rfl | norm_num
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact normalized_radial_identity s ds hx

theorem field_eventually_ne_zero {s : ℝ → ℂ}
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0) : ∀ᶠ x : ℝ in 𝓝[>] 0, s x ≠ 0 := by
  have he := (normalized_field_tendsto hs hs0).eventually
    (eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num))
  filter_upwards [he] with x hx
  intro hz
  apply hx
  simp [hz]

/-- Compactness supplies the checkpoint's first zero, separated from the initial zero. -/
theorem exists_first_zero {s : ℝ → ℂ} (hcont : Continuous s)
    (hnear : ∀ᶠ x : ℝ in 𝓝[>] 0, s x ≠ 0)
    {h : ℝ} (hh : 0 < h) (hzero : s h = 0) :
    ∃ H, 0 < H ∧ H ≤ h ∧ s H = 0 ∧ ∀ x ∈ Ioo 0 H, s x ≠ 0 := by
  rcases mem_nhdsGT_iff_exists_Ioc_subset.mp hnear with ⟨ε, hε, hεs⟩
  have hεh : ε < h := by
    by_contra hz
    exact hεs ⟨hh, le_of_not_gt hz⟩ hzero
  have hcompact : IsCompact (Icc ε h ∩ s ⁻¹' {0}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hcont)
  rcases hcompact.exists_isLeast ⟨h, ⟨⟨hεh.le, le_rfl⟩, hzero⟩⟩ with ⟨H, hH⟩
  refine ⟨H, hε.trans_le hH.1.1.1, hH.1.1.2, hH.1.2, ?_⟩
  intro x hx hzx
  by_cases hxε : x ≤ ε
  · exact hεs ⟨hx.1, hxε⟩ hzx
  · have hxset : x ∈ Icc ε h ∩ s ⁻¹' {0} :=
      ⟨⟨(lt_of_not_ge hxε).le, hx.2.le.trans hH.1.1.2⟩, hzx⟩
    exact (not_le_of_gt hx.2) (hH.2 hxset)

theorem rho_continuous {s : ℝ → ℂ} (hs : Continuous s) : Continuous (rho s) := by
  change Continuous (fun x => ‖s x‖)
  exact hs.norm

theorem rhoSlope_continuousOn {s ds : ℝ → ℂ} {J : Set ℝ}
    (hs : Continuous s) (hds : Continuous ds) (hzero : ∀ x ∈ J, s x ≠ 0) :
    ContinuousOn (rhoSlope s ds) J := by
  have hn : Continuous (radialNumerator s ds) :=
    Complex.continuous_re.comp (hs.star.mul hds)
  exact hn.continuousOn.div (rho_continuous hs).continuousOn (fun x hx => (rho_pos (hzero x hx)).ne')

/-- The nonvanishing-interval comparison, derived from the actual complex Helmholtz equations. -/
theorem helmholtz_sine_comparison_on_nonzero {s ds : ℝ → ℂ} {p q : ℝ → ℝ}
    {k K H : ℝ} (hK : 0 < K) (hKH : K * H ≤ Real.pi) (bad : Finset ℝ)
    (hscont : Continuous s) (hdscont : Continuous ds)
    (hsderiv : ∀ x, HasDerivAt s (ds x) x)
    (hdsderiv : ∀ x ∈ Ioo 0 H, x ∉ bad → HasDerivAt ds
      (-(k : ℂ) ^ 2 * ((p x : ℂ) + Complex.I * (q x : ℂ)) * s x) x)
    (hcap : ∀ x ∈ Ioo 0 H, k ^ 2 * p x ≤ K ^ 2)
    (hs0 : s 0 = 0) (hds0 : ds 0 = 1)
    (hnonzero : ∀ x ∈ Ioo 0 H, s x ≠ 0)
    {h : ℝ} (hh : h ∈ Ioo 0 H) : Real.sin (K * h) / K ≤ rho s h := by
  have hinit : HasDerivAt s 1 0 := by simpa only [hds0] using hsderiv 0
  apply sine_comparison_of_nonvanishing hK hKH bad
    (rho_continuous hscont).continuousOn (rhoSlope_continuousOn hscont hdscont hnonzero)
  · intro x hx
    exact rho_hasDerivAt (hsderiv x) (hnonzero x hx)
  · intro x hx hxb
    exact rhoSlope_hasDerivAt (hsderiv x) (hdsderiv x hx hxb) (hnonzero x hx)
  · intro x hx _
    exact modulus_forcing_nonneg (hnonzero x hx) (hcap x hx)
  · simpa [rho, hs0] using (rho_continuous hscont).tendsto 0 |>.mono_left nhdsWithin_le_nhds
  · exact rhoSlope_tendsto hinit hs0 hdscont.continuousAt hds0
  · exact sineRatio_tendsto hK.ne' hinit hs0
  · exact hh

theorem endpoint_le_of_le_Ioo {F G : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hF : ContinuousAt F H) (hG : ContinuousAt G H)
    (hbound : ∀ x ∈ Ioo 0 H, F x ≤ G x) : F H ≤ G H := by
  apply le_of_tendsto_of_tendsto (b := 𝓝[<] H) (hF.tendsto.mono_left nhdsWithin_le_nhds)
    (hG.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hH).filter_mono nhdsWithin_le_nhds] with x hx hxp
  exact hbound x ⟨hxp, hx⟩

/-- First-zero contradiction, with the initial limits proved from differentiability. -/
theorem helmholtz_ne_zero_before {s ds : ℝ → ℂ} {p q : ℝ → ℝ}
    {k K H : ℝ} (hK : 0 < K) (hKH : K * H ≤ Real.pi) (bad : Finset ℝ)
    (hscont : Continuous s) (hdscont : Continuous ds)
    (hsderiv : ∀ x, HasDerivAt s (ds x) x)
    (hdsderiv : ∀ x ∈ Ioo 0 H, x ∉ bad → HasDerivAt ds
      (-(k : ℂ) ^ 2 * ((p x : ℂ) + Complex.I * (q x : ℂ)) * s x) x)
    (hcap : ∀ x ∈ Ioo 0 H, k ^ 2 * p x ≤ K ^ 2)
    (hs0 : s 0 = 0) (hds0 : ds 0 = 1) : ∀ h ∈ Ioo 0 H, s h ≠ 0 := by
  have hinit : HasDerivAt s 1 0 := by simpa only [hds0] using hsderiv 0
  intro h hh hzero
  rcases exists_first_zero hscont (field_eventually_ne_zero hinit hs0) hh.1 hzero
    with ⟨H₀, hH₀, hH₀h, hH₀zero, hH₀nz⟩
  have hH₀H : H₀ < H := hH₀h.trans_lt hh.2
  have hKH₀ : K * H₀ < Real.pi := (mul_lt_mul_of_pos_left hH₀H hK).trans_le hKH
  have hb (x : ℝ) (hx : x ∈ Ioo 0 H₀) : Real.sin (K * x) / K ≤ rho s x := by
    apply helmholtz_sine_comparison_on_nonzero hK hKH₀.le bad hscont hdscont hsderiv
    · intro y hy hyb
      exact hdsderiv y ⟨hy.1, hy.2.trans hH₀H⟩ hyb
    · intro y hy
      exact hcap y ⟨hy.1, hy.2.trans hH₀H⟩
    · exact hs0
    · exact hds0
    · exact hH₀nz
    · exact hx
  have hboundary : Real.sin (K * H₀) / K ≤ rho s H₀ :=
    endpoint_le_of_le_Ioo hH₀ (by fun_prop) (rho_continuous hscont).continuousAt hb
  have hsin : 0 < Real.sin (K * H₀) := Real.sin_pos_of_pos_of_lt_pi (mul_pos hK hH₀) hKH₀
  have hpositive : 0 < Real.sin (K * H₀) / K := div_pos hsin hK
  simp only [rho, hH₀zero, Complex.normSq_zero, Real.sqrt_zero] at hboundary
  exact not_le_of_gt hpositive hboundary

/-- Lemma 4.1 for a finite-interface complex Helmholtz field, with only the local real cap.
Its physical instantiation uses the finite-layer fields, rather than an assumed scattering model. -/
theorem helmholtz_modulus_comparison {s ds : ℝ → ℂ} {p q : ℝ → ℝ}
    {k K H : ℝ} (hK : 0 < K) (hH : 0 < H) (hKH : K * H ≤ Real.pi) (bad : Finset ℝ)
    (hscont : Continuous s) (hdscont : Continuous ds)
    (hsderiv : ∀ x, HasDerivAt s (ds x) x)
    (hdsderiv : ∀ x ∈ Ioo 0 H, x ∉ bad → HasDerivAt ds
      (-(k : ℂ) ^ 2 * ((p x : ℂ) + Complex.I * (q x : ℂ)) * s x) x)
    (hcap : ∀ x ∈ Ioo 0 H, k ^ 2 * p x ≤ K ^ 2)
    (hs0 : s 0 = 0) (hds0 : ds 0 = 1) : Real.sin (K * H) / K ≤ ‖s H‖ := by
  have hnz := helmholtz_ne_zero_before hK hKH bad hscont hdscont hsderiv hdsderiv hcap hs0 hds0
  have hb (x : ℝ) (hx : x ∈ Ioo 0 H) : Real.sin (K * x) / K ≤ rho s x :=
    helmholtz_sine_comparison_on_nonzero hK hKH bad hscont hdscont hsderiv hdsderiv hcap
      hs0 hds0 hnz hx
  rw [← rho_eq_norm]
  exact endpoint_le_of_le_Ioo hH (by fun_prop) (rho_continuous hscont).continuousAt hb

#print axioms le_of_hasDerivAt_nonneg_off_finset
#print axioms monotoneOn_of_hasDerivAt_nonneg_off_finset
#print axioms rho_eq_norm
#print axioms rho_nonneg
#print axioms rho_pos
#print axioms rho_sq
#print axioms normSq_derivative_algebra
#print axioms normSq_hasDerivAt
#print axioms rho_hasDerivAt
#print axioms radial_helmholtz_algebra
#print axioms radialNumerator_hasDerivAt
#print axioms radial_angular_identity
#print axioms rhoSlope_hasDerivAt
#print axioms modulus_forcing_nonneg
#print axioms comparisonWronskian_hasDerivAt
#print axioms comparisonWronskian_continuousOn
#print axioms sineRatio_hasDerivAt
#print axioms comparisonWronskian_nonneg
#print axioms sine_comparison_of_nonvanishing
#print axioms normalized_field_tendsto
#print axioms rho_div_tendsto
#print axioms sine_div_tendsto
#print axioms sineRatio_tendsto
#print axioms normalized_radial_identity
#print axioms rhoSlope_tendsto
#print axioms field_eventually_ne_zero
#print axioms exists_first_zero
#print axioms rho_continuous
#print axioms rhoSlope_continuousOn
#print axioms helmholtz_sine_comparison_on_nonzero
#print axioms endpoint_le_of_le_Ioo
#print axioms helmholtz_ne_zero_before
#print axioms helmholtz_modulus_comparison

end
end OQ7.ModulusComparison
