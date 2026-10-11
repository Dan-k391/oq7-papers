import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OQ7.ResourceScalar
noncomputable section
open Set
open scoped Topology

/-- The scalar cell function in (22) of the supplied paper. -/
def f (u : ℝ) : ℝ := u ^ 2 - Real.sin u ^ 2

/-- Its square root, used when combining cell determinants. -/
def g (u : ℝ) : ℝ := Real.sqrt (f u)

def numerator (u : ℝ) : ℝ := u - Real.sin u * Real.cos u
def slope (u : ℝ) : ℝ := numerator u / g u
def H (u : ℝ) : ℝ := 2 * Real.sin u ^ 2 * f u - numerator u ^ 2

theorem f_nonneg (u : ℝ) : 0 ≤ f u := by
  exact sub_nonneg.mpr Real.sin_sq_le_sq

theorem f_pos {u : ℝ} (hu : u ≠ 0) : 0 < f u := by
  exact sub_pos.mpr (Real.sin_sq_lt_sq hu)

theorem g_nonneg (u : ℝ) : 0 ≤ g u := Real.sqrt_nonneg _

theorem g_pos {u : ℝ} (hu : u ≠ 0) : 0 < g u := by
  exact Real.sqrt_pos.mpr (f_pos hu)

theorem g_sq (u : ℝ) : g u ^ 2 = f u := Real.sq_sqrt (f_nonneg u)

theorem f_hasDerivAt (u : ℝ) : HasDerivAt f (2 * numerator u) u := by
  convert ((hasDerivAt_id u).pow 2).sub ((Real.hasDerivAt_sin u).pow 2) using 1
  · rfl
  · dsimp [numerator]
    ring

theorem numerator_hasDerivAt (u : ℝ) :
    HasDerivAt numerator (2 * Real.sin u ^ 2) u := by
  convert (hasDerivAt_id u).sub ((Real.hasDerivAt_sin u).mul (Real.hasDerivAt_cos u))
    using 1
  · rfl
  · nlinarith [Real.sin_sq_add_cos_sq u]

theorem g_hasDerivAt {u : ℝ} (hu : u ≠ 0) : HasDerivAt g (slope u) u := by
  convert (f_hasDerivAt u).sqrt (f_pos hu).ne' using 1
  · rfl
  · dsimp [slope, g]
    ring

theorem f_continuous : Continuous f := by unfold f; fun_prop
theorem g_continuous : Continuous g := f_continuous.sqrt
theorem numerator_continuous : Continuous numerator := by unfold numerator; fun_prop

theorem H_hasDerivAt (u : ℝ) :
    HasDerivAt H (4 * Real.sin u * Real.cos u * f u) u := by
  convert (((Real.hasDerivAt_sin u).pow 2).const_mul 2 |>.mul (f_hasDerivAt u)).sub
    ((numerator_hasDerivAt u).pow 2) using 1
  · rfl
  · dsimp [numerator]
    ring

theorem H_continuous : Continuous H := by
  unfold H
  exact (((Real.continuous_sin.pow 2).const_mul 2).mul f_continuous).sub
    (numerator_continuous.pow 2)

theorem H_nonneg {u : ℝ} (hu : u ∈ Icc 0 (Real.pi / 2)) : 0 ≤ H u := by
  have hmono : MonotoneOn H (Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) H_continuous.continuousOn
      (fun x _ => (H_hasDerivAt x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(H_hasDerivAt x).deriv]
    rw [interior_Icc] at hx
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (by norm_num)
        exact Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2, Real.pi_pos])
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
    · exact f_nonneg x
  have hz : (0 : ℝ) ∈ Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  simpa [H, numerator, f] using hmono hz hu hu.1

theorem slope_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt slope (H u / g u ^ 3) u := by
  have hg : g u ≠ 0 := (g_pos hu).ne'
  convert (numerator_hasDerivAt u).div (g_hasDerivAt hu) hg using 1
  · rfl
  · dsimp [slope, H]
    field_simp
    nlinarith [g_sq u]

/-- Lemma 4.4's convexity interval is exactly the half period. -/
theorem g_convex_half : ConvexOn ℝ (Icc 0 (Real.pi / 2)) g := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) g_continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (g_hasDerivAt hx.1.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ≠ 0 := by rw [interior_Icc] at hx; exact hx.1.ne'
    have heq : deriv g =ᶠ[𝓝 x] slope := by
      filter_upwards [eventually_ne_nhds hx'] with y hy using (g_hasDerivAt hy).deriv
    exact ((slope_hasDerivAt hx').congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ≠ 0 := by rw [interior_Icc] at hx; exact hx.1.ne'
    have heq : deriv g =ᶠ[𝓝 x] slope := by
      filter_upwards [eventually_ne_nhds hx'] with y hy using (g_hasDerivAt hy).deriv
    change 0 ≤ deriv (deriv g) x
    rw [((slope_hasDerivAt hx').congr_of_eventuallyEq heq).deriv]
    exact div_nonneg (H_nonneg (interior_subset hx)) (pow_nonneg (g_nonneg x) _)

/-- A derivative comparison on a compact interval, including both endpoints. -/
theorem nonneg_of_hasDerivAt {F F' : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hzero : F 0 = 0) (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hbound : ∀ x ∈ Icc 0 u, 0 ≤ F' x) : 0 ≤ F u := by
  have hmono : MonotoneOn F (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (show Continuous F from (show Differentiable ℝ F from
        fun x => (hderiv x).differentiableAt).continuous).continuousOn
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hderiv x).deriv]
    exact hbound x (interior_subset hx)
  have hz := hmono (show (0 : ℝ) ∈ Icc 0 u from ⟨le_rfl, hu⟩)
    (show u ∈ Icc 0 u from ⟨hu, le_rfl⟩) hu
  simpa only [hzero] using hz

theorem numerator_upper {u : ℝ} (hu : 0 ≤ u) : numerator u ≤ 2 * u ^ 3 / 3 := by
  have hb : 0 ≤ 2 * u ^ 3 / 3 - numerator u := by
    apply nonneg_of_hasDerivAt (F' := fun x => 2 * x ^ 2 - 2 * Real.sin x ^ 2) hu
    · simp [numerator]
    · intro x
      convert (((hasDerivAt_id x).pow 3).const_mul (2 / 3 : ℝ)).sub
        (numerator_hasDerivAt x) using 1 <;> (try funext y) <;> dsimp <;> ring
    · intro x _
      nlinarith [Real.sin_sq_le_sq (x := x)]
  linarith

theorem f_upper {u : ℝ} (hu : 0 ≤ u) : f u ≤ u ^ 4 / 3 := by
  have hb : 0 ≤ u ^ 4 / 3 - f u := by
    apply nonneg_of_hasDerivAt (F' := fun x => 4 * x ^ 3 / 3 - 2 * numerator x) hu
    · simp [f]
    · intro x
      convert (((hasDerivAt_id x).pow 4).div_const 3).sub (f_hasDerivAt x)
        using 1 <;> (try funext y) <;> dsimp <;> ring
    · intro x hx
      linarith [numerator_upper hx.1]
  linarith

theorem sin_sq_lower_half {u : ℝ} (hu : u ∈ Icc 0 (Real.pi / 2)) :
    4 * u ^ 2 / Real.pi ^ 2 ≤ Real.sin u ^ 2 := by
  have hj := Real.mul_le_sin hu.1 hu.2
  have hs : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu.1 (by linarith [hu.2, Real.pi_pos])
  have hl : 2 * u ≤ Real.pi * Real.sin u := by
    have h := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    convert h using 1
    field_simp
  have hsq := mul_self_le_mul_self (mul_nonneg (by norm_num) hu.1) hl
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith

theorem numerator_lower_half {u : ℝ} (hu : u ∈ Icc 0 (Real.pi / 2)) :
    8 * u ^ 3 / (3 * Real.pi ^ 2) ≤ numerator u := by
  have hb : 0 ≤ numerator u - 8 * u ^ 3 / (3 * Real.pi ^ 2) := by
    apply nonneg_of_hasDerivAt
      (F' := fun x => 2 * Real.sin x ^ 2 - 8 * x ^ 2 / Real.pi ^ 2) hu.1
    · simp [numerator]
    · intro x
      convert (numerator_hasDerivAt x).sub
        (((hasDerivAt_id x).pow 3).const_mul (8 / (3 * Real.pi ^ 2)))
        using 1 <;> (try funext y) <;> dsimp <;> ring
    · intro x hx
      have hl := sin_sq_lower_half ⟨hx.1, hx.2.trans hu.2⟩
      ring_nf at hl ⊢
      linarith
  linarith

/-- The explicit quartic lower estimate used by the finite resource floor. -/
theorem f_lower_half {u : ℝ} (hu : u ∈ Icc 0 (Real.pi / 2)) :
    4 * u ^ 4 / (3 * Real.pi ^ 2) ≤ f u := by
  have hb : 0 ≤ f u - 4 * u ^ 4 / (3 * Real.pi ^ 2) := by
    apply nonneg_of_hasDerivAt
      (F' := fun x => 2 * numerator x - 16 * x ^ 3 / (3 * Real.pi ^ 2)) hu.1
    · simp [f]
    · intro x
      convert (f_hasDerivAt x).sub
        (((hasDerivAt_id x).pow 4).const_mul (4 / (3 * Real.pi ^ 2)))
        using 1 <;> (try funext y) <;> dsimp <;> ring
    · intro x hx
      have hl := numerator_lower_half ⟨hx.1, hx.2.trans hu.2⟩
      ring_nf at hl ⊢
      linarith
  linarith

theorem numerator_lower_small {u : ℝ} (hu : u ∈ Icc 0 1) :
    2 * u ^ 3 / 3 - 2 * u ^ 5 / 15 ≤ numerator u := by
  have hb : 0 ≤ numerator u - (2 * u ^ 3 / 3 - 2 * u ^ 5 / 15) := by
    apply nonneg_of_hasDerivAt
      (F' := fun x => 2 * Real.sin x ^ 2 - (2 * x ^ 2 - 2 * x ^ 4 / 3)) hu.1
    · simp [numerator]
    · intro x
      convert (numerator_hasDerivAt x).sub
        ((((hasDerivAt_id x).pow 3).const_mul (2 / 3 : ℝ)).sub
          (((hasDerivAt_id x).pow 5).const_mul (2 / 15 : ℝ)))
        using 1 <;> (try funext y) <;> dsimp <;> ring
    · intro x hx
      have hs := Real.sin_ge_sub_cube hx.1
      have hx1 : x ≤ 1 := hx.2.trans hu.2
      have hx2 : x ^ 2 ≤ 1 := by simpa [sq] using mul_self_le_mul_self hx.1 hx1
      have hl : 0 ≤ x - x ^ 3 / 6 := by
        have hc := mul_nonneg hx.1 (show 0 ≤ 1 - x ^ 2 / 6 by nlinarith)
        nlinarith
      have hsq := mul_self_le_mul_self hl hs
      nlinarith [sq_nonneg (x ^ 3)]
  linarith

/-- An elementary two-sided remainder, sufficient for the sharp asymptotic floor. -/
theorem f_lower_small {u : ℝ} (hu : u ∈ Icc 0 1) :
    u ^ 4 / 3 - 2 * u ^ 6 / 45 ≤ f u := by
  have hb : 0 ≤ f u - (u ^ 4 / 3 - 2 * u ^ 6 / 45) := by
    apply nonneg_of_hasDerivAt
      (F' := fun x => 2 * numerator x - (4 * x ^ 3 / 3 - 4 * x ^ 5 / 15)) hu.1
    · simp [f]
    · intro x
      convert (f_hasDerivAt x).sub
        ((((hasDerivAt_id x).pow 4).div_const 3).sub
          (((hasDerivAt_id x).pow 6).const_mul (2 / 45 : ℝ)))
        using 1 <;> (try funext y) <;> dsimp <;> ring
    · intro x hx
      linarith [numerator_lower_small ⟨hx.1, hx.2.trans hu.2⟩]
  linarith

theorem g_lower_half {u : ℝ} (hu : u ∈ Icc 0 (Real.pi / 2)) :
    2 * u ^ 2 / (Real.pi * Real.sqrt 3) ≤ g u := by
  apply Real.le_sqrt_of_sq_le
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have heq : (2 * u ^ 2 / (Real.pi * Real.sqrt 3)) ^ 2 =
      4 * u ^ 4 / (3 * Real.pi ^ 2) := by
    simp only [div_pow, mul_pow, hsq3]
    ring
  rw [heq]
  exact f_lower_half hu

theorem slope_upper_half {x : ℝ} (hx : x ∈ Icc 0 (Real.pi / 2)) (hx0 : 0 < x) :
    slope x ≤ Real.pi * x / Real.sqrt 3 := by
  have hs3 : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo := g_lower_half hx
  have hmul := mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ Real.pi * x / Real.sqrt 3 by positivity)
  have heq : Real.pi * x / Real.sqrt 3 *
      (2 * x ^ 2 / (Real.pi * Real.sqrt 3)) = 2 * x ^ 3 / 3 := by
    field_simp
    nlinarith [hs3sq]
  rw [heq] at hmul
  apply (div_le_iff₀ (g_pos hx0.ne')).mpr
  exact (numerator_upper hx.1).trans hmul

theorem g_tangent_half {x v : ℝ} (hx : x ∈ Icc 0 (Real.pi / 2)) (hx0 : x ≠ 0)
    (hv : v ∈ Icc 0 (Real.pi / 2)) :
    g x + slope x * (v - x) ≤ g v := by
  rcases lt_trichotomy x v with h | h | h
  · have hb := g_convex_half.le_slope_of_hasDerivAt hx hv h (g_hasDerivAt hx0)
    rw [slope_def_field] at hb
    have := (le_div_iff₀ (sub_pos.mpr h)).mp hb
    linarith
  · simp [h]
  · have hb := g_convex_half.slope_le_of_hasDerivAt hv hx h (g_hasDerivAt hx0)
    rw [slope_def_field] at hb
    have := (div_le_iff₀ (sub_pos.mpr h)).mp hb
    nlinarith

theorem tangent_intercept_nonpos {x : ℝ} (hx : x ∈ Icc 0 (Real.pi / 2))
    (hx0 : x ≠ 0) : g x - x * slope x ≤ 0 := by
  have hb := g_tangent_half hx hx0 (show (0 : ℝ) ∈ Icc 0 (Real.pi / 2) by
    constructor; exact le_rfl; positivity)
  simpa [g, f, mul_comm, sub_eq_add_neg] using hb

theorem slope_small {x : ℝ} (hx : 0 < x) (hxmax : x ≤ 1 / 3) :
    slope x ≤ Real.pi / (3 * Real.sqrt 3) := by
  have hhalf : x ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  have hb := slope_upper_half ⟨hx.le, hhalf⟩ hx
  apply hb.trans
  rw [← div_div]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < Real.sqrt (3 : ℝ))).mpr
  nlinarith [Real.pi_pos]

/-- The tail of the full period dominates every small-mean tangent slope. -/
theorem g_tail_linear {v : ℝ} (hv : Real.pi / 2 ≤ v) :
    Real.pi / (3 * Real.sqrt 3) * v ≤ g v := by
  have hv0 : 0 ≤ v := le_trans (by positivity) hv
  have hp3 := Real.pi_gt_three
  have hp4 := Real.pi_le_four
  have hp2lo : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  have hp2hi : Real.pi ^ 2 ≤ (16 : ℝ) := by nlinarith [Real.pi_pos]
  have hcoef : Real.pi ^ 2 * (27 - Real.pi ^ 2) ≥ (108 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp2lo) (sub_nonneg.mpr hp2hi)]
  have hv2 : Real.pi ^ 2 / 4 ≤ v ^ 2 := by nlinarith [sq_nonneg (v - Real.pi / 2)]
  have hcoef0 : 0 ≤ 27 - Real.pi ^ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hv2 hcoef0
  have hsin := Real.sin_sq_le_one v
  have hl : Real.pi ^ 2 * v ^ 2 / 27 ≤ f v := by
    dsimp [f]
    nlinarith
  apply Real.le_sqrt_of_sq_le
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have heq : (Real.pi / (3 * Real.sqrt 3) * v) ^ 2 =
      Real.pi ^ 2 * v ^ 2 / 27 := by
    rw [mul_pow, div_pow, mul_pow, hs3sq]
    ring
  rw [heq]
  exact hl

/-- Lemma 4.4's separate global supporting tangent. Convexity is not extended. -/
theorem g_tangent_full {x v : ℝ} (hx : 0 < x) (hxmax : x ≤ 1 / 3)
    (hv : v ∈ Icc 0 Real.pi) : g x + slope x * (v - x) ≤ g v := by
  have hhalf : x ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  by_cases hvt : v ≤ Real.pi / 2
  · exact g_tangent_half ⟨hx.le, hhalf⟩ hx.ne' ⟨hv.1, hvt⟩
  · have hi := tangent_intercept_nonpos ⟨hx.le, hhalf⟩ hx.ne'
    have hs := mul_le_mul_of_nonneg_right (slope_small hx hxmax) hv.1
    have ht := g_tail_linear (le_of_not_ge hvt)
    nlinarith

theorem f_even (u : ℝ) : f (-u) = f u := by simp [f, Real.sin_neg]
theorem f_abs (u : ℝ) : f |u| = f u := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, f_even]

theorem g_zero : g 0 = 0 := by simp [g, f]

theorem g_le_sq (u : ℝ) : g u ≤ u ^ 2 := by
  unfold g
  apply (Real.sqrt_le_left (sq_nonneg u)).mpr
  have hb := f_upper (abs_nonneg u)
  rw [f_abs, pow_abs] at hb
  rw [abs_of_nonneg (show 0 ≤ u ^ 4 by positivity)] at hb
  nlinarith [f_nonneg u]

theorem abs_g_div_le_abs {u : ℝ} (hu : u ≠ 0) : |g u / u| ≤ |u| := by
  rw [abs_div, abs_of_nonneg (g_nonneg u)]
  apply (div_le_iff₀ (abs_pos.mpr hu)).mpr
  simpa only [← sq, sq_abs] using g_le_sq u

/-- The endpoint is differentiable with zero slope, without a formal Taylor series. -/
theorem g_hasDerivAt_zero : HasDerivAt g 0 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ha : Filter.Tendsto (fun u : ℝ => |u|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun u : ℝ => g u / u) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using ha.neg) ha
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact (abs_le.mp (abs_g_div_le_abs (by simpa using hu))).1
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact (abs_le.mp (abs_g_div_le_abs (by simpa using hu))).2
  convert ht using 1
  funext u
  simp only [slope_def_field, g_zero, sub_zero]

theorem f_ratio_lower {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    1 / 3 - 2 * u ^ 2 / 45 ≤ f u / u ^ 4 := by
  apply (le_div_iff₀ (pow_pos hu 4)).mpr
  have hb := f_lower_small ⟨hu.le, hu1⟩
  nlinarith

theorem f_ratio_upper {u : ℝ} (hu : 0 < u) : f u / u ^ 4 ≤ 1 / 3 := by
  apply (div_le_iff₀ (pow_pos hu 4)).mpr
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using f_upper hu.le

/-- The sharp fourth-order coefficient used in the varying-stack lower limit. -/
theorem tendsto_f_ratio_right :
    Filter.Tendsto (fun u : ℝ => f u / u ^ 4) (𝓝[>] 0) (𝓝 (1 / 3)) := by
  have hi : Filter.Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hl : Filter.Tendsto (fun u : ℝ => 1 / 3 - 2 * u ^ 2 / 45)
      (𝓝[>] 0) (𝓝 (1 / 3)) := by
    convert tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hi.pow 2)).div_const 45)
      using 1 <;> norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with u hu hu1
    exact f_ratio_lower hu hu1.le
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact f_ratio_upper hu

/-- Ordinary Jensen is used only for cells whose masses lie in the half interval. -/
theorem sum_g_half {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Icc 0 (Real.pi / 2)) :
    (n : ℝ) * g ((∑ i, u i) / n) ≤ ∑ i, g (u i) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := g_convex_half.map_sum_le (t := Finset.univ)
    (w := fun _ : Fin n => (1 : ℝ) / n) (p := u)
    (fun _ _ => by positivity)
    (by simp [Finset.sum_const, hn0]) (fun i _ => hu i)
  simp only [smul_eq_mul] at hb
  have heq : (∑ i, 1 / (n : ℝ) * u i) = (∑ i, u i) / n := by
    rw [← Finset.mul_sum]
    ring
  rw [heq] at hb
  have hrhs : (∑ i, 1 / (n : ℝ) * g (u i)) = (∑ i, g (u i)) / n := by
    rw [← Finset.mul_sum]
    ring
  rw [hrhs] at hb
  simpa only [mul_comm] using (le_div_iff₀ hnpos).mp hb

/-- Summing the full-period supporting tangent replaces invalid global Jensen. -/
theorem sum_g_full {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Icc 0 Real.pi)
    (hm0 : 0 < (∑ i, u i) / (n : ℝ)) (hm1 : (∑ i, u i) / (n : ℝ) ≤ 1 / 3) :
    (n : ℝ) * g ((∑ i, u i) / n) ≤ ∑ i, g (u i) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => g_tangent_full hm0 hm1 (hu i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib] at hb
  have hz : (∑ i, u i) - (n : ℝ) * ((∑ i, u i) / n) = 0 := by field_simp; ring
  rw [hz, mul_zero, add_zero] at hb
  exact hb

theorem sum_g_small_total {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hU : (∑ i, u i) ≤ Real.pi / 2) :
    (n : ℝ) * g ((∑ i, u i) / n) ≤ ∑ i, g (u i) := by
  apply sum_g_half hn u
  intro i
  exact ⟨hu i, (Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)).trans hU⟩

/-- The two legitimate aggregation cases in Theorem 4.5's full-cell proof. -/
theorem sum_g_full_cases {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Icc 0 Real.pi) (hM : 0 < ∑ i, u i)
    (hcase : (∑ i, u i) ≤ Real.pi / 2 ∨ (∑ i, u i) / (n : ℝ) ≤ 1 / 3) :
    (n : ℝ) * g ((∑ i, u i) / n) ≤ ∑ i, g (u i) := by
  rcases hcase with h | h
  · exact sum_g_small_total hn u (fun i => (hu i).1) h
  · exact sum_g_full hn u hu (div_pos hM (by exact_mod_cast hn)) h

#print axioms f_nonneg
#print axioms f_pos
#print axioms g_nonneg
#print axioms g_pos
#print axioms g_sq
#print axioms f_hasDerivAt
#print axioms numerator_hasDerivAt
#print axioms g_hasDerivAt
#print axioms f_continuous
#print axioms g_continuous
#print axioms numerator_continuous
#print axioms H_hasDerivAt
#print axioms H_continuous
#print axioms H_nonneg
#print axioms slope_hasDerivAt
#print axioms g_convex_half
#print axioms nonneg_of_hasDerivAt
#print axioms numerator_upper
#print axioms f_upper
#print axioms sin_sq_lower_half
#print axioms numerator_lower_half
#print axioms f_lower_half
#print axioms numerator_lower_small
#print axioms f_lower_small
#print axioms g_lower_half
#print axioms slope_upper_half
#print axioms g_tangent_half
#print axioms tangent_intercept_nonpos
#print axioms slope_small
#print axioms g_tail_linear
#print axioms g_tangent_full
#print axioms f_even
#print axioms f_abs
#print axioms g_zero
#print axioms g_le_sq
#print axioms abs_g_div_le_abs
#print axioms g_hasDerivAt_zero
#print axioms f_ratio_lower
#print axioms f_ratio_upper
#print axioms tendsto_f_ratio_right
#print axioms sum_g_half
#print axioms sum_g_full
#print axioms sum_g_small_total
#print axioms sum_g_full_cases

end
end OQ7.ResourceScalar

