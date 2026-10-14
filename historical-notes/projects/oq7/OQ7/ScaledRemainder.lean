import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace OQ7
open Filter Asymptotics
open scoped Topology

theorem tendsto_scaled_quartic_remainder {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {F : ℕ → A} {F0 J : A} {C : ℝ}
    (h : ∀ᶠ m : ℕ in atTop,
      ‖F m - F0 - (1 / (m : ℝ) ^ 2) • J‖ ≤ C / (m : ℝ) ^ 4) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 • (F m - F0)) atTop (𝓝 J) := by
  have hrec : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun m : ℕ => C * (1 / (m : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul (hrec.pow 2)
  have hb : ∀ᶠ m : ℕ in atTop,
      ‖(m : ℝ) ^ 2 • (F m - F0) - J‖ ≤ C * (1 / (m : ℝ)) ^ 2 := by
    filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with m hm hmp
    have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hmp.ne'
    have he : (m : ℝ) ^ 2 • (F m - F0) - J =
        (m : ℝ) ^ 2 • (F m - F0 - (1 / (m : ℝ) ^ 2) • J) := by
      simp [smul_sub, smul_smul, hmr]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      (m : ℝ) ^ 2 * ‖F m - F0 - (1 / (m : ℝ) ^ 2) • J‖ ≤
          (m : ℝ) ^ 2 * (C / (m : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = C * (1 / (m : ℝ)) ^ 2 := by field_simp
  have hz := squeeze_zero' (Eventually.of_forall fun m : ℕ => norm_nonneg
    ((m : ℝ) ^ 2 • (F m - F0) - J)) hb hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hz

theorem tendsto_of_scaled_square_difference {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {F : ℕ → A} {F0 J : A}
    (h : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 • (F m - F0)) atTop (𝓝 J)) :
    Tendsto F atTop (𝓝 F0) := by
  have hrec : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun m : ℕ => (1 / (m : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using hrec.pow 2
  have hz := hi.smul h
  have hd : (fun m : ℕ => (1 / (m : ℝ)) ^ 2 • ((m : ℝ) ^ 2 • (F m - F0)))
      =ᶠ[atTop] (fun m : ℕ => F m - F0) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [smul_smul, hmr]
  have hh : Tendsto (fun m : ℕ => F m - F0) atTop (𝓝 0) := by
    simpa only [zero_smul] using hz.congr' hd
  have ha := hh.add_const F0
  simpa using ha

/-- Convergence of the scaled correction gives the norm-dependent O(m⁻²) estimate
in any compatible real normed-space instance. -/
theorem isBigO_of_scaled_square_difference {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {F : ℕ → A} {F0 J : A}
    (h : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 • (F m - F0)) atTop (𝓝 J)) :
    (fun m : ℕ => F m - F0) =O[atTop] (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
  have hb : (fun m : ℕ => (m : ℝ) ^ 2 • (F m - F0))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := isBigO_const_of_tendsto h one_ne_zero
  have hs := (isBigO_refl (fun m : ℕ => 1 / (m : ℝ) ^ 2) atTop).smul hb
  have he : (fun m : ℕ => (1 / (m : ℝ) ^ 2) • ((m : ℝ) ^ 2 • (F m - F0)))
      =ᶠ[atTop] (fun m : ℕ => F m - F0) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [smul_smul, hmr]
  simpa only [smul_eq_mul, mul_one] using hs.congr' he (Eventually.of_forall fun _ => rfl)

#print axioms tendsto_scaled_quartic_remainder
#print axioms tendsto_of_scaled_square_difference
#print axioms isBigO_of_scaled_square_difference
end OQ7
