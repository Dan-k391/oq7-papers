import OQ7.ResourceScalar
import Mathlib.Analysis.SpecificLimits.Basic

namespace OQ7.ResourceFloor
noncomputable section
open Filter Set
open scoped Topology

/-- Positive natural cell count, with exactly the ceiling convention in Theorem 4.5. -/
def cellCount (a L : ℝ) : ℕ := max 1 ⌈a * L⌉₊

theorem cellCount_pos (a L : ℝ) : 0 < cellCount a L := by
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem cellCount_cast_pos (a L : ℝ) : (0 : ℝ) < cellCount a L := by
  exact_mod_cast cellCount_pos a L

theorem cellCount_eq_ceil {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    cellCount a L = ⌈a * L⌉₊ := by
  exact max_eq_right (Nat.one_le_ceil_iff.mpr (mul_pos ha hL))

theorem cellCount_lower (a L : ℝ) : a * L ≤ (cellCount a L : ℝ) := by
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈a * L⌉₊)

theorem cellCount_upper {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (cellCount a L : ℝ) ≤ 1 + a * L := by
  rw [cellCount_eq_ceil ha hL]
  exact (Nat.ceil_lt_add_one (mul_pos ha hL).le).le.trans_eq (by ring)

theorem cellCount_ratio {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℝ => (cellCount a L : ℝ) / L) atTop (𝓝 a) := by
  apply (tendsto_nat_ceil_mul_div_atTop ha.le).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [cellCount_eq_ceil ha hL]

theorem cellCount_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℝ => (cellCount a L : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono (cellCount_lower a) (Tendsto.const_mul_atTop ha tendsto_id)

theorem inverse_cellCount_ratio {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℝ => L / (cellCount a L : ℝ)) atTop (𝓝 (1 / a)) := by
  simpa only [inv_div, one_div] using (cellCount_ratio ha).inv₀ ha.ne'

def U (k P Q M : ℝ) : ℝ := k * Real.sqrt P * M / Q

def beta (k P Q M : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Q ^ 2 / P ^ 2 * ResourceScalar.f (U k P Q M / (n : ℝ))

def fullCellCount (k P L : ℝ) : ℕ := cellCount (k * Real.sqrt P / Real.pi) L
def halfCellCount (k P L : ℝ) : ℕ := cellCount (2 * k * Real.sqrt P / Real.pi) L

theorem U_pos {k P Q M : ℝ} (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q)
    (hM : 0 < M) : 0 < U k P Q M := by unfold U; positivity

theorem U_div_cellCount_tendsto {a k P Q M : ℝ} (ha : 0 < a)
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    Tendsto (fun L : ℝ => U k P Q M / (cellCount a L : ℝ)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_const_nhds.div_atTop (cellCount_atTop ha)
  · exact Eventually.of_forall (fun L => div_pos (U_pos hk hP hQ hM) (cellCount_cast_pos a L))

theorem full_mean_eventually_small {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    ∀ᶠ L : ℝ in atTop, U k P Q M / (fullCellCount k P L : ℝ) ≤ 1 / 3 := by
  have ha : 0 < k * Real.sqrt P / Real.pi := by positivity
  have ht := U_div_cellCount_tendsto ha hk hP hQ hM
  have htn : Tendsto (fun L : ℝ => U k P Q M / (fullCellCount k P L : ℝ))
      atTop (𝓝 0) := ht.mono_right nhdsWithin_le_nhds
  filter_upwards [htn.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 3 by norm_num))]
    with L hL
  exact hL.le

theorem scaled_beta_identity {k P Q M L : ℝ} {n : ℕ}
    (hn : 0 < n) (hU : U k P Q M ≠ 0) :
    (k * L) ^ 2 * beta k P Q M n =
      (k ^ 2 * Q ^ 2 / P ^ 2 * U k P Q M ^ 4) *
        (L / (n : ℝ)) ^ 2 *
        (ResourceScalar.f (U k P Q M / (n : ℝ)) / (U k P Q M / (n : ℝ)) ^ 4) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold beta
  field_simp

theorem scaled_beta_cellCount_limit {a k P Q M : ℝ} (ha : 0 < a)
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    Tendsto (fun L : ℝ => (k * L) ^ 2 * beta k P Q M (cellCount a L)) atTop
      (𝓝 ((k ^ 2 * Q ^ 2 / P ^ 2 * U k P Q M ^ 4) * (1 / a) ^ 2 * (1 / 3))) := by
  have hratio := ResourceScalar.tendsto_f_ratio_right.comp
    (U_div_cellCount_tendsto ha hk hP hQ hM)
  have hc : Tendsto (fun _ : ℝ => k ^ 2 * Q ^ 2 / P ^ 2 * U k P Q M ^ 4) atTop
      (𝓝 (k ^ 2 * Q ^ 2 / P ^ 2 * U k P Q M ^ 4)) := tendsto_const_nhds
  have ht := (hc.mul ((inverse_cellCount_ratio ha).pow 2)).mul hratio
  apply ht.congr'
  exact Eventually.of_forall (fun L =>
    (scaled_beta_identity (cellCount_pos a L) (U_pos hk hP hQ hM).ne').symm)

theorem full_constant_identity {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) :
    (k ^ 2 * Q ^ 2 / P ^ 2 * U k P Q M ^ 4) *
        (1 / (k * Real.sqrt P / Real.pi)) ^ 2 * (1 / 3) =
      Real.pi ^ 2 * (k * M) ^ 4 / (3 * P * Q ^ 2) := by
  have hs : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP.le
  have hs0 : Real.sqrt P ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  have hs4 : Real.sqrt P ^ 4 = P ^ 2 := by
    calc Real.sqrt P ^ 4 = (Real.sqrt P ^ 2) ^ 2 := by ring
         _ = P ^ 2 := by rw [hs]
  unfold U
  simp only [mul_pow, div_pow, one_div, inv_div, hs, hs4]
  field_simp

/-- The sharp all-budget asymptotic of the scalar full-cell floor. -/
theorem full_floor_limit {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    Tendsto (fun L : ℝ => (k * L) ^ 2 * beta k P Q M (fullCellCount k P L)) atTop
      (𝓝 (Real.pi ^ 2 * (k * M) ^ 4 / (3 * P * Q ^ 2))) := by
  have ha : 0 < k * Real.sqrt P / Real.pi := by positivity
  simpa only [fullCellCount, full_constant_identity hk hP hQ] using
    scaled_beta_cellCount_limit ha hk hP hQ hM

theorem beta_pos {k P Q M : ℝ} {n : ℕ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hn : 0 < n) :
    0 < beta k P Q M n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : 0 < U k P Q M / (n : ℝ) := div_pos (U_pos hk hP hQ hM) hnpos
  unfold beta
  exact mul_pos (by positivity) (ResourceScalar.f_pos harg.ne')

theorem beta_quartic_lower {k P Q M : ℝ} {n : ℕ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hn : 0 < n)
    (hhalf : U k P Q M / (n : ℝ) ≤ Real.pi / 2) :
    4 * k ^ 4 * M ^ 4 / (3 * Real.pi ^ 2 * Q ^ 2 * (n : ℝ) ^ 2) ≤ beta k P Q M n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP.le
  have hs4 : Real.sqrt P ^ 4 = P ^ 2 := by
    calc Real.sqrt P ^ 4 = (Real.sqrt P ^ 2) ^ 2 := by ring
         _ = P ^ 2 := by rw [hs]
  have hb := mul_le_mul_of_nonneg_left
    (ResourceScalar.f_lower_half ⟨(div_pos (U_pos hk hP hQ hM) hnpos).le, hhalf⟩)
    (show 0 ≤ (n : ℝ) ^ 2 * Q ^ 2 / P ^ 2 by positivity)
  have heq : (n : ℝ) ^ 2 * Q ^ 2 / P ^ 2 *
      (4 * (U k P Q M / (n : ℝ)) ^ 4 / (3 * Real.pi ^ 2)) =
        4 * k ^ 4 * M ^ 4 / (3 * Real.pi ^ 2 * Q ^ 2 * (n : ℝ) ^ 2) := by
    unfold U
    simp only [mul_pow, div_pow, hs4]
    field_simp
  rw [heq] at hb
  exact hb

theorem half_mean_le_halfperiod {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (_hM : 0 < M) (hL : 0 < L)
    (hresource : M ≤ Q * L) : U k P Q M / (halfCellCount k P L : ℝ) ≤ Real.pi / 2 := by
  have hnpos : (0 : ℝ) < halfCellCount k P L := cellCount_cast_pos _ _
  have hcl := cellCount_lower (2 * k * Real.sqrt P / Real.pi) L
  have hc : 2 * k * Real.sqrt P * L ≤ Real.pi * (halfCellCount k P L : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left hcl Real.pi_pos.le
    dsimp [halfCellCount]
    convert hb using 1
    field_simp
  have hm := mul_le_mul_of_nonneg_left hresource
    (show 0 ≤ 2 * k * Real.sqrt P by positivity)
  have hcQ := mul_le_mul_of_nonneg_right hc hQ.le
  apply (div_le_iff₀ hnpos).mpr
  unfold U
  apply (div_le_iff₀ hQ).mpr
  nlinarith

/-- The explicit positive finite-budget estimate for the half-cell scalar floor. -/
theorem half_floor_explicit {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hL : 0 < L)
    (hresource : M ≤ Q * L) :
    4 * k ^ 4 * M ^ 4 / (3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2) ≤
      beta k P Q M (halfCellCount k P L) := by
  have ha : 0 < 2 * k * Real.sqrt P / Real.pi := by positivity
  have hnpos : (0 : ℝ) < halfCellCount k P L := cellCount_cast_pos _ _
  have hnupper := cellCount_upper ha hL
  have hc : Real.pi * (halfCellCount k P L : ℝ) ≤
      Real.pi + 2 * k * Real.sqrt P * L := by
    have hb := mul_le_mul_of_nonneg_left hnupper Real.pi_pos.le
    dsimp [halfCellCount]
    convert hb using 1
    field_simp
  have hsq := mul_self_le_mul_self (mul_nonneg Real.pi_pos.le hnpos.le) hc
  have hden : 3 * Real.pi ^ 2 * Q ^ 2 * (halfCellCount k P L : ℝ) ^ 2 ≤
      3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3 * Q ^ 2 by positivity)
    nlinarith
  apply le_trans _ (beta_quartic_lower hk hP hQ hM (cellCount_pos _ _)
    (half_mean_le_halfperiod hk hP hQ hM hL hresource))
  apply div_le_div_of_nonneg_left (by positivity)
    (show 0 < 3 * Real.pi ^ 2 * Q ^ 2 * (halfCellCount k P L : ℝ) ^ 2 by positivity) hden

theorem explicit_floor_pos {k P Q M L : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) (hL : 0 < L) :
    0 < 4 * k ^ 4 * M ^ 4 / (3 * Q ^ 2 * (Real.pi + 2 * k * Real.sqrt P * L) ^ 2) := by
  positivity

#print axioms cellCount_pos
#print axioms cellCount_cast_pos
#print axioms cellCount_eq_ceil
#print axioms cellCount_lower
#print axioms cellCount_upper
#print axioms cellCount_ratio
#print axioms cellCount_atTop
#print axioms inverse_cellCount_ratio
#print axioms U_pos
#print axioms U_div_cellCount_tendsto
#print axioms full_mean_eventually_small
#print axioms scaled_beta_identity
#print axioms scaled_beta_cellCount_limit
#print axioms full_constant_identity
#print axioms full_floor_limit
#print axioms beta_pos
#print axioms beta_quartic_lower
#print axioms half_mean_le_halfperiod
#print axioms half_floor_explicit
#print axioms explicit_floor_pos

end
end OQ7.ResourceFloor


