import OQ7.ResourceAsymptotics
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section

namespace OQ7

open Filter
open scoped Topology

/-- The sharp Section 4 coefficient, before multiplication by the target-envelope factor. -/
def resourceAsymptoticCoefficient (k P Q M : ℝ) : ℝ :=
  Real.pi ^ 2 * (k * M) ^ 4 / (3 * P * Q ^ 2)

theorem resource_scaled_full_floor_eventually_lower {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      resourceAsymptoticCoefficient k P Q M - ε ≤
        (k * L) ^ 2 * ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) := by
  have ht := ResourceFloor.full_floor_limit hk hP hQ hM
  exact (ht.eventually (eventually_gt_nhds
    (sub_lt_self (resourceAsymptoticCoefficient k P Q M) hε))).mono fun L hL => hL.le

/-- Order-theoretic helper: an eventual full-cell floor transfers to any varying sequence.
Its floor hypothesis is discharged by the physical Theorem 4.5 below. -/
theorem resource_sequence_eventual_lower_of_floor {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    (L c : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hfloor : ∀ᶠ j : ℕ in atTop,
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P (L j)) ≤ c j)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      resourceAsymptoticCoefficient k P Q M - ε ≤ (k * L j) ^ 2 * c j := by
  have hb := hL.eventually (resource_scaled_full_floor_eventually_lower hk hP hQ hM hε)
  filter_upwards [hb, hfloor] with j hj hfj
  exact hj.trans (mul_le_mul_of_nonneg_left hfj (sq_nonneg _))

/-- Extended-real liminf records the valid `+∞` case for sequences far above the sharp floor. -/
theorem resource_sequence_liminf_lower_of_floor {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    (L c : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hfloor : ∀ᶠ j : ℕ in atTop,
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P (L j)) ≤ c j) :
    (resourceAsymptoticCoefficient k P Q M : EReal) ≤
      liminf (fun j => ((k * L j) ^ 2 * c j : EReal)) atTop := by
  have ht := (ResourceFloor.full_floor_limit hk hP hQ hM).comp hL
  have hte : Tendsto
      (fun j => (((k * L j) ^ 2 *
        ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P (L j)) : ℝ) : EReal))
      atTop (𝓝 (resourceAsymptoticCoefficient k P Q M : EReal)) :=
    EReal.tendsto_coe.mpr ht
  rw [← hte.liminf_eq]
  apply Filter.liminf_le_liminf
  filter_upwards [hfloor] with j hj
  exact_mod_cast mul_le_mul_of_nonneg_left hj (sq_nonneg (k * L j))
  all_goals isBoundedDefault

/-- A full-cell floor, uniformly valid in the budget, yields a uniform epsilon bound.
This is a pure order lemma; physical floors below supply its hypothesis. -/
theorem resource_uniform_eventual_lower_of_floor {ι : Type*} {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M)
    (admissible : ℝ → ι → Prop) (c : ℝ → ι → ℝ)
    (hfloor : ∀ᶠ L : ℝ in atTop, ∀ s, admissible L s →
      ResourceFloor.beta k P Q M (ResourceFloor.fullCellCount k P L) ≤ c L s)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ s, admissible L s →
      resourceAsymptoticCoefficient k P Q M - ε ≤ (k * L) ^ 2 * c L s := by
  filter_upwards [resource_scaled_full_floor_eventually_lower hk hP hQ hM hε,
    hfloor] with L hL hF
  intro s hs
  exact hL.trans (mul_le_mul_of_nonneg_left (hF s hs) (sq_nonneg _))

theorem resourceAsymptoticCoefficient_pos {k P Q M : ℝ}
    (hk : 0 < k) (hP : 0 < P) (hQ : 0 < Q) (hM : 0 < M) :
    0 < resourceAsymptoticCoefficient k P Q M := by
  unfold resourceAsymptoticCoefficient
  positivity

#print axioms resource_uniform_eventual_lower_of_floor
#print axioms resourceAsymptoticCoefficient_pos
#print axioms resource_scaled_full_floor_eventually_lower
#print axioms resource_sequence_eventual_lower_of_floor
#print axioms resource_sequence_liminf_lower_of_floor

end OQ7

