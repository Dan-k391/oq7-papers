import Mathlib.Tactic

/-! Algebraic consequences of explicitly supplied power inequalities.
These lemmas are ingredients, not substitutes for the Maxwell estimates. -/
namespace FixedResource

theorem interval_width {x y l u : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hy : l ≤ y ∧ y ≤ u) : |x - y| ≤ u - l := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem efficiency_fraction {A S X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b)
    (hbal : X = A + S) (hS : S ≤ b * A) : S / X ≤ b / (1 + b) := by
  apply (div_le_div_iff₀ hX (by positivity : 0 < 1 + b)).mpr
  nlinarith

theorem efficiency_pair {Ap Am Sp Sm X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b)
    (hp : X = Ap + Sp) (hm : X = Am + Sm)
    (hSp : 0 ≤ Sp) (hSm : 0 ≤ Sm) (hep : Sp ≤ b * Ap) (hem : Sm ≤ b * Am) :
    |Ap - Am| / X ≤ b / (1 + b) := by
  have hp' := efficiency_fraction hX hb hp hep
  have hm' := efficiency_fraction hX hb hm hem
  have hi := interval_width ⟨div_nonneg hSp hX.le, hp'⟩ ⟨div_nonneg hSm hX.le, hm'⟩
  rw [← sub_div, abs_div, abs_of_pos hX, sub_zero] at hi
  have he : Ap - Am = -(Sp - Sm) := by linarith
  simpa only [he, abs_neg] using hi

theorem response_extinction_cap {A S X K : ℝ} (hX : 0 < X) (hK : 0 < K)
    (hS : 0 ≤ S) (hbal : X = A + S) (hwork : X ^ 2 ≤ K * A) :
    X ≤ K ∧ S / X ≤ 1 - X / K := by
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (show A ≤ X by linarith) hK.le]
  · apply (div_le_iff₀ hX).mpr
    have hd : X ^ 2 / K ≤ A := (div_le_iff₀ hK).mpr (by nlinarith)
    have he : (1 - X / K) * X = X - X ^ 2 / K := by ring
    rw [he]
    linarith

theorem necessary_efficiency_cost {b g ε : ℝ} (hε : 0 < ε)
    (hb : 0 ≤ b) (hl : 1 - ε ≤ g) (hu : g ≤ b / (1 + b)) :
    (1 - ε) / ε ≤ b := by
  apply (div_le_iff₀ hε).mpr
  have h := (le_div_iff₀ (by positivity : 0 < 1 + b)).mp (hl.trans hu)
  nlinarith

theorem response_pair {Ap Am Sp Sm X b K : ℝ} (hX : 0 < X) (hb : 0 ≤ b) (hK : 0 < K)
    (hp : X = Ap + Sp) (hm : X = Am + Sm)
    (hSp : 0 ≤ Sp) (hSm : 0 ≤ Sm) (hep : Sp ≤ b * Ap) (hem : Sm ≤ b * Am)
    (hwp : X ^ 2 ≤ K * Ap) (hwm : X ^ 2 ≤ K * Am) :
    X ≤ K ∧ |Ap - Am| / X ≤ min (b / (1 + b)) (1 - X / K) := by
  have hpc := response_extinction_cap hX hK hSp hp hwp
  have hmc := response_extinction_cap hX hK hSm hm hwm
  refine ⟨hpc.1, le_min (efficiency_pair hX hb hp hm hSp hSm hep hem) ?_⟩
  have hi := interval_width ⟨div_nonneg hSp hX.le, hpc.2⟩ ⟨div_nonneg hSm hX.le, hmc.2⟩
  rw [← sub_div, abs_div, abs_of_pos hX, sub_zero] at hi
  have he : Ap - Am = -(Sp - Sm) := by linarith
  simpa only [he, abs_neg] using hi

theorem positive_extinction_cost {k M E X g ε : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hε : 0 < ε) (hfloor : E ≤ X) (hl : 1 - ε ≤ g) (hu : g ≤ 1 - X / (k * M)) :
    E / (k * ε) ≤ M := by
  have h := (div_le_iff₀ (mul_pos hk hM)).mp (show X / (k * M) ≤ ε by linarith)
  apply (div_le_iff₀ (mul_pos hk hε)).mpr
  nlinarith

theorem absolute_difference_quarter {x g : ℝ} (hx : 0 ≤ x)
    (hg : g ≤ 1 - x) : x * g ≤ 1 / 4 := by
  have h := mul_le_mul_of_nonneg_left hg hx
  nlinarith [sq_nonneg (x - 1 / 2)]

theorem absolute_difference_small {x g b : ℝ} (hx : 0 ≤ x)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (he : g ≤ b / (1 + b))
    (hw : g ≤ 1 - x) : x * g ≤ b / (1 + b) ^ 2 := by
  have hd : 0 < 1 + b := by positivity
  by_cases h : x ≤ 1 / (1 + b)
  · calc
      x * g ≤ x * (b / (1 + b)) := mul_le_mul_of_nonneg_left he hx
      _ ≤ (1 / (1 + b)) * (b / (1 + b)) := by gcongr
      _ = _ := by field_simp
  · have hxl : 1 / (1 + b) ≤ x := le_of_lt (lt_of_not_ge h)
    have hhalf : (1 / 2 : ℝ) ≤ 1 / (1 + b) := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hnon : 0 ≤ (x - 1 / (1 + b)) * (x + 1 / (1 + b) - 1) := by
      apply mul_nonneg (sub_nonneg.mpr hxl)
      linarith
    calc
      x * g ≤ x * (1 - x) := mul_le_mul_of_nonneg_left hw hx
      _ ≤ (1 / (1 + b)) * (1 - 1 / (1 + b)) := by nlinarith
      _ = _ := by field_simp; ring

end FixedResource
