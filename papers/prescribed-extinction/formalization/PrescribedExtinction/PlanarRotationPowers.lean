import PrescribedExtinction.UniformBodyPowers
import PrescribedExtinction.NormalizedRotationPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set

theorem planarNormalizedAbsorption_continuous (k : ℝ) (hk : 0 < k) (σ : Direction)
    (L : ℝ) (hL : 0 ≤ L) (h : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ => planarNormalizedAbsorption k hk σ L hL h θ α β hα hβ) := by
  have hr := planarNormalizedResponse_continuous k hk σ L hL h α β hα hβ
  exact continuous_const.mul ((Complex.continuous_im.comp
    (hr.inner ((planarInverseMaterial L h α β).continuous.comp hr))).neg)

theorem planarNormalizedAbsorption_le_extinction (k : ℝ) (hk : 0 < k) (σ : Direction)
    (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    planarNormalizedAbsorption k hk σ L hL h θ α β hα hβ ≤
      planarNormalizedExtinction k hk σ L hL h θ α β hα hβ := by
  rw [planarNormalizedExtinction_work_balance]
  exact le_add_of_nonneg_right (mul_nonneg hk.le (planarActiveOutgoing_im_nonneg k hk L hL h θ _))

theorem planarNormalizedExtinction_reciprocity (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    planarNormalizedExtinction k hk .plus (h + d) (by linarith) h θ α β hα hβ =
      planarNormalizedExtinction k hk .minus (h + d) (by linarith) h θ α β hα hβ := by
  let X := planarNormalizedExtinction k hk .plus (h + d) (by linarith) h θ α β hα hβ
  let Y := planarNormalizedExtinction k hk .minus (h + d) (by linarith) h θ α β hα hβ
  by_contra hne
  have hδ : 0 < |X - Y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨R, hR, he⟩ := physicalBody_normalized_powers_uniform_aperture_localization k hk h d hh hd
    α β hα hβ (|X - Y| / 4) (by positivity)
  let B : TwoLayerBody := ⟨R, h, d, 1, 1, by linarith, hh, hd⟩
  have hp := he B rfl rfl le_rfl .plus θ
  have hm := he B rfl rfl le_rfl .minus θ
  have hc := normalizedExtinction_reciprocity k hk B θ α β hα hβ
  have hx : |normalizedExtinction k hk B .plus θ α β hα hβ - R ^ 2 * X| ≤ |X - Y| / 4 * R ^ 2 := by
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans hp
  have hy : |normalizedExtinction k hk B .plus θ α β hα hβ - R ^ 2 * Y| ≤ |X - Y| / 4 * R ^ 2 := by
    rw [hc]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans hm
  have htri := abs_sub_le (R ^ 2 * X) (normalizedExtinction k hk B .plus θ α β hα hβ) (R ^ 2 * Y)
  rw [abs_sub_comm (R ^ 2 * X) (normalizedExtinction k hk B .plus θ α β hα hβ),
    ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg R)] at htri
  have hsum : R ^ 2 * |X - Y| ≤ R ^ 2 * (|X - Y| / 2) := by linarith
  have hrr : 0 < R ^ 2 := sq_pos_of_pos (by linarith)
  have hh := le_of_mul_le_mul_left hsum hrr
  linarith

def planarNormalizedAsymmetry (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  |planarNormalizedAbsorption k hk .plus L hL h θ α β hα hβ -
    planarNormalizedAbsorption k hk .minus L hL h θ α β hα hβ| /
    planarNormalizedExtinction k hk .plus L hL h θ α β hα hβ

theorem planarNormalizedAsymmetry_continuous (k : ℝ) (hk : 0 < k) (L : ℝ) (hL : 0 ≤ L)
    (h : ℝ) (hh : 0 ≤ h) (hplate : h < L) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ => planarNormalizedAsymmetry k hk L hL h θ α β hα hβ) :=
  ((planarNormalizedAbsorption_continuous k hk .plus L hL h α β hα hβ).sub
    (planarNormalizedAbsorption_continuous k hk .minus L hL h α β hα hβ)).abs.div
    (planarNormalizedExtinction_continuous k hk .plus L hL h α β hα hβ)
    (fun θ => ne_of_gt (planarNormalizedExtinction_pos k hk .plus L hL h θ hh hplate α β hα hβ))

theorem planarNormalizedAsymmetry_lt_one (k : ℝ) (hk : 0 < k)
    (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    planarNormalizedAsymmetry k hk (h + d) (by linarith) h θ α β hα hβ < 1 := by
  apply (div_lt_one (planarNormalizedExtinction_pos k hk .plus (h + d) (by linarith) h θ hh.le
    (by linarith) α β hα hβ)).mpr
  have hp := planarNormalizedAbsorption_pos k hk .plus (h + d) (by linarith) h θ hh.le (by linarith) α β hα hβ
  have hm := planarNormalizedAbsorption_pos k hk .minus (h + d) (by linarith) h θ hh.le (by linarith) α β hα hβ
  have hpl := planarNormalizedAbsorption_le_extinction k hk .plus (h + d) (by linarith) h θ α β hα hβ
  have hml := planarNormalizedAbsorption_le_extinction k hk .minus (h + d) (by linarith) h θ α β hα hβ
  have he := planarNormalizedExtinction_reciprocity k hk h d hh hd θ α β hα hβ
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end OQ7Prescribed
