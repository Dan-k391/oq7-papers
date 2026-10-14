import PrescribedExtinction.PlanarMaterialInverse
import PrescribedExtinction.PlanarDrive

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set

def planarNormalizedResponse (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : PlanarCurrentL2 L :=
  (planarActiveMaterialEquiv k hk L hL h θ α β hα hβ).symm (-planarNormalizedDrive k σ L h)

theorem planarNormalizedResponse_equation (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    planarActiveMaterialOperator k hk L hL h θ α β
      (planarNormalizedResponse k hk σ L hL h θ α β hα hβ) = -planarNormalizedDrive k σ L h :=
  (planarActiveMaterialEquiv k hk L hL h θ α β hα hβ).apply_symm_apply _

theorem planarNormalizedResponse_norm_le (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    ‖planarNormalizedResponse k hk σ L hL h θ α β hα hβ‖ ≤
      (1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β)) * ‖planarNormalizedDrive k σ L h‖ := by
  have he := planarActiveMaterialEquiv_inverse_norm_le k hk L hL h θ α β hα hβ
  have hn := (planarActiveMaterialEquiv k hk L hL h θ α β hα hβ).symm.toContinuousLinearMap.le_opNorm
    (-planarNormalizedDrive k σ L h)
  exact hn.trans (by simpa only [norm_neg] using mul_le_mul_of_nonneg_right he (norm_nonneg (-planarNormalizedDrive k σ L h)))

theorem planarNormalizedResponse_continuous (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L) (h : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ : ℝ => planarNormalizedResponse k hk σ L hL h θ α β hα hβ) := by
  letI : NormedAddCommGroup (PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L) := inferInstance
  have hm : Continuous (fun _ : ℝ => planarInverseMaterial L h α β) := continuous_const
  have ht := (planarActiveOutgoing_rotation_continuous k hk L hL h).sub hm
  apply continuous_iff_continuousAt.mpr
  intro θ
  apply continuousLinearEquiv_response_continuousAt
    (fun φ => planarActiveMaterialEquiv k hk L hL h φ α β hα hβ)
    (fun _ => -planarNormalizedDrive k σ L h) θ
    (1 / min (α.im / Complex.normSq α) (β.im / Complex.normSq β))
  · intro φ
    exact planarActiveMaterialEquiv_inverse_norm_le k hk L hL h φ α β hα hβ
  · change ContinuousAt (fun φ => planarActiveMaterialOperator k hk L hL h φ α β) θ
    exact ht.continuousAt
  · exact continuousAt_const

def planarNormalizedExtinction (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  k * (inner ℂ (planarNormalizedDrive k σ L h) (planarNormalizedResponse k hk σ L hL h θ α β hα hβ)).im

def planarNormalizedAbsorption (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L) (h θ : ℝ)
    (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) : ℝ :=
  k * -(inner ℂ (planarNormalizedResponse k hk σ L hL h θ α β hα hβ)
    (planarInverseMaterial L h α β (planarNormalizedResponse k hk σ L hL h θ α β hα hβ))).im

theorem planarNormalizedResponse_ne_zero (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L)
    (h θ : ℝ) (hh : 0 ≤ h) (hplate : h < L) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    planarNormalizedResponse k hk σ L hL h θ α β hα hβ ≠ 0 := by
  intro hz
  have he := planarNormalizedResponse_equation k hk σ L hL h θ α β hα hβ
  rw [hz, map_zero] at he
  exact planarNormalizedDrive_ne_zero k σ L h hh hplate (neg_eq_zero.mp he.symm)

theorem planarNormalizedAbsorption_pos (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L)
    (h θ : ℝ) (hh : 0 ≤ h) (hplate : h < L) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    0 < planarNormalizedAbsorption k hk σ L hL h θ α β hα hβ := by
  have hc := activeMaterialCoercivity_pos α β hα hβ
  have hn := norm_pos_iff.mpr (planarNormalizedResponse_ne_zero k hk σ L hL h θ hh hplate α β hα hβ)
  have he := planarInverseMaterial_negative_imaginary_bound L h α β (planarNormalizedResponse k hk σ L hL h θ α β hα hβ)
  exact mul_pos hk ((mul_pos hc (sq_pos_of_pos hn)).trans_le he)

theorem planarNormalizedExtinction_work_balance (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L)
    (h θ : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    planarNormalizedExtinction k hk σ L hL h θ α β hα hβ =
      planarNormalizedAbsorption k hk σ L hL h θ α β hα hβ + k *
        (inner ℂ (planarNormalizedResponse k hk σ L hL h θ α β hα hβ)
          (planarActiveOutgoing k hk L hL h θ (planarNormalizedResponse k hk σ L hL h θ α β hα hβ))).im := by
  let r := planarNormalizedResponse k hk σ L hL h θ α β hα hβ
  have he := planarNormalizedResponse_equation k hk σ L hL h θ α β hα hβ
  change planarActiveOutgoing k hk L hL h θ r - planarInverseMaterial L h α β r = -planarNormalizedDrive k σ L h at he
  have hi := congrArg (fun z => (inner ℂ r z).im) he
  rw [inner_sub_right, inner_neg_right, Complex.sub_im, Complex.neg_im] at hi
  have hs := inner_im_symm (𝕜 := ℂ) (planarNormalizedDrive k σ L h) r
  change (inner ℂ (planarNormalizedDrive k σ L h) r).im = -(inner ℂ r (planarNormalizedDrive k σ L h)).im at hs
  change k * (inner ℂ (planarNormalizedDrive k σ L h) r).im =
    k * -(inner ℂ r (planarInverseMaterial L h α β r)).im + k * (inner ℂ r (planarActiveOutgoing k hk L hL h θ r)).im
  rw [hs, ← hi]
  ring

theorem planarNormalizedExtinction_pos (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L)
    (h θ : ℝ) (hh : 0 ≤ h) (hplate : h < L) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    0 < planarNormalizedExtinction k hk σ L hL h θ α β hα hβ := by
  rw [planarNormalizedExtinction_work_balance]
  exact add_pos_of_pos_of_nonneg (planarNormalizedAbsorption_pos k hk σ L hL h θ hh hplate α β hα hβ)
    (mul_nonneg hk.le (planarActiveOutgoing_im_nonneg k hk L hL h θ _))

theorem planarNormalizedExtinction_continuous (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L)
    (h : ℝ) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im) :
    Continuous (fun θ => planarNormalizedExtinction k hk σ L hL h θ α β hα hβ) :=
  continuous_const.mul (Complex.continuous_im.comp (continuous_const.inner
    (planarNormalizedResponse_continuous k hk σ L hL h α β hα hβ)))

theorem planarNormalizedExtinction_compact_lower_bound (k : ℝ) (hk : 0 < k) (σ : Direction) (L : ℝ) (hL : 0 ≤ L)
    (h : ℝ) (hh : 0 ≤ h) (hplate : h < L) (α β : ℂ) (hα : 0 < α.im) (hβ : 0 < β.im)
    (s : Set ℝ) (hs : IsCompact s) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ s, c ≤ planarNormalizedExtinction k hk σ L hL h θ α β hα hβ :=
  hs.exists_forall_le' (planarNormalizedExtinction_continuous k hk σ L hL h α β hα hβ).continuousOn
    (fun θ _ => planarNormalizedExtinction_pos k hk σ L hL h θ hh hplate α β hα hβ)

end OQ7Prescribed
