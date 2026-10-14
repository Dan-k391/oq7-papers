import work.PlanarHeightGreen
import work.SlabSupportedLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory

theorem scalarPlanarPotential_congr_ae (k : ℝ) (q r : ℝ → ℂ) (he : q =ᵐ[volume] r) :
    scalarPlanarPotential k q = scalarPlanarPotential k r := by
  funext z
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

theorem scalarPlanarPotential_add (k : ℝ) (hk : 0 < k) (q r : ℝ → ℂ)
    (hq : Integrable q volume) (hr : Integrable r volume) :
    scalarPlanarPotential k (fun t => q t + r t) =
      fun z => scalarPlanarPotential k q z + scalarPlanarPotential k r z := by
  funext z
  simp only [scalarPlanarPotential, mul_add]
  exact integral_add (scalarPlanarPotential_integrand_integrable k hk q hq z)
    (scalarPlanarPotential_integrand_integrable k hk r hr z)

theorem scalarPlanarPotential_smul (k : ℝ) (q : ℝ → ℂ) (a : ℂ) :
    scalarPlanarPotential k (fun t => a * q t) = fun z => a * scalarPlanarPotential k q z := by
  funext z
  unfold scalarPlanarPotential
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by ring

theorem heightSupportedProfile_integrable (M : ℝ) (q : HeightSupportedL2 M) :
    Integrable (q : HeightL2) volume :=
  heightProfile_integrable (q : HeightL2) (Lp.memLp (q : HeightL2)) M q.property

def planarHeightRaw (k : ℝ) (hk : 0 < k) (M L : ℝ) (q : HeightSupportedL2 M) : HeightL2 :=
  (scalarPlanarPotential_height_memLp k hk (q : HeightL2) (heightSupportedProfile_integrable M q) L).toLp
    ((Icc 0 L).indicator (scalarPlanarPotential k (q : HeightL2)))

theorem planarHeightRaw_coe (k : ℝ) (hk : 0 < k) (M L : ℝ) (q : HeightSupportedL2 M) :
    planarHeightRaw k hk M L q =ᵐ[volume]
      (Icc 0 L).indicator (scalarPlanarPotential k (q : HeightL2)) :=
  (scalarPlanarPotential_height_memLp k hk (q : HeightL2) (heightSupportedProfile_integrable M q) L).coeFn_toLp

theorem planarHeightRaw_norm_le (k : ℝ) (hk : 0 < k) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (q : HeightSupportedL2 M) :
    ‖planarHeightRaw k hk M L q‖ ≤ (Real.sqrt L * (1 / (2 * k)) * Real.sqrt (2 * M)) * ‖q‖ := by
  change ‖planarHeightRaw k hk M L q‖ ≤ (Real.sqrt L * (1 / (2 * k)) * Real.sqrt (2 * M)) * ‖(q : HeightL2)‖
  have he := scalarPlanarPotential_height_norm_bound k hk (q : HeightL2)
    (heightSupportedProfile_integrable M q) L hL
  have hi := heightProfile_integral_norm_bound (q : HeightL2) (Lp.memLp (q : HeightL2)) M hM q.property
  rw [Lp.toLp_coeFn] at hi
  have hc : 0 ≤ Real.sqrt L * (1 / (2 * k)) := by positivity
  refine he.trans ((mul_le_mul_of_nonneg_left hi hc).trans_eq ?_)
  ring

def planarHeightLinear (k : ℝ) (hk : 0 < k) (M L : ℝ) : HeightSupportedL2 M →ₗ[ℂ] HeightL2 where
  toFun := planarHeightRaw k hk M L
  map_add' q r := by
    have he := scalarPlanarPotential_congr_ae k (q + r : HeightL2)
      (fun t => (q : HeightL2) t + (r : HeightL2) t) (Lp.coeFn_add (q : HeightL2) (r : HeightL2))
    have hid := scalarPlanarPotential_add k hk (q : HeightL2) (r : HeightL2)
      (heightSupportedProfile_integrable M q) (heightSupportedProfile_integrable M r)
    apply Lp.ext
    filter_upwards [planarHeightRaw_coe k hk M L (q + r), planarHeightRaw_coe k hk M L q,
      planarHeightRaw_coe k hk M L r,
      Lp.coeFn_add (planarHeightRaw k hk M L q) (planarHeightRaw k hk M L r)] with z ha hq hr hb
    rw [ha, hb]
    change (Icc 0 L).indicator (scalarPlanarPotential k (q + r : HeightL2)) z =
      planarHeightRaw k hk M L q z + planarHeightRaw k hk M L r z
    rw [hq, hr]
    by_cases hz : z ∈ Icc 0 L
    · simp only [indicator_of_mem hz]
      rw [he, hid]
    · simp only [indicator_of_notMem hz, add_zero]
  map_smul' a q := by
    have he := scalarPlanarPotential_congr_ae k ((a • (q : HeightL2) : HeightL2) : ℝ → ℂ)
      (fun t => a * (q : HeightL2) t) (Lp.coeFn_smul a (q : HeightL2))
    have hid := scalarPlanarPotential_smul k (q : HeightL2) a
    apply Lp.ext
    filter_upwards [planarHeightRaw_coe k hk M L (a • q), planarHeightRaw_coe k hk M L q,
      Lp.coeFn_smul a (planarHeightRaw k hk M L q)] with z ha hq hb
    change planarHeightRaw k hk M L (a • q) z = (a • planarHeightRaw k hk M L q) z
    rw [ha, hb]
    change (Icc 0 L).indicator (scalarPlanarPotential k ((a • (q : HeightL2) : HeightL2) : ℝ → ℂ)) z =
      a * planarHeightRaw k hk M L q z
    rw [hq]
    by_cases hz : z ∈ Icc 0 L
    · simp only [indicator_of_mem hz]
      rw [he, hid]
    · simp only [indicator_of_notMem hz, mul_zero]

def planarHeightMap (k : ℝ) (hk : 0 < k) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    HeightSupportedL2 M →L[ℂ] HeightL2 :=
  (planarHeightLinear k hk M L).mkContinuous (Real.sqrt L * (1 / (2 * k)) * Real.sqrt (2 * M))
    fun q => planarHeightRaw_norm_le k hk M L hM hL q

theorem planarHeightMap_coe (k : ℝ) (hk : 0 < k) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (q : HeightSupportedL2 M) : planarHeightMap k hk M L hM hL q =ᵐ[volume]
      (Icc 0 L).indicator (scalarPlanarPotential k (q : HeightL2)) :=
  planarHeightRaw_coe k hk M L q

end OQ7Prescribed
