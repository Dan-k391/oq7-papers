import work.WeakLorentzBoundaryBound
import work.SmoothSourceWeakDecay
import work.CompactFieldTestSeparation

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem vacuum_outgoing_weak_smooth_work_zero (k : ℝ) (hk : 0 < k) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (hout : Outgoing E H) (q : CompactPolarization) (hq : ContDiff ℝ (⊤ : ℕ∞) q.current) :
    (∫ x : Position, bilinear (q.current x) (E x)) = 0 := by
  let N := ∫ y : Position, ‖q.current y‖
  let B := electricDecayConstant k q.radius * N
  let C := radiationKernelConstant k q.radius * N
  let W := (Complex.I * (k : ℂ)) * (∫ x : Position, bilinear (q.current x) (E x))
  have hN : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (electricDecayConstant_nonneg k q.radius q.radius_nonneg) hN
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖W‖ ≤ 4 * Real.pi * (ε ^ 2 + B * ε) := by
    obtain ⟨ρ, _, hb⟩ := hout ε hε
    let r := max ρ (max (2 * q.radius + 2) (C / ε))
    have hρr : ρ ≤ r := le_max_left _ _
    have hqr : 2 * q.radius + 2 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
    have hr : 0 < r := by linarith [q.radius_nonneg]
    have hCr : C / ε ≤ r := (le_max_right _ _).trans (le_max_right _ _)
    have hc : C ≤ ε * r := by have h := (div_le_iff₀ hε).mp hCr; simpa [mul_comm] using h
    have hd := smooth_source_weak_decay k q hq r ε hε.le hqr hc
    have henergy := vacuum_weak_weighted_electric_energy k E H hE hH he hh ε ρ hε hb r hr hρr
    have hflux := weak_Lorentz_boundary_bound E H (smoothElectricSource k q) (smoothMagneticSource k q)
      hE r ε B ρ hr hε hB hρr hb hd henergy
    change ‖∫ x : Position, (sourceEnergyWeight r x : ℂ) *
      (bilinear (E x) (cross (smoothMagneticSource k q x) (complexify (radialDirection x))) -
        bilinear (smoothElectricSource k q x) (cross (H x) (complexify (radialDirection x))))‖ ≤ _ at hflux
    rw [vacuum_weak_smooth_source_radial_Lorentz k E H hE hH he hh q hq r hr
      (by linarith [q.radius_nonneg])] at hflux
    exact hflux
  have hW : W = 0 := by
    by_contra hn
    have hw : 0 < ‖W‖ := norm_pos_iff.mpr hn
    let M := 4 * Real.pi * (1 + B)
    have hM : 0 < M := by dsimp [M]; positivity
    let ε := min 1 (‖W‖ / (2 * M))
    have hε : 0 < ε := lt_min (by norm_num) (div_pos hw (by positivity))
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεW : ε ≤ ‖W‖ / (2 * M) := min_le_right _ _
    have hem : ε * (2 * M) ≤ ‖W‖ := (le_div_iff₀ (by positivity)).mp hεW
    have hs : ε ^ 2 ≤ ε := by nlinarith
    have hscale : 4 * Real.pi * (ε ^ 2 + B * ε) ≤ M * ε := by
      have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * Real.pi)
      dsimp [M]
      nlinarith
    have hsmall := (hbound ε hε).trans hscale
    linarith
  have hkC : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk.ne')
  exact (mul_eq_zero.mp hW).resolve_left hkC

/-- A globally source-free locally-L2 weak Maxwell pair satisfying the
original full uniform Silver–Muller condition is zero almost everywhere. -/
theorem vacuum_outgoing_weak_unique_zero (k : ℝ) (hk : 0 < k) (E H : Field)
    (hE : LocallySquareIntegrable E) (hH : LocallySquareIntegrable H)
    (he : HasWeakCurl E (fun x => (Complex.I * (k : ℂ)) • H x))
    (hh : HasWeakCurl H (fun x => (-Complex.I * (k : ℂ)) • E x))
    (hout : Outgoing E H) : E =ᵐ[volume] 0 ∧ H =ᵐ[volume] 0 := by
  have hEl := locallySquareIntegrable_locallyIntegrable E hE
  have hHl := locallySquareIntegrable_locallyIntegrable H hH
  have hEz : E =ᵐ[volume] 0 := field_zero_ae_of_compact_smooth_bilinear_tests E hEl
    (fun q hq => vacuum_outgoing_weak_smooth_work_zero k hk E H hE hH he hh hout q hq)
  refine ⟨hEz, ?_⟩
  apply field_zero_ae_of_compact_smooth_bilinear_tests H hHl
  intro q hq
  have he0 : HasWeakCurl 0 (fun x => (Complex.I * (k : ℂ)) • H x) :=
    he.congr_ae hEz (ae_of_all _ fun _ => rfl)
  have ht := he0 q.current hq (compactPolarization_current_hasCompactSupport q)
  have hl : (∫ x : Position, bilinear (0 : Vector) (curl q.current x)) = 0 := by simp [bilinear]
  have hp : (fun x => bilinear ((Complex.I * (k : ℂ)) • H x) (q.current x)) =
      fun x => (Complex.I * (k : ℂ)) * bilinear (q.current x) (H x) := by
    funext x
    rw [bilinear_complex_smul_left, bilinear_comm]
  change (∫ x : Position, bilinear (0 : Vector) (curl q.current x)) =
    ∫ x : Position, bilinear ((Complex.I * (k : ℂ)) • H x) (q.current x) at ht
  rw [hl, hp, integral_const_mul] at ht
  have hkC : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk.ne')
  exact (mul_eq_zero.mp ht.symm).resolve_left hkC

end OQ7Prescribed
