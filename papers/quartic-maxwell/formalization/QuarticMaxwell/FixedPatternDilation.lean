import QuarticMaxwell.PhysicalDilation
import QuarticMaxwell.FixedPatternContrast

/-! Fixed physical wavenumber, shrinking actual spatial pattern R Ω.
The field and power change of variables is supplied by PhysicalDilation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
namespace FixedPatternDilation
open MeasureTheory OQ7Prescribed WeakMaterial PhysicalDilation PhysicalPowers

theorem contrast_congr (B : Medium) (k : ℝ) (n : UnitSphere) (e : Vector)
    (s u : State B k n e) (t v : State B k (opposite n) e)
    (hs : s.electric =ᵐ[volume] u.electric) (ht : t.electric =ᵐ[volume] v.electric) :
    FixedPatternContrast.contrast B k n e s t = FixedPatternContrast.contrast B k n e u v := by
  unfold FixedPatternContrast.contrast
  rw [absorption_congr B k hs, absorption_congr B k ht, extinction_congr B k n e hs]

theorem contrast_scale (B : Medium) (r : ℝ) (hr : 0 < r) (k : ℝ)
    (n : UnitSphere) (e : Vector) (s : State B (k * r) n e)
    (t : State B (k * r) (opposite n) e) :
    FixedPatternContrast.contrast (medium B r hr) k n e
      (state B r hr k n e s) (state B r hr k (opposite n) e t) =
        FixedPatternContrast.contrast B (k * r) n e s t := by
  unfold FixedPatternContrast.contrast
  change |absorption (medium B r hr) k (fun x => s.electric (r⁻¹ • x)) -
    absorption (medium B r hr) k (fun x => t.electric (r⁻¹ • x))| /
    extinction (medium B r hr) k n e (fun x => s.electric (r⁻¹ • x)) = _
  rw [absorption_scale, absorption_scale, extinction_scale, ← mul_sub, abs_mul,
    abs_of_pos (pow_pos hr 2)]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hr.ne')

/-- The original fixed-k shrinking-body statement, for every actual outgoing
weak state on the dilated measurable tensor pattern, with explicit O((kR)^6). -/
theorem fixed_wavenumber_quartic (B : Medium) (hV : 0 < volume.real B.domain)
    (hsym : ∀ᵐ x ∂volume, x ∈ B.domain → ∀ a b : Vector,
      bilinear a (B.susceptibility x b) = bilinear b (B.susceptibility x a))
    (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector)
    (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (r : ℝ) (hr : 0 < r) (hsmall : r ≤ FixedPatternContrast.interval B e / k)
    (s : State (medium B r hr) k n e) (t : State (medium B r hr) k (opposite n) e) :
    |FixedPatternContrast.contrast (medium B r hr) k n e s t -
      FixedPatternContrast.coefficient B n e * (k * r) ^ 4| ≤
        FixedPatternContrast.remainderConstant B n e * (k * r) ^ 6 := by
  have hkr := mul_pos hk hr
  let s0 := solution B (k * r) hkr n e htr
  let t0 := solution B (k * r) hkr (opposite n) e (opposite_transverse n e htr)
  have hs := state_electric_unique (medium B r hr) k hk n e htr s (state B r hr k n e s0)
  have ht := state_electric_unique (medium B r hr) k hk (opposite n) e
    (opposite_transverse n e htr) t (state B r hr k (opposite n) e t0)
  rw [contrast_congr _ _ _ _ s _ t _ hs ht, contrast_scale]
  apply FixedPatternContrast.fixed_pattern_quartic B hV hsym n e he hen htr
    (k * r) hkr _ s0 t0
  have hh := (le_div_iff₀ hk).mp hsmall
  nlinarith

theorem interval_pos (B : Medium) (hV : 0 < volume.real B.domain)
    (k : ℝ) (hk : 0 < k) (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) :
    0 < FixedPatternContrast.interval B e / k :=
  div_pos (FixedPatternContrast.interval_pos B hV n e hen) hk

end FixedPatternDilation
end QuarticMaxwell
