import work.SlabDyadicAperture
import work.DyadicAxisRepresentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open Set MeasureTheory
open scoped InnerProductSpace

def scalarAxisPolarization (f : Position → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (a : Position) : CompactPolarization := by
  let hb := hc.isBounded.subset_closedBall_lt 0 (0 : Position)
  let R := Classical.choose hb
  have hR := Classical.choose_spec hb
  have hpc : HasCompactSupport (fun x => f x • complexify a) := hc.smul_right
  exact {
    current := fun x => f x • complexify a
    radius := R
    radius_nonneg := hR.1.le
    memLp := (hf.smul continuous_const).memLp_of_hasCompactSupport hpc
    vanish := fun x hx => by
      have hn : x ∉ tsupport f := by
        intro h
        have he := hR.2 h
        simp only [Metric.mem_closedBall, dist_zero_right] at he
        exact (not_lt_of_ge he) hx
      rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
  }

theorem scalarAxisPolarization_current (f : Position → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (a : Position) :
    (scalarAxisPolarization f hf hc a).current = fun x => f x • complexify a := rfl

theorem slabPosition_horizontal_height (y : Position) :
    slabPosition (slabHorizontalCoordinate y) (y 2) = y := by
  ext i
  fin_cases i <;> simp [slabPosition, slabHorizontalCoordinate]

theorem smoothDyadicField_slab_source_projection (k : ℝ) (p : CompactPolarization)
    (w : ℂ → ℂ) (q : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hwc : HasCompactSupport w) (hqc : HasCompactSupport q) (u v x : ℂ) (z : ℝ)
    (hp : p.current = fun y => slabSeparatedFunction w q y • complexify (slabPosition u 0)) :
    axisCoupling (slabPosition v 0) (smoothDyadicField k p (slabPosition x z)) =
      scalarOutgoingSlabTransverse k w q x z u v := by
  rw [smoothDyadicField_axis_source_projection k p _
    (slabSeparatedFunction_contDiff w q hw hq)
    (slabSeparatedFunction_hasCompactSupport w q hwc hqc) _ _ hp]
  unfold scalarOutgoingSlabTransverse
  congr 2
  simp [slabPosition, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ, mul_comm]

theorem electricVolumeField_slab_uniform_aperture_error (k : ℝ) (hk : 0 < k)
    (w : ℂ → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (A X L : ℝ) (hA0 : 0 ≤ A) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hA : tsupport w ⊆ Metric.closedBall 0 A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) q → HasCompactSupport q →
      tsupport q ⊆ Icc 0 L → ∀ (R : ℝ) (u v : ℂ), 1 ≤ R → ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      ∀ p : CompactPolarization,
      p.current = (fun y => slabSeparatedFunction (scaledApertureWindow w R) q y •
        complexify (slabPosition u 0)) →
      ∀ᵐ y : Position ∂volume, ‖slabHorizontalCoordinate y‖ ≤ X * R → y 2 ∈ Icc 0 L →
        ‖axisCoupling (slabPosition v 0) (electricVolumeField k p y) -
          planarSlabTransverse k (scaledApertureWindow w R) q (slabHorizontalCoordinate y) (y 2) u v‖ ≤
            (C / R) * ∫ t : ℝ, ‖q t‖ := by
  obtain ⟨C, hC, he⟩ := scalarOutgoingSlabTransverse_uniform_aperture_error k hk w hw hwc A X L hA0 hX hL hA
  refine ⟨C, hC, ?_⟩
  intro q hq hqc hqs R u v hR hu hv p hp
  have hR0 : 0 < R := by linarith
  have hW := scaledApertureWindow_contDiff w hw R
  have hWc := scaledApertureWindow_hasCompactSupport w hwc R hR0.ne'
  have hpc : ContDiff ℝ (⊤ : ℕ∞) p.current := by
    rw [hp]
    exact (slabSeparatedFunction_contDiff _ q hW hq).smul contDiff_const
  filter_upwards [smoothDyadicField_eq_electricVolumeField k p hpc] with y hy
  intro hx hz
  rw [← hy, ← slabPosition_horizontal_height y,
    smoothDyadicField_slab_source_projection k p _ q hW hq hWc hqc u v _ _ hp]
  simpa only [slabPosition_horizontal_height] using he q hq hqc hqs R (y 2)
    (slabHorizontalCoordinate y) u v hR hz hx hu hv

end OQ7Prescribed
