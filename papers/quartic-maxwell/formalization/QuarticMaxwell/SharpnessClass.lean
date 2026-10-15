import QuarticMaxwell.FixedPatternDilation
import QuarticMaxwell.Asymptotics

/-! The actual admissible design class and its uniform fixed-resource upper
bound. These definitions use outgoing weak states and literal physical powers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell.SharpnessClass
open MeasureTheory Set OQ7Prescribed WeakMaterial PhysicalPowers FixedPatternContrast

def Reciprocal (B : Medium) : Prop :=
  ∀ᵐ x ∂volume, x ∈ B.domain → ∀ u v : Vector,
    bilinear u (B.susceptibility x v) = bilinear v (B.susceptibility x u)

def Admissible (m M R : ℝ) (B : Medium) : Prop :=
  0 < volume.real B.domain ∧ Reciprocal B ∧ B.M ≤ M ∧ m ≤ B.m ∧ B.radius ≤ R

def values (m M k R : ℝ) (n : UnitSphere) (e : Vector) : Set ℝ :=
  {v | ∃ B : Medium, Admissible m M R B ∧
    ∃ s : State B k n e, ∃ q : State B k (opposite n) e, v = contrast B k n e s q}

def upperConstant (m M : ℝ) : ℝ :=
  (8 / 9 : ℝ) * (M ^ 2 / m) ^ 2 * (1 / m + 7 / 4)

theorem upperConstant_pos (m M : ℝ) (hm : 0 < m) (hM : m ≤ M) :
    0 < upperConstant m M := by
  have hMp := hm.trans_le hM
  unfold upperConstant
  positivity

theorem uniform_upper (m M k R : ℝ) (hm : 0 < m) (hM : m ≤ M)
    (hk : 0 < k) (_hR : 0 < R) (hsmall : k * R ≤ 1)
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0)
    (B : Medium) (hB : Admissible m M R B)
    (s : State B k n e) (q : State B k (opposite n) e) :
    contrast B k n e s q ≤ upperConstant m M * (k * R) ^ 4 := by
  have h := (theorem11_ball B hk hB.1 hB.2.1 n e he hen htr s q).2
  have hMp := hm.trans_le hM
  have hrho : B.M ^ 2 / B.m ≤ M ^ 2 / m := by
    gcongr
    exact B.M_pos.le
    exact hB.2.2.1
    exact hB.2.2.2.1
  have hrad : k * B.radius ≤ k * R := mul_le_mul_of_nonneg_left hB.2.2.2.2 hk.le
  have hrad0 : 0 ≤ k * B.radius := mul_nonneg hk.le B.radius_nonneg
  have hsquare : (k * B.radius) ^ 2 ≤ 1 := by nlinarith [hrad.trans hsmall]
  have hden : 1 / B.m ≤ 1 / m := one_div_le_one_div_of_le hm hB.2.2.2.1
  have hp : 1 / B.m + 1 + 3 / 4 * (k * B.radius) ^ 2 ≤ 1 / m + 7 / 4 := by
    linarith
  have hpow : (k * B.radius) ^ 4 ≤ (k * R) ^ 4 := by gcongr
  change contrast B k n e s q ≤ _ at h
  calc
    _ ≤ (8 / 9 : ℝ) * (B.M ^ 2 / B.m) ^ 2 *
        (1 / B.m + 1 + 3 / 4 * (k * B.radius) ^ 2) * (k * B.radius) ^ 4 :=
      h.trans (min_le_right _ _)
    _ ≤ upperConstant m M * (k * R) ^ 4 := by
      unfold upperConstant
      gcongr
      · positivity [B.m_pos]
      · exact div_nonneg (sq_nonneg _) B.m_pos.le

theorem values_upper (m M k R : ℝ) (hm : 0 < m) (hM : m ≤ M)
    (hk : 0 < k) (hR : 0 < R) (hsmall : k * R ≤ 1)
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0) :
    ∀ v ∈ values m M k R n e, v ≤ upperConstant m M * (k * R) ^ 4 := by
  rintro v ⟨B, hB, s, q, rfl⟩
  exact uniform_upper m M k R hm hM hk hR hsmall n e he hen htr B hB s q

theorem scaled_volume (B : Medium) (r : ℝ) (hr : 0 < r) :
    volume.real (PhysicalDilation.medium B r hr).domain = r ^ 3 * volume.real B.domain := by
  have h := PhysicalDilation.integral_scale r⁻¹ (inv_pos.mpr hr)
    (B.domain.indicator (fun _ : Position => (1 : ℝ)))
  have hi : (fun x : Position => B.domain.indicator (fun _ : Position => (1 : ℝ)) (r⁻¹ • x)) =
      (PhysicalDilation.medium B r hr).domain.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : r⁻¹ • x ∈ B.domain <;> simp [Set.indicator, PhysicalDilation.medium, hx]
  rw [hi, integral_indicator_const _ (PhysicalDilation.medium B r hr).measurable,
    integral_indicator_const _ B.measurable] at h
  simpa only [smul_eq_mul, mul_one, inv_pow, inv_inv] using h

theorem scaled_reciprocal (B : Medium) (hB : Reciprocal B) (r : ℝ) (hr : 0 < r) :
    Reciprocal (PhysicalDilation.medium B r hr) := by
  exact (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).ae hB

theorem scaled_admissible (m M : ℝ) (B : Medium) (hB : Admissible m M 1 B)
    (r : ℝ) (hr : 0 < r) : Admissible m M r (PhysicalDilation.medium B r hr) := by
  refine ⟨?_, scaled_reciprocal B hB.2.1 r hr, hB.2.2.1, hB.2.2.2.1, ?_⟩
  · rw [scaled_volume]
    exact mul_pos (pow_pos hr 3) hB.1
  · change r * B.radius ≤ r
    nlinarith [hB.2.2.2.2]

def lowerScale (B : Medium) (n : UnitSphere) (e : Vector) : ℝ :=
  min (interval B e) (Real.sqrt (coefficient B n e / (2 * (|remainderConstant B n e| + 1))))

theorem lowerScale_pos (B : Medium) (hV : 0 < volume.real B.domain)
    (n : UnitSphere) (e : Vector) (hen : ‖e‖ = 1) (hC : 0 < coefficient B n e) :
    0 < lowerScale B n e := by
  unfold lowerScale
  exact lt_min (FixedPatternContrast.interval_pos B hV n e hen)
    (Real.sqrt_pos.mpr (div_pos hC (by positivity)))

theorem physical_lower (B : Medium) (hV : 0 < volume.real B.domain) (hsym : Reciprocal B)
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0) (hC : 0 < coefficient B n e)
    (k r : ℝ) (hk : 0 < k) (hr : 0 < r) (hsmall : k * r ≤ lowerScale B n e)
    (s : State (PhysicalDilation.medium B r hr) k n e)
    (q : State (PhysicalDilation.medium B r hr) k (opposite n) e) :
    coefficient B n e / 2 * (k * r) ^ 4 ≤
      contrast (PhysicalDilation.medium B r hr) k n e s q := by
  have hki : k * r ≤ interval B e := hsmall.trans (min_le_left _ _)
  have herr := FixedPatternDilation.fixed_wavenumber_quartic B hV hsym k hk n e he hen htr
    r hr ((le_div_iff₀ hk).mpr (by nlinarith [hki])) s q
  have hroot : k * r ≤ Real.sqrt (coefficient B n e / (2 * (|remainderConstant B n e| + 1))) :=
    hsmall.trans (min_le_right _ _)
  have ht := mul_pos hk hr
  have hsq := (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).mpr hroot
  rw [Real.sq_sqrt (by positivity)] at hsq
  have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (|remainderConstant B n e| + 1))).mp hsq
  have hs : |remainderConstant B n e| * (k * r) ^ 2 ≤ coefficient B n e / 2 := by
    nlinarith [sq_nonneg (k * r)]
  have herr' := herr.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity : 0 ≤ (k * r) ^ 6))
  exact positive_coefficient_lower_bound ht.le le_rfl (abs_nonneg _) herr' hs

theorem lower_member (m M : ℝ) (B : Medium) (hB : Admissible m M 1 B)
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0) (hC : 0 < coefficient B n e)
    (k r : ℝ) (hk : 0 < k) (hr : 0 < r) (hsmall : k * r ≤ lowerScale B n e) :
    ∃ v ∈ values m M k r n e, coefficient B n e / 2 * (k * r) ^ 4 ≤ v := by
  let Bs := PhysicalDilation.medium B r hr
  let s := solution Bs k hk n e htr
  let q := solution Bs k hk (opposite n) e (opposite_transverse n e htr)
  refine ⟨contrast Bs k n e s q, ⟨Bs, scaled_admissible m M B hB r hr, s, q, rfl⟩, ?_⟩
  exact physical_lower B hB.1 hB.2.1 n e he hen htr hC k r hk hr hsmall s q

theorem sSup_sandwich (m M : ℝ) (hm : 0 < m) (hM : m ≤ M)
    (B : Medium) (hB : Admissible m M 1 B)
    (n : UnitSphere) (e : Vector) (he : vectorConjugate e = e) (hen : ‖e‖ = 1)
    (htr : bilinear (complexify (n : Position)) e = 0) (hC : 0 < coefficient B n e)
    (k R : ℝ) (hk : 0 < k) (hR : 0 < R)
    (hsmall : k * R ≤ min 1 (lowerScale B n e)) :
    coefficient B n e / 2 * (k * R) ^ 4 ≤ sSup (values m M k R n e) ∧
      sSup (values m M k R n e) ≤ upperConstant m M * (k * R) ^ 4 := by
  obtain ⟨v, hv, hlo⟩ := lower_member m M B hB n e he hen htr hC k R hk hR
    (hsmall.trans (min_le_right _ _))
  have hup := values_upper m M k R hm hM hk hR (hsmall.trans (min_le_left _ _)) n e he hen htr
  have hb : BddAbove (values m M k R n e) := ⟨upperConstant m M * (k * R) ^ 4, hup⟩
  exact ⟨hlo.trans (le_csSup hb hv), csSup_le ⟨v, hv⟩ hup⟩

end QuarticMaxwell.SharpnessClass
