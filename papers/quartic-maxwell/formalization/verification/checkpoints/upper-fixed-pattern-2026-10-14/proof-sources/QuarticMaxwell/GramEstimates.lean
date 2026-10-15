import QuarticMaxwell.RadiationTaylor

/-! Quantitative bounds for the actual complete-angle radiation Gram map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QuarticMaxwell
open MeasureTheory Set OQ7Prescribed

theorem inner_central_difference {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B C : H →L[ℂ] E) (p q : H) :
    inner ℂ (A p) (A q) + inner ℂ (C p) (C q) - 2 * inner ℂ (B p) (B q) =
      inner ℂ (B p) ((A + C - (2 : ℂ) • B) q) +
      inner ℂ ((A + C - (2 : ℂ) • B) p) (B q) +
      inner ℂ ((A - B) p) ((A - B) q) +
      inner ℂ ((C - B) p) ((C - B) q) := by
  simp only [add_apply, sub_apply, smul_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, map_ofNat]
  ring

theorem even_gram_pairing_bound {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B C : H →L[ℂ] E) {b d e : ℝ} (_hb : 0 ≤ b) (_hd : 0 ≤ d) (_he : 0 ≤ e)
    (hB : ∀ f, ‖B f‖ ≤ b * ‖f‖)
    (hAB : ∀ f, ‖(A - B) f‖ ≤ d * ‖f‖)
    (hCB : ∀ f, ‖(C - B) f‖ ≤ d * ‖f‖)
    (hE : ∀ f, ‖(A + C - (2 : ℂ) • B) f‖ ≤ e * ‖f‖)
    (heven : ∀ p q, inner ℂ (C p) (C q) = inner ℂ (A p) (A q)) (p q : H) :
    ‖inner ℂ (A p) (A q) - inner ℂ (B p) (B q)‖ ≤
      (b * e + d ^ 2) * ‖p‖ * ‖q‖ := by
  have hid := inner_central_difference A B C p q
  rw [heven] at hid
  have hid' : (2 : ℂ) * (inner ℂ (A p) (A q) - inner ℂ (B p) (B q)) =
      inner ℂ (B p) ((A + C - (2 : ℂ) • B) q) +
      inner ℂ ((A + C - (2 : ℂ) • B) p) (B q) +
      inner ℂ ((A - B) p) ((A - B) q) +
      inner ℂ ((C - B) p) ((C - B) q) := by convert hid using 1; ring
  have hn (f g : E) (x y : ℝ) (hx : ‖f‖ ≤ x) (hy : ‖g‖ ≤ y) :
      ‖inner ℂ f g‖ ≤ x * y :=
    (norm_inner_le_norm f g).trans (mul_le_mul hx hy (norm_nonneg g) ((norm_nonneg f).trans hx))
  have hnorm := congrArg norm hid'
  rw [norm_mul] at hnorm
  norm_num only [Complex.norm_ofNat] at hnorm
  have hsum := norm_add_le
    (inner ℂ (B p) ((A + C - (2 : ℂ) • B) q) +
      inner ℂ ((A + C - (2 : ℂ) • B) p) (B q) +
      inner ℂ ((A - B) p) ((A - B) q))
    (inner ℂ ((C - B) p) ((C - B) q))
  have hsum₂ := norm_add_le
    (inner ℂ (B p) ((A + C - (2 : ℂ) • B) q) +
      inner ℂ ((A + C - (2 : ℂ) • B) p) (B q))
    (inner ℂ ((A - B) p) ((A - B) q))
  have hsum₁ := norm_add_le
    (inner ℂ (B p) ((A + C - (2 : ℂ) • B) q))
    (inner ℂ ((A + C - (2 : ℂ) • B) p) (B q))
  have h₁ := hn _ _ _ _ (hB p) (hE q)
  have h₂ := hn _ _ _ _ (hE p) (hB q)
  have h₃ := hn _ _ _ _ (hAB p) (hAB q)
  have h₄ := hn _ _ _ _ (hCB p) (hCB q)
  nlinarith only [hnorm, hsum, hsum₂, hsum₁, h₁, h₂, h₃, h₄]

theorem domainRadiationMap_apply_norm_bound (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) (f : DomainL2 D) :
    ‖domainRadiationMap k D hD hfin f‖ ≤
      Real.sqrt (8 * Real.pi * volume.real D / 3) * ‖f‖ := by
  apply (domainRadiationMap k D hD hfin).le_opNorm f |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (domainRadiationMap_norm_sq_le k D hD hfin)

theorem radiationGram_norm_le (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) :
    ‖radiationGram k D hD hfin‖ ≤ volume.real D / (6 * Real.pi) := by
  let : CompleteSpace (DomainL2 D) := domainCompleteSpace D hD
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    _ ≤ (1 / (16 * Real.pi ^ 2)) *
        (‖domainRadiationMap k D hD hfin‖ * ‖domainRadiationMap k D hD hfin‖) := by
      unfold radiationGram
      change ‖(((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ)) •
        ((domainRadiationMap k D hD hfin).adjoint ∘L domainRadiationMap k D hD hfin)‖ ≤ _
      calc
        _ ≤ ‖(((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ))‖ *
            ‖(domainRadiationMap k D hD hfin).adjoint ∘L domainRadiationMap k D hD hfin‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ = _ := by rw [ContinuousLinearMap.norm_adjoint_comp_self, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (1 / (16 * Real.pi ^ 2)) * (8 * Real.pi * volume.real D / 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using domainRadiationMap_norm_sq_le k D hD hfin
    _ = _ := by field_simp; ring

theorem radiationGram_difference_pairing_bound (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) (p q : DomainL2 D) :
    ‖inner ℂ p ((radiationGram k D hD hfin - radiationGram 0 D hD hfin) q)‖ ≤
      (volume.real D * R ^ 2 / (3 * Real.pi) * k ^ 2) * ‖p‖ * ‖q‖ := by
  let C := 8 * Real.pi * volume.real D / 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
  have h := even_gram_pairing_bound
    (domainRadiationMap k D hD hfin) (domainRadiationMap 0 D hD hfin)
    (domainRadiationMap (-k) D hD hfin)
    (Real.sqrt_nonneg C) (show 0 ≤ Real.sqrt C * (|k| * R) by positivity)
    (show 0 ≤ Real.sqrt C * (k ^ 2 * R ^ 2) by positivity)
    (domainRadiationMap_apply_norm_bound 0 D hD hfin)
    (domainRadiationMap_difference_apply_norm_le k D hD hfin hR hsub)
    (fun f => by simpa only [abs_neg] using domainRadiationMap_difference_apply_norm_le (-k) D hD hfin hR hsub f)
    (domainRadiationMap_even_remainder_apply_norm_le k D hD hfin hR hsub)
    (fun p q => by
      have he := linear_inner_of_norm_sq (domainRadiationMap (-k) D hD hfin).toLinearMap
        (domainRadiationMap k D hD hfin).toLinearMap 1
        (fun f => by simpa using domainRadiationMap_norm_sq_even k D hD hfin f) p q
      simpa using he) p q
  have heq : Real.sqrt C * (Real.sqrt C * (k ^ 2 * R ^ 2)) +
      (Real.sqrt C * (|k| * R)) ^ 2 = 2 * C * k ^ 2 * R ^ 2 := by
    calc
      _ = 2 * (Real.sqrt C) ^ 2 * k ^ 2 * R ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]
        ring
      _ = _ := by rw [hs]
  rw [heq] at h
  have hin : inner ℂ p ((radiationGram k D hD hfin - radiationGram 0 D hD hfin) q) =
      (((1 / (16 * Real.pi ^ 2) : ℝ) : ℂ)) *
      (inner ℂ (domainRadiationMap k D hD hfin p) (domainRadiationMap k D hD hfin q) -
       inner ℂ (domainRadiationMap 0 D hD hfin p) (domainRadiationMap 0 D hD hfin q)) := by
    change inner ℂ p (radiationGram k D hD hfin q - radiationGram 0 D hD hfin q) = _
    rw [inner_sub_right, radiationGram_inner, radiationGram_inner]
    ring
  rw [hin, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 / (16 * Real.pi ^ 2))).trans
  apply le_of_eq
  dsimp [C]
  field_simp
  ring

theorem radiationGram_difference_norm_le (k : ℝ) (D : Set Position)
    (hD : MeasurableSet D) (hfin : volume D ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hsub : D ⊆ Metric.closedBall (0 : Position) R) :
    ‖radiationGram k D hD hfin - radiationGram 0 D hD hfin‖ ≤
      volume.real D * R ^ 2 / (3 * Real.pi) * k ^ 2 := by
  apply operator_norm_of_quadratic_pairing _ (by positivity)
  intro q p
  apply (radiationGram_difference_pairing_bound k D hD hfin hR hsub p q).trans
  have hsq := sq_nonneg (‖p‖ - ‖q‖)
  have hC : 0 ≤ volume.real D * R ^ 2 / (3 * Real.pi) * k ^ 2 := by positivity
  nlinarith only [mul_nonneg hC hsq]

end QuarticMaxwell
