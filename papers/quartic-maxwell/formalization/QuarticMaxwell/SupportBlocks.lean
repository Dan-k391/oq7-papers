import QuarticMaxwell.SphereResponse

/-! Actual orthogonal support decomposition of the zero-extension L² spaces.
The two off-diagonal block norms combine without an extra factor of two. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QuarticMaxwell.SupportBlocks
open OQ7Prescribed MeasureTheory Set

variable (D E : Set OQ7Prescribed.Position)

def inclusionLinear (hsub : D ⊆ E) : DomainL2 D →ₗ[ℂ] DomainL2 E where
  toFun f := ⟨(f : VectorL2), by
    change ∀ᵐ x ∂volume, x ∉ E → (f : VectorL2) x = 0
    filter_upwards [f.property] with x hx hmem
    exact hx (fun hxd => hmem (hsub hxd))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inclusion (hsub : D ⊆ E) : DomainL2 D →L[ℂ] DomainL2 E :=
  (inclusionLinear D E hsub).mkContinuous 1 (fun f => by simp [inclusionLinear])

theorem inclusion_coe (hsub : D ⊆ E) (f : DomainL2 D) :
    (inclusion D E hsub f : VectorL2) = (f : VectorL2) := rfl

theorem inclusion_norm (hsub : D ⊆ E) (f : DomainL2 D) :
    ‖inclusion D E hsub f‖ = ‖f‖ := rfl

def restriction (hD : MeasurableSet D) : DomainL2 E →L[ℂ] DomainL2 D :=
  setRestrictionCLM volume D hD ∘L (setSupportedL2 (E := Vector) volume E).subtypeL

theorem restriction_coe (hD : MeasurableSet D) (f : DomainL2 E) :
    (restriction D E hD f : VectorL2) =ᵐ[volume] D.indicator (fun x => (f : VectorL2) x) :=
  indicatorL2_coe volume D hD (f : VectorL2)

theorem restriction_inclusion (hD : MeasurableSet D) (hsub : D ⊆ E) (f : DomainL2 D) :
    restriction D E hD (inclusion D E hsub f) = f := by
  apply Subtype.ext
  exact (indicatorL2_eq_self_iff volume D hD (f : VectorL2)).mpr f.property

theorem disjoint_inner (hdis : Disjoint D E) (f : DomainL2 D) (g : DomainL2 E) :
    inner ℂ (f : VectorL2) (g : VectorL2) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [f.property, g.property] with x hf hg
  by_cases hx : x ∈ D
  · rw [hg (fun he => (Set.disjoint_left.mp hdis hx he))]
    simp
  · rw [hf hx]
    simp

theorem restriction_other (hD : MeasurableSet D) (hdis : Disjoint D E) (f : DomainL2 E) :
    restriction D E hD f = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [restriction_coe D E hD f, f.property,
    Lp.coeFn_zero (E := Vector) (p := 2) (μ := volume)] with x hx hf hz
  change (restriction D E hD f : VectorL2) x = (0 : VectorL2) x
  rw [hx, hz]
  by_cases hmem : x ∈ D
  · simp [Set.indicator, hmem, hf (fun he => Set.disjoint_left.mp hdis hmem he)]
  · simp [Set.indicator, hmem]

def injectLeft : DomainL2 D →L[ℂ] DomainL2 (D ∪ E) := inclusion D (D ∪ E) subset_union_left

def injectRight : DomainL2 E →L[ℂ] DomainL2 (D ∪ E) := inclusion E (D ∪ E) subset_union_right

def projectLeft (hD : MeasurableSet D) : DomainL2 (D ∪ E) →L[ℂ] DomainL2 D :=
  restriction D (D ∪ E) hD

def projectRight (hE : MeasurableSet E) : DomainL2 (D ∪ E) →L[ℂ] DomainL2 E :=
  restriction E (D ∪ E) hE

theorem support_decomposition (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hdis : Disjoint D E) (f : DomainL2 (D ∪ E)) :
    injectLeft D E (projectLeft D E hD f) + injectRight D E (projectRight D E hE f) = f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [restriction_coe D (D ∪ E) hD f, restriction_coe E (D ∪ E) hE f,
    f.property, Lp.coeFn_add (projectLeft D E hD f : VectorL2)
      (projectRight D E hE f : VectorL2)] with x hl hr hf ha
  change ((projectLeft D E hD f : VectorL2) + (projectRight D E hE f : VectorL2)) x = _
  rw [ha]
  change (restriction D (D ∪ E) hD f : VectorL2) x +
    (restriction E (D ∪ E) hE f : VectorL2) x = _
  rw [hl, hr]
  by_cases hx : x ∈ D
  · have he : x ∉ E := fun he => Set.disjoint_left.mp hdis hx he
    simp [Set.indicator, hx, he]
  · by_cases he : x ∈ E
    · simp [Set.indicator, hx, he]
    · simp [Set.indicator, hx, he, hf (by simp [hx, he])]

theorem joined_norm_sq (hdis : Disjoint D E) (f : DomainL2 D) (g : DomainL2 E) :
    ‖injectLeft D E f + injectRight D E g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
  change ‖(f : VectorL2) + (g : VectorL2)‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ)]
  rw [disjoint_inner D E hdis f g]
  simp

theorem split_norm_sq (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hdis : Disjoint D E) (f : DomainL2 (D ∪ E)) :
    ‖projectLeft D E hD f‖ ^ 2 + ‖projectRight D E hE f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← joined_norm_sq D E hdis, support_decomposition D E hD hE hdis]

def diagonal (hD : MeasurableSet D) (hE : MeasurableSet E)
    (A : DomainL2 D →L[ℂ] DomainL2 D) (B : DomainL2 E →L[ℂ] DomainL2 E) :
    DomainL2 (D ∪ E) →L[ℂ] DomainL2 (D ∪ E) :=
  injectLeft D E ∘L A ∘L projectLeft D E hD + injectRight D E ∘L B ∘L projectRight D E hE

def offDiagonal (hD : MeasurableSet D) (hE : MeasurableSet E)
    (C : DomainL2 E →L[ℂ] DomainL2 D) (F : DomainL2 D →L[ℂ] DomainL2 E) :
    DomainL2 (D ∪ E) →L[ℂ] DomainL2 (D ∪ E) :=
  injectLeft D E ∘L C ∘L projectRight D E hE + injectRight D E ∘L F ∘L projectLeft D E hD

theorem diagonal_norm_le (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (A : DomainL2 D →L[ℂ] DomainL2 D) (B : DomainL2 E →L[ℂ] DomainL2 E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hA : ‖A‖ ≤ ρ) (hB : ‖B‖ ≤ ρ) :
    ‖diagonal D E hD hE A B‖ ≤ ρ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hρ
  intro f
  have h1 := (A.le_opNorm (projectLeft D E hD f)).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h2 := (B.le_opNorm (projectRight D E hE f)).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hs := split_norm_sq D E hD hE hdis f
  have ho := joined_norm_sq D E hdis (A (projectLeft D E hD f)) (B (projectRight D E hE f))
  change ‖injectLeft D E (A (projectLeft D E hD f)) +
      injectRight D E (B (projectRight D E hE f))‖ ≤ ρ * ‖f‖
  have hsq1 := mul_self_le_mul_self (norm_nonneg _) h1
  have hsq2 := mul_self_le_mul_self (norm_nonneg _) h2
  have hs' := congrArg (fun r : ℝ => ρ ^ 2 * r) hs
  have hsq : ‖injectLeft D E (A (projectLeft D E hD f)) +
      injectRight D E (B (projectRight D E hE f))‖ ^ 2 ≤ (ρ * ‖f‖) ^ 2 := by
    nlinarith only [ho, hs', hsq1, hsq2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ (norm_nonneg _))).mp hsq

theorem offDiagonal_norm_le (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (C : DomainL2 E →L[ℂ] DomainL2 D) (F : DomainL2 D →L[ℂ] DomainL2 E)
    {c : ℝ} (hc : 0 ≤ c) (hC : ‖C‖ ≤ c) (hF : ‖F‖ ≤ c) :
    ‖offDiagonal D E hD hE C F‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  have h1 := (C.le_opNorm (projectRight D E hE f)).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  have h2 := (F.le_opNorm (projectLeft D E hD f)).trans
    (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
  have hs := split_norm_sq D E hD hE hdis f
  have ho := joined_norm_sq D E hdis (C (projectRight D E hE f)) (F (projectLeft D E hD f))
  change ‖injectLeft D E (C (projectRight D E hE f)) +
      injectRight D E (F (projectLeft D E hD f))‖ ≤ c * ‖f‖
  have hsq1 := mul_self_le_mul_self (norm_nonneg _) h1
  have hsq2 := mul_self_le_mul_self (norm_nonneg _) h2
  have hs' := congrArg (fun r : ℝ => c ^ 2 * r) hs
  have hsq : ‖injectLeft D E (C (projectRight D E hE f)) +
      injectRight D E (F (projectLeft D E hD f))‖ ^ 2 ≤ (c * ‖f‖) ^ 2 := by
    nlinarith only [ho, hs', hsq1, hsq2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hsq

end QuarticMaxwell.SupportBlocks

namespace QuarticMaxwell.SupportBlocks
open OQ7Prescribed MeasureTheory Set
variable (D E : Set OQ7Prescribed.Position)

theorem projectLeft_injectLeft (hD : MeasurableSet D) (f : DomainL2 D) :
    projectLeft D E hD (injectLeft D E f) = f :=
  restriction_inclusion D (D ∪ E) hD subset_union_left f

theorem projectRight_injectRight (hE : MeasurableSet E) (f : DomainL2 E) :
    projectRight D E hE (injectRight D E f) = f :=
  restriction_inclusion E (D ∪ E) hE subset_union_right f

theorem projectLeft_injectRight (hD : MeasurableSet D) (hdis : Disjoint D E) (f : DomainL2 E) :
    projectLeft D E hD (injectRight D E f) = 0 :=
  restriction_other D E hD hdis f

theorem projectRight_injectLeft (hE : MeasurableSet E) (hdis : Disjoint D E) (f : DomainL2 D) :
    projectRight D E hE (injectLeft D E f) = 0 :=
  restriction_other E D hE hdis.symm f

theorem component_ext (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    {f g : DomainL2 (D ∪ E)} (hL : projectLeft D E hD f = projectLeft D E hD g)
    (hR : projectRight D E hE f = projectRight D E hE g) : f = g := by
  rw [← support_decomposition D E hD hE hdis f, hL, hR,
    support_decomposition D E hD hE hdis g]

theorem projectLeft_diagonal (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (A : DomainL2 D →L[ℂ] DomainL2 D) (B : DomainL2 E →L[ℂ] DomainL2 E) (f : DomainL2 (D ∪ E)) :
    projectLeft D E hD (diagonal D E hD hE A B f) = A (projectLeft D E hD f) := by
  change projectLeft D E hD (injectLeft D E (A (projectLeft D E hD f)) +
    injectRight D E (B (projectRight D E hE f))) = _
  rw [map_add, projectLeft_injectLeft, projectLeft_injectRight D E hD hdis, add_zero]

theorem projectRight_diagonal (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (A : DomainL2 D →L[ℂ] DomainL2 D) (B : DomainL2 E →L[ℂ] DomainL2 E) (f : DomainL2 (D ∪ E)) :
    projectRight D E hE (diagonal D E hD hE A B f) = B (projectRight D E hE f) := by
  change projectRight D E hE (injectLeft D E (A (projectLeft D E hD f)) +
    injectRight D E (B (projectRight D E hE f))) = _
  rw [map_add, projectRight_injectLeft D E hE hdis, projectRight_injectRight, zero_add]

theorem projectLeft_offDiagonal (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (C : DomainL2 E →L[ℂ] DomainL2 D) (F : DomainL2 D →L[ℂ] DomainL2 E) (f : DomainL2 (D ∪ E)) :
    projectLeft D E hD (offDiagonal D E hD hE C F f) = C (projectRight D E hE f) := by
  change projectLeft D E hD (injectLeft D E (C (projectRight D E hE f)) +
    injectRight D E (F (projectLeft D E hD f))) = _
  rw [map_add, projectLeft_injectLeft, projectLeft_injectRight D E hD hdis, add_zero]

theorem projectRight_offDiagonal (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (C : DomainL2 E →L[ℂ] DomainL2 D) (F : DomainL2 D →L[ℂ] DomainL2 E) (f : DomainL2 (D ∪ E)) :
    projectRight D E hE (offDiagonal D E hD hE C F f) = F (projectLeft D E hD f) := by
  change projectRight D E hE (injectLeft D E (C (projectRight D E hE f)) +
    injectRight D E (F (projectLeft D E hD f))) = _
  rw [map_add, projectRight_injectLeft D E hE hdis, projectRight_injectRight, zero_add]

theorem diagonal_inverse_cancel (hD : MeasurableSet D) (hE : MeasurableSet E) (hdis : Disjoint D E)
    (J : DomainL2 D ≃L[ℂ] DomainL2 D) (K : DomainL2 E ≃L[ℂ] DomainL2 E) (f : DomainL2 (D ∪ E)) :
    diagonal D E hD hE J.symm.toContinuousLinearMap K.symm.toContinuousLinearMap
      (diagonal D E hD hE J.toContinuousLinearMap K.toContinuousLinearMap f) = f := by
  change injectLeft D E (J.symm (projectLeft D E hD
      (diagonal D E hD hE J.toContinuousLinearMap K.toContinuousLinearMap f))) +
    injectRight D E (K.symm (projectRight D E hE
      (diagonal D E hD hE J.toContinuousLinearMap K.toContinuousLinearMap f))) = f
  rw [projectLeft_diagonal D E hD hE hdis, projectRight_diagonal D E hD hE hdis]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  exact support_decomposition D E hD hE hdis f

end QuarticMaxwell.SupportBlocks
