import PrescribedExtinction.SetSupportedL2

noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set
open scoped Classical

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

def supportedConstLinear (μ : Measure α) (s : Set α) (A : E →L[ℂ] E) :
    SetSupportedL2 (E := E) μ s →ₗ[ℂ] SetSupportedL2 (E := E) μ s where
  toFun f := ⟨A.compLp (f : Lp E 2 μ), by
    change ∀ᵐ x ∂μ, x ∉ s → (A.compLp (f : Lp E 2 μ)) x = 0
    filter_upwards [A.coeFn_compLp (f : Lp E 2 μ), f.property] with x hx hf
    intro hxs
    rw [hx, hf hxs, map_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (A.compLpL 2 μ) (f : Lp E 2 μ) (g : Lp E 2 μ)
  map_smul' z f := by
    apply Subtype.ext
    exact map_smul (A.compLpL 2 μ) z (f : Lp E 2 μ)

def supportedConstCLM (μ : Measure α) (s : Set α) (A : E →L[ℂ] E) :
    SetSupportedL2 (E := E) μ s →L[ℂ] SetSupportedL2 (E := E) μ s :=
  (supportedConstLinear μ s A).mkContinuous ‖A‖ fun f =>
    A.norm_compLp_le (f : Lp E 2 μ)

theorem supportedConstCLM_coe (μ : Measure α) (s : Set α) (A : E →L[ℂ] E)
    (f : SetSupportedL2 (E := E) μ s) :
    (supportedConstCLM μ s A f : Lp E 2 μ) =ᵐ[μ] fun x => A ((f : Lp E 2 μ) x) :=
  A.coeFn_compLp (f : Lp E 2 μ)

def supportedSliceLinear (μ : Measure α) (s t : Set α) (ht : MeasurableSet t) :
    SetSupportedL2 (E := E) μ s →ₗ[ℂ] SetSupportedL2 (E := E) μ s where
  toFun f := ⟨indicatorL2 μ t ht (f : Lp E 2 μ), by
    change ∀ᵐ x ∂μ, x ∉ s → (indicatorL2 μ t ht (f : Lp E 2 μ)) x = 0
    filter_upwards [indicatorL2_coe μ t ht (f : Lp E 2 μ), f.property] with x hx hf
    intro hxs
    rw [hx]
    by_cases hxt : x ∈ t
    · rw [indicator_of_mem hxt, hf hxs]
    · rw [indicator_of_notMem hxt]⟩
  map_add' f g := Subtype.ext (indicatorL2_add μ t ht (f : Lp E 2 μ) (g : Lp E 2 μ))
  map_smul' z f := Subtype.ext (indicatorL2_smul μ t ht z (f : Lp E 2 μ))

def supportedSliceCLM (μ : Measure α) (s t : Set α) (ht : MeasurableSet t) :
    SetSupportedL2 (E := E) μ s →L[ℂ] SetSupportedL2 (E := E) μ s :=
  (supportedSliceLinear (E := E) μ s t ht).mkContinuous 1 fun f => by
    change ‖indicatorL2 μ t ht (f : Lp E 2 μ)‖ ≤ 1 * ‖(f : Lp E 2 μ)‖
    simpa using indicatorL2_norm_le μ t ht (f : Lp E 2 μ)

theorem supportedSliceCLM_coe (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (f : SetSupportedL2 (E := E) μ s) :
    (supportedSliceCLM μ s t ht f : Lp E 2 μ) =ᵐ[μ] t.indicator (fun x => (f : Lp E 2 μ) x) :=
  indicatorL2_coe μ t ht (f : Lp E 2 μ)

def twoPieceSupportedOperator (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (A B : E →L[ℂ] E) : SetSupportedL2 (E := E) μ s →L[ℂ] SetSupportedL2 (E := E) μ s :=
  supportedConstCLM μ s A ∘L supportedSliceCLM μ s t ht +
    supportedConstCLM μ s B ∘L
      (ContinuousLinearMap.id ℂ (SetSupportedL2 (E := E) μ s) - supportedSliceCLM μ s t ht)

theorem twoPieceSupportedOperator_coe (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (A B : E →L[ℂ] E) (f : SetSupportedL2 (E := E) μ s) :
    (twoPieceSupportedOperator μ s t ht A B f : Lp E 2 μ) =ᵐ[μ]
      fun x => if x ∈ t then A ((f : Lp E 2 μ) x) else B ((f : Lp E 2 μ) x) := by
  classical
  let g := supportedSliceCLM μ s t ht f
  have hgs := supportedSliceCLM_coe μ s t ht f
  have has := supportedConstCLM_coe μ s A g
  have hbs := supportedConstCLM_coe μ s B (f - g)
  filter_upwards [hgs, has, hbs, Lp.coeFn_sub (f : Lp E 2 μ) (g : Lp E 2 μ),
    Lp.coeFn_add (supportedConstCLM μ s A g : Lp E 2 μ)
      (supportedConstCLM μ s B (f - g) : Lp E 2 μ)] with x hg ha hb hsub hadd
  change ((supportedConstCLM μ s A g : Lp E 2 μ) +
    (supportedConstCLM μ s B (f - g) : Lp E 2 μ)) x = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [ha, hb]
  change A ((g : Lp E 2 μ) x) + B (((f : Lp E 2 μ) - (g : Lp E 2 μ)) x) = _
  rw [hsub]
  change A ((g : Lp E 2 μ) x) + B ((f : Lp E 2 μ) x - (g : Lp E 2 μ) x) = _
  rw [hg]
  by_cases hx : x ∈ t
  · simp [hx]
  · simp [hx]

theorem twoPieceSupportedOperator_negative_imaginary_bound
    (μ : Measure α) (s t : Set α) (ht : MeasurableSet t)
    (A B : E →L[ℂ] E) (c : ℝ)
    (hA : ∀ v : E, c * ‖v‖ ^ 2 ≤ -(inner ℂ v (A v)).im)
    (hB : ∀ v : E, c * ‖v‖ ^ 2 ≤ -(inner ℂ v (B v)).im)
    (f : SetSupportedL2 (E := E) μ s) :
    c * ‖f‖ ^ 2 ≤ -(inner ℂ f (twoPieceSupportedOperator μ s t ht A B f)).im := by
  let J := twoPieceSupportedOperator μ s t ht A B
  have hi := L2.integrable_inner (𝕜 := ℂ) (f : Lp E 2 μ) (J f : Lp E 2 μ)
  have hii := L2.integrable_inner (𝕜 := ℂ) (f : Lp E 2 μ) (f : Lp E 2 μ)
  have hself (x : α) : (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re = ‖(f : Lp E 2 μ) x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hs : ∫ x : α, ‖(f : Lp E 2 μ) x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
    have hn : ∫ x : α, (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re ∂μ = ‖f‖ ^ 2 := by
      have hre : (∫ x : α, inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x) ∂μ).re =
          ∫ x : α, (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re ∂μ :=
        (Complex.reCLM.integral_comp_comm hii).symm
      rw [← hre]
      change (inner ℂ (f : Lp E 2 μ) (f : Lp E 2 μ)).re = _
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (f : Lp E 2 μ)
    simpa only [hself] using hn
  have hnorm : Integrable (fun x : α => ‖(f : Lp E 2 μ) x‖ ^ 2) μ := by
    have hn := hii.re
    change Integrable (fun x : α => (inner ℂ ((f : Lp E 2 μ) x) ((f : Lp E 2 μ) x)).re) μ at hn
    simpa only [hself] using hn
  have hm : c * ‖f‖ ^ 2 ≤ ∫ x : α, -(inner ℂ ((f : Lp E 2 μ) x) ((J f : Lp E 2 μ) x)).im ∂μ := by
    rw [← hs, ← integral_const_mul]
    apply integral_mono_ae (hnorm.const_mul c) hi.im.neg
    filter_upwards [twoPieceSupportedOperator_coe μ s t ht A B f] with x hx
    change c * ‖(f : Lp E 2 μ) x‖ ^ 2 ≤ -(inner ℂ ((f : Lp E 2 μ) x) ((J f : Lp E 2 μ) x)).im
    rw [hx]
    split_ifs
    · exact hA _
    · exact hB _
  have him : (∫ x : α, inner ℂ ((f : Lp E 2 μ) x) ((J f : Lp E 2 μ) x) ∂μ).im =
      ∫ x : α, (inner ℂ ((f : Lp E 2 μ) x) ((J f : Lp E 2 μ) x)).im ∂μ :=
    (Complex.imCLM.integral_comp_comm hi).symm
  rw [integral_neg, ← him] at hm
  exact hm

end OQ7Prescribed
