import PrescribedExtinction.Theorem11
import PrescribedExtinction.TestRegularity
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Analytic.Uniqueness

/-! Independent audit experiments (written by the auditor, not from the repo).
Compiled against the from-source build of commit 5a8350d. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open OQ7Prescribed

noncomputable section

/-! ## E0. Exact final declaration, statement, and axioms -/
set_option pp.fullNames true in
#check @OQ7Prescribed.theorem11
#print axioms OQ7Prescribed.theorem11
example : OQ7Prescribed.Theorem11Statement := OQ7Prescribed.theorem11

/-! ## E1. The two `⊤`s: `ContDiff ℝ ⊤` (old) is analytic (ω); `ContDiff ℝ (⊤ : ℕ∞)` (new) is C^∞. -/
example : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ (⊤ : WithTop ℕ∞) := by simp
example : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl

/-! ## E2. The pre-correction weak-curl condition was vacuous.
An analytic, compactly supported field on ℝ³ is identically zero, so the old test class is {0}
and `AnalyticTestWeakCurl F G` holds for *every* pair of fields. -/
theorem auditor_analytic_compactSupport_eq_zero (φ : Field)
    (h : ContDiff ℝ ⊤ φ) (hs : HasCompactSupport φ) : φ = 0 := by
  have han : AnalyticOnNhd ℝ φ univ := h.analyticOnNhd
  obtain ⟨z, hz⟩ : ∃ z : Position, z ∉ tsupport φ := by
    by_contra hcon
    push Not at hcon
    have huniv : tsupport φ = univ := eq_univ_of_forall hcon
    have hc : IsCompact (univ : Set Position) := huniv ▸ hs
    exact noncompact_univ Position hc
  have hz' : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  funext x
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) hz'
    (mem_univ x)

theorem auditor_old_weakCurl_vacuous (F G : Field) : AnalyticTestWeakCurl F G := by
  intro φ hφ hs
  have h0 := auditor_analytic_compactSupport_eq_zero φ hφ hs
  subst h0
  have hc : curl (0 : Field) = 0 := by
    funext x; ext i; fin_cases i <;> simp [curl]
  simp [hc, bilinear]

/-! ## E3. The corrected condition has content: `curl 0 = e_x` is rejected.
Test with a smooth bump times e_x. -/
theorem auditor_new_weakCurl_nonvacuous :
    ¬ HasWeakCurl (fun _ => 0) (fun _ => basisC 0) := by
  intro h
  let b : ContDiffBump (0 : Position) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : ℝ →L[ℝ] Vector := (ContinuousLinearMap.lsmul ℝ ℝ).flip (basisC 0) |>.restrictScalars ℝ
  -- explicit ℝ-linear embedding r ↦ r • e_x
  let φ : Field := fun x => ((b x : ℝ) : ℂ) • basisC 0
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x => (b x : ℝ)) := b.contDiff
    have hl : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => ((r : ℂ)) • basisC 0) := by
      have : (fun r : ℝ => ((r : ℂ)) • basisC 0) = fun r : ℝ => r • basisC 0 := by
        funext r; rw [Complex.coe_smul]
      rw [this]
      exact contDiff_id.smul contDiff_const
    exact hl.comp hb
  have hs : HasCompactSupport φ := by
    have : φ = (fun r : ℝ => ((r : ℂ)) • basisC 0) ∘ (fun x => b x) := rfl
    rw [this]
    exact b.hasCompactSupport.comp_left (by simp)
  have he := h φ hφ hs
  have hl : (∫ x : Position, bilinear ((fun _ => (0 : Vector)) x) (curl φ x)) = 0 := by
    simp [bilinear]
  have hr : (∫ x : Position, bilinear ((fun _ => basisC 0) x) (φ x)) =
      ((∫ x : Position, b x : ℝ) : ℂ) := by
    have : (fun x : Position => bilinear (basisC 0) (φ x)) = fun x => ((b x : ℝ) : ℂ) := by
      funext x
      simp [bilinear, φ, basisC, Fin.sum_univ_succ, Pi.single_apply]
    simp only [this]
    exact integral_ofReal
  rw [hl, hr] at he
  have hpos : 0 < ∫ x : Position, b x := b.integral_pos
  have : (∫ x : Position, b x) = 0 := by exact_mod_cast he.symm
  linarith

/-! ## E4. Default-zero integrals cannot be exploited in the final statement.
(a) A positive extinction forces integrability of the extinction integrand. -/
theorem auditor_extinction_pos_integrable (k : ℝ) (B : TwoLayerBody) (σ : Direction) (E : Field)
    (hX : 0 < extinction k B σ E) :
    IntegrableOn (fun x => pairing (incidentElectric k σ x) (polarization B E x)) B.domain := by
  by_contra hni
  have h0 : (∫ x in B.domain, pairing (incidentElectric k σ x) (polarization B E x)) = 0 :=
    integral_undef hni
  simp [extinction, h0] at hX

/-! (b) For EVERY ScatteringState, the absorption integrand is integrable on the body
(so `absorption` is never a default-zero Bochner integral). -/
theorem auditor_pairing_eq_inner (u v : Vector) : pairing u v = inner ℂ u v := by
  simp [pairing, PiLp.inner_apply, mul_comm]

theorem auditor_absorption_integrand (B : TwoLayerBody) (E : Field) (x : Position) :
    (quadratic (B.permittivity x) (E x)).im = (pairing (E x) (polarization B E x)).im := by
  have hsplit : tensorApply (B.permittivity x) (E x) = E x + polarization B E x := by
    ext i
    simp [tensorApply, polarization, TwoLayerBody.susceptibility, Matrix.sub_mulVec]
  have hlin : pairing (E x) (E x + polarization B E x) =
      pairing (E x) (E x) + pairing (E x) (polarization B E x) := by
    simp [pairing, mul_add, Finset.sum_add_distrib]
  rw [quadratic, hsplit, hlin, Complex.add_im, pairing_self]
  simp

theorem auditor_absorption_integrable (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (s : ScatteringState k B σ) :
    IntegrableOn (fun x => (quadratic (B.permittivity x) (s.electric x)).im) B.domain := by
  have hE : MemLp s.electric 2 (volume.restrict B.domain) :=
    (s.maxwell.1 (closure B.domain) (domain_compact_closure B)).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hP : MemLp (polarization B s.electric) 2 (volume.restrict B.domain) :=
    s.current_memLp.restrict B.domain
  have hi : Integrable (fun x => inner ℂ (hE.toLp s.electric x)
      (hP.toLp (polarization B s.electric) x)) (volume.restrict B.domain) :=
    L2.integrable_inner (hE.toLp s.electric) (hP.toLp _)
  have hi' : Integrable (fun x => pairing (s.electric x) (polarization B s.electric x))
      (volume.restrict B.domain) := by
    refine hi.congr ?_
    filter_upwards [hE.coeFn_toLp, hP.coeFn_toLp] with x h1 h2
    rw [h1, h2, auditor_pairing_eq_inner]
  have := hi'.im
  refine this.congr (Eventually.of_forall fun x => ?_)
  exact (auditor_absorption_integrand B s.electric x).symm

/-! ## E5. Weak-curl integrands are genuinely integrable for every ScatteringState and every
smooth compactly supported test, so the Maxwell equations are never `0 = 0` by default. -/
theorem auditor_bilinear_integrable (F ψ : Field) (hF : LocallySquareIntegrable F)
    (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x => bilinear (F x) (ψ x)) := by
  set K := tsupport ψ
  have hK : IsCompact K := hs
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hF1 : Integrable F (volume.restrict K) := (hF K hK).integrable one_le_two
  have hon : IntegrableOn (fun x => bilinear (F x) (ψ x)) K := by
    unfold IntegrableOn bilinear
    refine integrable_finsetSum _ fun i _ => ?_
    have hFi : Integrable (fun x => F x i) (volume.restrict K) :=
      (EuclideanSpace.proj i : Vector →L[ℂ] ℂ).integrable_comp hF1
    obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hs
    exact hFi.mul_bdd ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _) |>.comp hψ
      |>.aestronglyMeasurable) (Eventually.of_forall fun x => (PiLp.norm_apply_le (ψ x) i).trans (hC x))
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro x hx
  by_contra hxK
  have : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxK
  simp [bilinear, this] at hx

theorem auditor_curl_continuous_compact (φ : Field) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : HasCompactSupport φ) : Continuous (curl φ) ∧ HasCompactSupport (curl φ) := by
  have hd : Continuous (fderiv ℝ φ) :=
    ContDiff.continuous_fderiv (𝕜 := ℝ) hφ (by simp)
  let c : (Position →L[ℝ] Vector) → Vector := fun L => WithLp.toLp 2
    ![L (basisR 1) 2 - L (basisR 2) 1, L (basisR 2) 0 - L (basisR 0) 2,
      L (basisR 0) 1 - L (basisR 1) 0]
  have hcurl : curl φ = c ∘ fderiv ℝ φ := rfl
  rw [hcurl]
  refine ⟨?_, (hs.fderiv (𝕜 := ℝ)).comp_left (by ext i; fin_cases i <;> simp [c])⟩
  refine Continuous.comp ?_ hd
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  have hev (v : Position) (j : Fin 3) : Continuous fun L : Position →L[ℝ] Vector => L v j :=
    ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)).comp (continuous_id.clm_apply continuous_const)
  fin_cases i <;> simp [Matrix.cons_val] <;> exact (hev _ _).sub (hev _ _)

theorem auditor_weakMaxwell_integrands (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (s : ScatteringState k B σ) (φ : Field) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : HasCompactSupport φ) :
    Integrable (fun x => bilinear (s.electric x) (curl φ x)) ∧
    Integrable (fun x => bilinear ((Complex.I * (k : ℂ)) • s.magnetic x) (φ x)) ∧
    Integrable (fun x => bilinear (s.magnetic x) (curl φ x)) ∧
    Integrable (fun x => bilinear ((-Complex.I * (k : ℂ)) •
      tensorApply (B.permittivity x) (s.electric x)) (φ x)) := by
  obtain ⟨hc, hcs⟩ := auditor_curl_continuous_compact φ hφ hs
  have hφc : Continuous φ := hφ.continuous
  have hE := s.maxwell.1
  have hH := s.maxwell.2.1
  have hsm (c : ℂ) (F : Field) (hF : LocallySquareIntegrable F) :
      LocallySquareIntegrable (fun x => c • F x) := fun K hK => (hF K hK).const_smul c
  have hD : LocallySquareIntegrable (fun x => tensorApply (B.permittivity x) (s.electric x)) := by
    intro K hK
    have : (fun x => tensorApply (B.permittivity x) (s.electric x)) =
        fun x => s.electric x + polarization B s.electric x := by
      funext x; ext i
      simp [tensorApply, polarization, TwoLayerBody.susceptibility, Matrix.sub_mulVec]
    rw [this]
    exact (hE K hK).add (s.current_memLp.restrict K)
  exact ⟨auditor_bilinear_integrable _ _ hE hc hcs,
    auditor_bilinear_integrable _ _ (hsm _ _ hH) hφc hs,
    auditor_bilinear_integrable _ _ hH hc hcs,
    auditor_bilinear_integrable _ _ (hsm _ _ hD) hφc hs⟩

/-! ## E7. Under the PRE-correction definitions, the plain incident field (no scattering at all)
is a "scattering state" for every body: the old target imposed no Maxwell equation. -/
structure AuditorOldScatteringState (k : ℝ) (B : TwoLayerBody) (σ : Direction) where
  electric : Field
  magnetic : Field
  maxwell : LocallySquareIntegrable electric ∧ LocallySquareIntegrable magnetic ∧
    AnalyticTestWeakCurl electric (fun x => (Complex.I * (k : ℂ)) • magnetic x) ∧
    AnalyticTestWeakCurl magnetic (fun x => (-Complex.I * (k : ℂ)) •
      tensorApply (B.permittivity x) (electric x))
  outgoing : Outgoing (fun x => electric x - incidentElectric k σ x)
    (fun x => magnetic x - incidentMagnetic k σ x)
  current_memLp : MemLp (polarization B electric) 2 volume

def auditorOldIncidentState (k : ℝ) (B : TwoLayerBody) (σ : Direction) :
    AuditorOldScatteringState k B σ where
  electric := incidentElectric k σ
  magnetic := incidentMagnetic k σ
  maxwell := ⟨incidentElectric_locallySquareIntegrable k σ,
    incidentMagnetic_locallySquareIntegrable k σ,
    auditor_old_weakCurl_vacuous _ _, auditor_old_weakCurl_vacuous _ _⟩
  outgoing := fun ε hε => ⟨1, one_pos, fun x _ => by
    have h0 : (WithLp.toLp 2 ![(0 : ℂ), 0, 0] : Vector) = 0 := by
      ext i; fin_cases i <;> rfl
    simpa [cross, h0] using hε⟩
  current_memLp := physicalPolarization_memLp B _ (incidentElectric_locallySquareIntegrable k σ)

#print axioms auditor_old_weakCurl_vacuous
#print axioms auditor_new_weakCurl_nonvacuous
#print axioms auditor_absorption_integrable
#print axioms auditor_weakMaxwell_integrands
#print axioms auditorOldIncidentState

end
