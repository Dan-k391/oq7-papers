import PrescribedExtinction.NewtonPunctured

/-! Exact Newtonian Hessian contact identity in the existing distribution
framework. Continuity of the principal value is a consequence of the proved
identity, not an assumed property of an integral-valued functional. -/
noncomputable section
namespace OQ7Prescribed
open MeasureTheory Set Filter
open scoped Topology

theorem newton_test_puncture_removal (φ : ScalarTest) :
    Tendsto (fun r : ℝ => ∫ x in {x : Position | r < ‖x‖}, newtonReal x * φ x)
      (𝓝 (0 : ℝ)) (𝓝 (∫ x, newtonReal x * φ x)) := by
  classical
  have hf := newtonReal_test_integrable φ
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝 (0 : ℝ))
    (F := fun r => {x : Position | r < ‖x‖}.indicator (fun x => newtonReal x * φ x))
    (f := fun x => newtonReal x * φ x) (fun x => ‖newtonReal x * φ x‖)
    (Eventually.of_forall fun r => hf.aestronglyMeasurable.indicator
      (isOpen_lt continuous_const continuous_norm).measurableSet)
    (Eventually.of_forall fun _ => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
    hf.norm ?_
  · simpa only [integral_indicator (isOpen_lt continuous_const continuous_norm).measurableSet] using h
  · exact ae_of_all _ fun x => by
      by_cases hx : x = 0
      · subst x
        simp only [newtonReal, norm_zero, mul_zero, inv_zero, zero_mul, indicator_apply, ite_self]
        exact tendsto_const_nhds
      · have he : (fun r : ℝ => {x : Position | r < ‖x‖}.indicator (fun x => newtonReal x * φ x) x)
            =ᶠ[𝓝 0] fun _ => newtonReal x * φ x := by
          filter_upwards [Iio_mem_nhds (norm_pos_iff.mpr hx)] with r hr
          exact indicator_of_mem (show x ∈ {x : Position | r < ‖x‖} from hr) _
        exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem newton_contact_identity_real (φ : ScalarTest) (i j : Fin 3) :
    (∫ x, newtonReal x * (testPartial j (testPartial i φ)) x) =
      newtonPVValue φ i j - ((if i = j then 1 else 0) / 3) * φ 0 := by
  have hL := (newton_test_puncture_removal (testPartial j (testPartial i φ))).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hR := ((newtonPrincipalValue_tendsto φ i j).add
    ((newtonContactBoundary_tendsto φ i j).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))).add
    ((newtonDerivativeBoundary_tendsto φ i j).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have he : (fun r : ℝ => ∫ x in {x : Position | r < ‖x‖},
      newtonReal x * (testPartial j (testPartial i φ)) x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => newtonPVTruncated φ i j r + newtonContactBoundary φ i j r + newtonDerivativeBoundary φ i j r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact newton_punctured_double_ibp r hr φ i j
  have h := tendsto_nhds_unique hL ((tendsto_congr' he).mpr hR)
  simpa only [add_zero, neg_mul, sub_eq_add_neg] using h

theorem newton_hessian_contact_apply (φ : ScalarTest) (i j : Fin 3) :
    greenHessian 0 i j φ =
      ((newtonPVValue φ i j - ((if i = j then 1 else 0) / 3) * φ 0 : ℝ) : ℂ) := by
  rw [greenHessian_apply, outgoingGreenDistribution_apply]
  have he : (fun x : Position => (testPartial j (testPartial i φ)) x • outgoingGreen 0 x) =
      (fun x => ((newtonReal x * (testPartial j (testPartial i φ)) x : ℝ) : ℂ)) := by
    funext x
    rw [← newtonReal_eq_green]
    simp [Complex.real_smul, mul_comm]
  rw [he, integral_complex_ofReal, newton_contact_identity_real]

def newtonDirac : ScalarDistribution :=
  Distribution.mapCLM Complex.ofRealCLM (Distribution.delta (Ω := ⊤) (n := ⊤) (0 : Position))

theorem newtonDirac_apply (φ : ScalarTest) : newtonDirac φ = (φ 0 : ℂ) := rfl

def newtonPVRepresentation (i j : Fin 3) : ScalarDistribution :=
  greenHessian 0 i j + ((if i = j then 1 else 0) / 3 : ℝ) • newtonDirac

theorem newtonPVRepresentation_apply (φ : ScalarTest) (i j : Fin 3) :
    newtonPVRepresentation i j φ = (newtonPVValue φ i j : ℂ) := by
  simp only [newtonPVRepresentation, add_apply, smul_apply, newton_hessian_contact_apply,
    newtonDirac_apply, Complex.real_smul]
  push_cast
  ring

/-- The actual compensated-integral principal value, bundled as a continuous
distribution. Its linearity and continuity follow from the proved Newton
integration identity and its representation as continuous distributions. -/
def newtonPVDistribution (i j : Fin 3) : ScalarDistribution where
  toFun φ := (newtonPVValue φ i j : ℂ)
  map_add' φ ψ := by
    have h := (newtonPVRepresentation i j).map_add φ ψ
    change newtonPVRepresentation i j (φ + ψ) =
      newtonPVRepresentation i j φ + newtonPVRepresentation i j ψ at h
    simpa only [newtonPVRepresentation_apply] using h
  map_smul' r φ := by
    have h := (newtonPVRepresentation i j).map_smul r φ
    change newtonPVRepresentation i j (r • φ) = r • newtonPVRepresentation i j φ at h
    simpa only [newtonPVRepresentation_apply, RingHom.id_apply] using h
  cont := by
    have he : (fun φ : ScalarTest => (newtonPVValue φ i j : ℂ)) = newtonPVRepresentation i j := by
      funext φ
      exact (newtonPVRepresentation_apply φ i j).symm
    rw [he]
    exact (newtonPVRepresentation i j).continuous

theorem newtonPVDistribution_apply (φ : ScalarTest) (i j : Fin 3) :
    newtonPVDistribution i j φ = (newtonPVValue φ i j : ℂ) := rfl

theorem newtonPVValue_continuous (i j : Fin 3) :
    Continuous (fun φ : ScalarTest => newtonPVValue φ i j) := by
  have hc : Continuous (fun φ : ScalarTest => Complex.re (newtonPVDistribution i j φ)) :=
    Complex.continuous_re.comp (newtonPVDistribution i j).continuous
  simpa only [newtonPVDistribution_apply, Complex.ofReal_re] using hc

theorem newton_hessian_contact_distribution (i j : Fin 3) :
    greenHessian 0 i j =
      newtonPVDistribution i j - ((if i = j then 1 else 0) / 3 : ℝ) • newtonDirac := by
  ext φ
  simp only [sub_apply, smul_apply, newtonPVDistribution_apply, newtonDirac_apply,
    newton_hessian_contact_apply, Complex.real_smul]
  push_cast
  ring

end OQ7Prescribed
