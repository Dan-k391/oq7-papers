import PrescribedExtinction.PhysicalPolarization
import PrescribedExtinction.IncidentMaxwell

/-! Conversion of a solution of the actual material volume equation into
the original physical scattering state. The volume equation is an explicit
hypothesis of this conversion; its solvability is not asserted here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OQ7Prescribed
open MeasureTheory

theorem compactField_bilinear_integrable (F : Field) (hF : LocallyIntegrable F volume)
    (ψ : Field) (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x : Position => bilinear (F x) (ψ x)) volume := by
  have h (i : Fin 3) : Integrable (fun x : Position => F x i * ψ x i) volume := by
    have h' := compactTest_component_integrable F hF i (fun x => ψ x i)
      ((vectorCoordinate i).continuous.comp hψ) (hs.comp_left (vectorCoordinate i).map_zero)
    simpa only [mul_comm] using h'
  exact integrable_finsetSum Finset.univ fun i _ => h i

theorem compactField_curl_hasCompactSupport (φ : Field) (hs : HasCompactSupport φ) :
    HasCompactSupport (curl φ) := by
  apply (hs.fderiv ℝ).mono
  intro x hx
  by_contra hh
  have hz : fderiv ℝ φ x = 0 := not_not.mp hh
  exact hx (by simp [curl, hz])

theorem bilinear_add_left (u v w : Vector) : bilinear (u + v) w = bilinear u w + bilinear v w := by
  simp [bilinear, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem HasWeakCurl.add_fields {F1 F2 G1 G2 : Field}
    (h1 : HasWeakCurl F1 G1) (h2 : HasWeakCurl F2 G2)
    (hF1 : LocallyIntegrable F1 volume) (hF2 : LocallyIntegrable F2 volume)
    (hG1 : LocallyIntegrable G1 volume) (hG2 : LocallyIntegrable G2 volume) :
    HasWeakCurl (fun x => F1 x + F2 x) (fun x => G1 x + G2 x) := by
  intro φ hφ hsφ
  have hf1 := compactField_bilinear_integrable F1 hF1 (curl φ)
    (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hf2 := compactField_bilinear_integrable F2 hF2 (curl φ)
    (smoothField_curl_continuous φ hφ) (compactField_curl_hasCompactSupport φ hsφ)
  have hg1 := compactField_bilinear_integrable G1 hG1 φ hφ.continuous hsφ
  have hg2 := compactField_bilinear_integrable G2 hG2 φ hφ.continuous hsφ
  simp_rw [bilinear_add_left]
  rw [integral_add hf1 hf2, integral_add hg1 hg2, h1 φ hφ hsφ, h2 φ hφ hsφ]

def volumeTotalElectric (k : ℝ) (σ : Direction) (p : CompactPolarization) : Field :=
  fun x => incidentElectric k σ x + outgoingElectricField k p x

def volumeTotalMagnetic (k : ℝ) (σ : Direction) (p : CompactPolarization) : Field :=
  fun x => incidentMagnetic k σ x + outgoingMagneticField k p x

def MaterialVolumeEquation (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) : Prop :=
  p.current =ᵐ[volume] polarization B (volumeTotalElectric k σ p)

theorem electric_add_polarization (B : TwoLayerBody) (E : Field) (x : Position) :
    E x + polarization B E x = tensorApply (B.permittivity x) (E x) := by
  ext i
  simp [polarization, TwoLayerBody.susceptibility, tensorApply, Matrix.sub_mulVec, PiLp.add_apply]

theorem volumeTotalElectric_locallySquareIntegrable (k : ℝ) (σ : Direction)
    (p : CompactPolarization) : LocallySquareIntegrable (volumeTotalElectric k σ p) := by
  intro K hK
  exact (incidentElectric_locallySquareIntegrable k σ K hK).add
    (outgoingElectricField_locallySquareIntegrable k p K hK)

theorem volumeTotalMagnetic_locallySquareIntegrable (k : ℝ) (σ : Direction)
    (p : CompactPolarization) : LocallySquareIntegrable (volumeTotalMagnetic k σ p) := by
  intro K hK
  exact (incidentMagnetic_locallySquareIntegrable k σ K hK).add
    (outgoingMagneticField_locallySquareIntegrable k p K hK)

theorem volumeTotalFields_weakMaxwell (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hvol : MaterialVolumeEquation k B σ p) :
    WeakMaxwell k B (volumeTotalElectric k σ p) (volumeTotalMagnetic k σ p) := by
  have hei := locallySquareIntegrable_locallyIntegrable _ (incidentElectric_locallySquareIntegrable k σ)
  have hhi := locallySquareIntegrable_locallyIntegrable _ (incidentMagnetic_locallySquareIntegrable k σ)
  have hes := locallySquareIntegrable_locallyIntegrable _ (outgoingElectricField_locallySquareIntegrable k p)
  have hhs := locallySquareIntegrable_locallyIntegrable _ (outgoingMagneticField_locallySquareIntegrable k p)
  have hp := (compactPolarization_current_integrable p).locallyIntegrable
  have hfirst := (incidentElectric_first_weakCurl k σ).add_fields (outgoingSourceFields_first_weakCurl k p)
    hei hes (hhi.smul (Complex.I * (k : ℂ))) (hhs.smul (Complex.I * (k : ℂ)))
  have hsecond := (incidentMagnetic_second_weakCurl k σ).add_fields (outgoingSourceFields_second_weakCurl k p)
    hhi hhs (hei.smul (-Complex.I * (k : ℂ))) ((hes.add hp).smul (-Complex.I * (k : ℂ)))
  refine ⟨volumeTotalElectric_locallySquareIntegrable k σ p,
    volumeTotalMagnetic_locallySquareIntegrable k σ p, ?_, ?_⟩
  · convert hfirst using 1 <;> funext x <;>
      simp [volumeTotalElectric, volumeTotalMagnetic, smul_add]
  · apply hsecond.congr_ae (ae_of_all _ fun _ => rfl)
    filter_upwards [hvol] with x hx
    rw [← smul_add, hx, ← add_assoc]
    change (-Complex.I * (k : ℂ)) •
      (volumeTotalElectric k σ p x + polarization B (volumeTotalElectric k σ p) x) =
        (-Complex.I * (k : ℂ)) • tensorApply (B.permittivity x) (volumeTotalElectric k σ p x)
    rw [electric_add_polarization]

/-- A proved constructor from the original physical material volume equation.
There is no assumption of Maxwell equations, radiation, optical identities,
or power data. Existence of a volume-equation solution remains to be proved. -/
def scatteringStateOfVolumeEquation (k : ℝ) (B : TwoLayerBody) (σ : Direction)
    (p : CompactPolarization) (hvol : MaterialVolumeEquation k B σ p) : ScatteringState k B σ where
  electric := volumeTotalElectric k σ p
  magnetic := volumeTotalMagnetic k σ p
  maxwell := volumeTotalFields_weakMaxwell k B σ p hvol
  outgoing := by
    convert outgoingSourceFields_outgoing k p using 1 <;> funext x <;>
      simp [volumeTotalElectric, volumeTotalMagnetic]
  current_memLp := physicalPolarization_memLp B _ (volumeTotalElectric_locallySquareIntegrable k σ p)

end OQ7Prescribed
