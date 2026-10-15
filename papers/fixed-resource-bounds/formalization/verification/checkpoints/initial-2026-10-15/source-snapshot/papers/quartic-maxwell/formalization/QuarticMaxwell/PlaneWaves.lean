import QuarticMaxwell.IncidentSources
import PrescribedExtinction.IncidentMaxwell
import PrescribedExtinction.FarFieldKernel

/-! The literal incident sources satisfy vacuum Maxwell for every real
unit propagation direction and transverse (possibly complex) polarization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuarticMaxwell
open MeasureTheory OQ7Prescribed

theorem radiationPhase_contDiff (k : ℝ) (n : UnitSphere) :
    ContDiff ℝ (⊤ : ℕ∞) (radiationPhase k n) := by
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun x : Position => inner ℝ (n : Position) x) :=
    (innerSL ℝ (n : Position)).contDiff
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hi))).cexp

theorem radiationPhase_hasFDerivAt (k : ℝ) (n : UnitSphere) (x : Position) :
    HasFDerivAt (radiationPhase k n)
      ((-Complex.I * (k : ℂ) * radiationPhase k n x) •
        (Complex.ofRealCLM.comp (innerSL ℝ (n : Position)))) x := by
  have h := (Complex.ofRealCLM.comp (innerSL ℝ (n : Position))).hasFDerivAt (x := x)
  have he := (h.const_mul (-Complex.I * (k : ℂ))).cexp
  convert he using 1
  · funext y
    simp [radiationPhase, mul_assoc]
  · ext y
    simp [radiationPhase, mul_assoc]
    ring

theorem realInner_basis (n : Position) (j : Fin 3) : inner ℝ n (basisR j) = n j := by
  fin_cases j <;> simp [basisR, PiLp.inner_apply, RCLike.inner_apply]

theorem radiationPhase_basis_derivative (k : ℝ) (n : UnitSphere) (x : Position) (j : Fin 3) :
    fderiv ℝ (radiationPhase k n) x (basisR j) =
      -Complex.I * (k : ℂ) * radiationPhase k n x * ((n : Position) j : ℂ) := by
  rw [(radiationPhase_hasFDerivAt k n x).fderiv]
  simp [realInner_basis, smul_eq_mul]

theorem phase_vector_curl (k : ℝ) (n : UnitSphere) (e : Vector) (x : Position) :
    curl (fun y => radiationPhase k n y • e) x =
      (-Complex.I * (k : ℂ) * radiationPhase k n x) • cross (complexify (n : Position)) e := by
  have h := (radiationPhase_hasFDerivAt k n x).smul_const e
  ext i
  fin_cases i <;> simp [curl, h.fderiv, realInner_basis, cross, complexify,
    PiLp.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul] <;> ring

def incidentMagneticWave (k : ℝ) (n : UnitSphere) (e : Vector) (x : Position) : Vector :=
  radiationPhase k n x • (-cross (complexify (n : Position)) e)

theorem incidentWave_contDiff (k : ℝ) (n : UnitSphere) (e : Vector) :
    ContDiff ℝ (⊤ : ℕ∞) (incidentWave k n e) :=
  (radiationPhase_contDiff k n).smul contDiff_const

theorem incidentMagneticWave_contDiff (k : ℝ) (n : UnitSphere) (e : Vector) :
    ContDiff ℝ (⊤ : ℕ∞) (incidentMagneticWave k n e) :=
  (radiationPhase_contDiff k n).smul contDiff_const

theorem incidentWave_first_curl (k : ℝ) (n : UnitSphere) (e : Vector) (x : Position) :
    curl (incidentWave k n e) x = (Complex.I * (k : ℂ)) • incidentMagneticWave k n e x := by
  change curl (fun y => radiationPhase k n y • e) x = _
  rw [phase_vector_curl]
  simp [incidentMagneticWave, smul_smul, mul_assoc]

theorem incidentMagneticWave_second_curl (k : ℝ) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) (x : Position) :
    curl (incidentMagneticWave k n e) x = (-Complex.I * (k : ℂ)) • incidentWave k n e x := by
  have hn : ‖(n : Position)‖ = 1 := (mem_sphere_zero_iff_norm).mp n.property
  have hc : cross (complexify (n : Position)) (cross (complexify (n : Position)) e) = -e := by
    have ha (a b : Vector) : cross a b = -cross b a := by
      ext i
      fin_cases i <;> simp [cross, PiLp.neg_apply] <;> ring
    have hb : bilinear e (complexify (n : Position)) = 0 := by
      simpa only [bilinear, mul_comm] using he
    rw [ha (complexify (n : Position)), cross_cross, hb, bilinear_complexify_self, hn]
    simp
  change curl (fun y => radiationPhase k n y • (-cross (complexify (n : Position)) e)) x = _
  rw [phase_vector_curl]
  have hneg : cross (complexify (n : Position)) (-cross (complexify (n : Position)) e) = e := by
    have ha (a b : Vector) : cross a (-b) = -cross a b := by
      ext i
      fin_cases i <;> simp [cross, PiLp.neg_apply] <;> ring
    rw [ha, hc, neg_neg]
  rw [hneg]
  simp [incidentWave, smul_smul, mul_assoc]

theorem incidentWave_first_weakCurl (k : ℝ) (n : UnitSphere) (e : Vector) :
    HasWeakCurl (incidentWave k n e)
      (fun x => (Complex.I * (k : ℂ)) • incidentMagneticWave k n e x) := by
  convert smoothField_hasWeakCurl _ (incidentWave_contDiff k n e) using 1
  exact (funext (incidentWave_first_curl k n e)).symm

theorem incidentMagneticWave_second_weakCurl (k : ℝ) (n : UnitSphere) (e : Vector)
    (he : bilinear (complexify (n : Position)) e = 0) :
    HasWeakCurl (incidentMagneticWave k n e)
      (fun x => (-Complex.I * (k : ℂ)) • incidentWave k n e x) := by
  convert smoothField_hasWeakCurl _ (incidentMagneticWave_contDiff k n e) using 1
  exact (funext (incidentMagneticWave_second_curl k n e he)).symm

theorem real_transverse {n : UnitSphere} {v : Position} (hv : inner ℝ (n : Position) v = 0) :
    bilinear (complexify (n : Position)) (complexify v) = 0 := by
  have hr : (∑ i : Fin 3, (n : Position) i * v i) = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hv
  change (∑ i : Fin 3, ((n : Position) i : ℂ) * (v i : ℂ)) = 0
  exact_mod_cast hr

theorem incidentWave_locallySquareIntegrable (k : ℝ) (n : UnitSphere) (e : Vector) :
    LocallySquareIntegrable (incidentWave k n e) := by
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply MemLp.of_bound ((incidentWave_contDiff k n e).continuous.aestronglyMeasurable.restrict) ‖e‖
  exact ae_of_all _ fun x => (incidentWave_norm k n e x).le

theorem incidentMagneticWave_locallySquareIntegrable (k : ℝ) (n : UnitSphere) (e : Vector) :
    LocallySquareIntegrable (incidentMagneticWave k n e) := by
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply MemLp.of_bound ((incidentMagneticWave_contDiff k n e).continuous.aestronglyMeasurable.restrict)
    ‖cross (complexify (n : Position)) e‖
  exact ae_of_all _ fun x => by simp [incidentMagneticWave, norm_smul, radiationPhase_norm]

end QuarticMaxwell
