import GeneralizedResearch.BeamSuperposition

/-! Classical Maxwell equations for genuine compact angular-spectrum
superpositions of the actual material matrix-exponential plane fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
namespace GeneralizedResearch.SuperposedMaxwell
open MeasureTheory Set BeamPackets BeamSuperposition
open ObliqueMaxwell FourierMaxwell
open scoped Matrix Matrix.Norms.Operator Topology
abbrev Transverse := BeamAveraging.Transverse
abbrev Spatial := ℝ×ℝ×ℝ
abbrev Parameter := Spatial×Transverse

def fiberState (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ) (p:Parameter) : Channel→ℂ :=
  state k (WithLp.ofLp p.2) R Q (u p.2) p.1.2.2
def derivativeState (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ) (p:Parameter) : Channel→ℂ :=
  generator k (WithLp.ofLp p.2) R Q*ᵥfiberState k R Q u p
def electricPlane (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ) (p:Parameter) : Vec3 :=
  phase (WithLp.ofLp p.2) p.1.1 p.1.2.1 • electric k (WithLp.ofLp p.2) (fiberState k R Q u p)
def magneticPlane (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ) (p:Parameter) : Vec3 :=
  phase (WithLp.ofLp p.2) p.1.1 p.1.2.1 • magnetic k (WithLp.ofLp p.2) (fiberState k R Q u p)
def electricPartial (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ) (j:Fin 3) (p:Parameter) : Vec3 :=
  if j=0 then (Complex.I*(WithLp.ofLp p.2 0:ℂ)) • electricPlane k R Q u p
  else if j=1 then (Complex.I*(WithLp.ofLp p.2 1:ℂ)) • electricPlane k R Q u p
  else phase (WithLp.ofLp p.2) p.1.1 p.1.2.1 • electric k (WithLp.ofLp p.2) (derivativeState k R Q u p)
def magneticPartial (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ) (j:Fin 3) (p:Parameter) : Vec3 :=
  if j=0 then (Complex.I*(WithLp.ofLp p.2 0:ℂ)) • magneticPlane k R Q u p
  else if j=1 then (Complex.I*(WithLp.ofLp p.2 1:ℂ)) • magneticPlane k R Q u p
  else phase (WithLp.ofLp p.2) p.1.1 p.1.2.1 • magnetic k (WithLp.ofLp p.2) (derivativeState k R Q u p)

def line (j:Fin 3) (p:Spatial) (x:ℝ) : Spatial :=
  if j=0 then (x,p.2.1,p.2.2) else if j=1 then (p.1,x,p.2.2) else (p.1,p.2.1,x)
def coordinate (p:Spatial) (j:Fin 3) : ℝ := ![p.1,p.2.1,p.2.2] j

theorem matrixVector_continuousOn {Y:Type*} [TopologicalSpace Y] (B:Set Y)
    (M:Y→Mat4) (u:Y→Channel→ℂ) (hM:ContinuousOn M B) (hu:ContinuousOn u B) :
    ContinuousOn (fun p=>M p*ᵥu p) B := by
  intro p hp
  apply continuousWithinAt_pi.mpr;intro i
  exact tendsto_finsetSum Finset.univ (fun j _=>
    (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp (hM p hp) i) j).mul
      (continuousWithinAt_pi.mp (hu p hp) j))

theorem generator_continuous (k:ℝ) (R Q:ObliqueVacuum.RMat) :
    Continuous (fun p:Parameter=>generator k (WithLp.ofLp p.2) R Q) := by
  have h := ObliqueMaxwell.generator_continuous k (fun _=>R) (fun _=>Q) continuous_const continuous_const
  have hp : Continuous (fun p:Parameter=>(WithLp.ofLp p.2,(0:ℝ))) :=
    ((PiLp.continuous_ofLp 2 (fun _:Fin 2=>ℝ)).comp continuous_snd).prodMk continuous_const
  convert h.comp hp using 1
  rfl

theorem state_continuousOn (k r:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ)
    (hu:ContinuousOn u (disk r)) :
    ContinuousOn (fiberState k R Q u) (univ ×ˢ disk r) ∧
      ContinuousOn (derivativeState k R Q u) (univ ×ˢ disk r) := by
  have hM : Continuous (fun p:Parameter=>transfer k (WithLp.ofLp p.2) R Q p.1.2.2) := by
    exact NormedSpace.exp_continuous.comp
      (((continuous_snd.comp continuous_snd).comp continuous_fst).smul (generator_continuous k R Q))
  have hU : ContinuousOn (fun p:Parameter=>u p.2) (univ ×ˢ disk r) :=
    hu.comp continuous_snd.continuousOn (fun p hp=>hp.2)
  have hS := matrixVector_continuousOn (univ ×ˢ disk r) _ _ hM.continuousOn hU
  exact ⟨hS,matrixVector_continuousOn (univ ×ˢ disk r) _ _ (generator_continuous k R Q).continuousOn hS⟩

theorem electric_continuous (k:ℝ) :
    Continuous (fun p:Transverse×(Channel→ℂ)=>electric k (WithLp.ofLp p.1) p.2) := by
  apply continuous_pi;intro i;fin_cases i <;> simp only [electric]
  all_goals fun_prop
theorem magnetic_continuous (k:ℝ) :
    Continuous (fun p:Transverse×(Channel→ℂ)=>magnetic k (WithLp.ofLp p.1) p.2) := by
  apply continuous_pi;intro i;fin_cases i <;> simp only [magnetic]
  all_goals fun_prop
theorem phase_continuous : Continuous (fun p:Parameter=>phase (WithLp.ofLp p.2) p.1.1 p.1.2.1) := by
  unfold phase OQ7Prescribed.apertureOscillation
  fun_prop

theorem plane_continuousOn (k r:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ)
    (hu:ContinuousOn u (disk r)) :
    ContinuousOn (electricPlane k R Q u) (univ ×ˢ disk r) ∧
      ContinuousOn (magneticPlane k R Q u) (univ ×ˢ disk r) := by
  have hs := (state_continuousOn k r R Q u hu).1
  have he := (electric_continuous k).comp_continuousOn (continuous_snd.continuousOn.prodMk hs)
  have hm := (magnetic_continuous k).comp_continuousOn (continuous_snd.continuousOn.prodMk hs)
  exact ⟨phase_continuous.continuousOn.smul he,phase_continuous.continuousOn.smul hm⟩

theorem partial_continuousOn (k r:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ)
    (hu:ContinuousOn u (disk r)) (j:Fin 3) :
    ContinuousOn (electricPartial k R Q u j) (univ ×ˢ disk r) ∧
      ContinuousOn (magneticPartial k R Q u j) (univ ×ˢ disk r) := by
  have hs := (state_continuousOn k r R Q u hu).2
  have hp := plane_continuousOn k r R Q u hu
  have he := (electric_continuous k).comp_continuousOn (continuous_snd.continuousOn.prodMk hs)
  have hm := (magnetic_continuous k).comp_continuousOn (continuous_snd.continuousOn.prodMk hs)
  have hκ (i:Fin 2) : Continuous (fun p:Parameter=>Complex.I*(WithLp.ofLp p.2 i:ℂ)) := by fun_prop
  fin_cases j
  · exact ⟨(hκ 0).continuousOn.smul hp.1,(hκ 0).continuousOn.smul hp.2⟩
  · exact ⟨(hκ 1).continuousOn.smul hp.1,(hκ 1).continuousOn.smul hp.2⟩
  · exact ⟨phase_continuous.continuousOn.smul he,phase_continuous.continuousOn.smul hm⟩

theorem line_continuous (j:Fin 3) (p:Spatial) : Continuous (line j p) := by
  fin_cases j
  · change Continuous (fun x:ℝ=>(x,p.2.1,p.2.2)); fun_prop
  · change Continuous (fun x:ℝ=>(p.1,x,p.2.2)); fun_prop
  · change Continuous (fun x:ℝ=>(p.1,p.2.1,x)); fun_prop

theorem plane_partial (k:ℝ) (R Q:ObliqueVacuum.RMat) (u:Transverse→Channel→ℂ)
    (q:Transverse) (p:Spatial) (j i:Fin 3) (x:ℝ) :
    HasDerivAt (fun s=>electricPlane k R Q u (line j p s,q) i)
      (electricPartial k R Q u j (line j p x,q) i) x ∧
      HasDerivAt (fun s=>magneticPlane k R Q u (line j p s,q) i)
        (magneticPartial k R Q u j (line j p x,q) i) x := by
  let κ := WithLp.ofLp q
  let F := state k κ R Q (u q) p.2.2
  fin_cases j
  · change HasDerivAt (fun s=>phase κ s p.2.1*electric k κ F i)
        (Complex.I*(κ 0:ℂ)*(phase κ x p.2.1*electric k κ F i)) x ∧
      HasDerivAt (fun s=>phase κ s p.2.1*magnetic k κ F i)
        (Complex.I*(κ 0:ℂ)*(phase κ x p.2.1*magnetic k κ F i)) x
    have hp := (OQ7Prescribed.apertureOscillation_hasDerivAt (κ 0) x).mul_const
      (OQ7Prescribed.apertureOscillation (κ 1) p.2.1)
    constructor
    · convert hp.mul_const (electric k κ F i) using 1 <;> first |rfl | (unfold phase;ring)
    · convert hp.mul_const (magnetic k κ F i) using 1 <;> first |rfl | (unfold phase;ring)
  · change HasDerivAt (fun s=>phase κ p.1 s*electric k κ F i)
        (Complex.I*(κ 1:ℂ)*(phase κ p.1 x*electric k κ F i)) x ∧
      HasDerivAt (fun s=>phase κ p.1 s*magnetic k κ F i)
        (Complex.I*(κ 1:ℂ)*(phase κ p.1 x*magnetic k κ F i)) x
    have hp := (OQ7Prescribed.apertureOscillation_hasDerivAt (κ 1) x).const_mul
      (OQ7Prescribed.apertureOscillation (κ 0) p.1)
    constructor
    · convert hp.mul_const (electric k κ F i) using 1 <;> first |rfl | (unfold phase;ring)
    · convert hp.mul_const (magnetic k κ F i) using 1 <;> first |rfl | (unfold phase;ring)
  · have hs := state_hasDerivAt k κ R Q (u q) x
    have he : HasDerivAt (fun z=>electric k κ (state k κ R Q (u q) z))
        (electric k κ (generator k κ R Q*ᵥstate k κ R Q (u q) x)) x := electric_hasDerivAt hs
    have hm : HasDerivAt (fun z=>magnetic k κ (state k κ R Q (u q) z))
        (magnetic k κ (generator k κ R Q*ᵥstate k κ R Q (u q) x)) x := magnetic_hasDerivAt hs
    constructor
    · exact (hasDerivAt_pi.mp he i).const_mul (phase κ p.1 p.2.1)
    · exact (hasDerivAt_pi.mp hm i).const_mul (phase κ p.1 p.2.1)

end GeneralizedResearch.SuperposedMaxwell
